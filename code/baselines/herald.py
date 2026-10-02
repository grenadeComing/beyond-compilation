#!/usr/bin/env python3
# oneshot_translation_herald.py
#
# One-shot Lean4 translation using Herald (OpenAI-compatible /v1/chat/completions),
# then compile-check via Lean REPL tool.
#
# Usage:
#   python oneshot_translation_herald.py \
#     --api-url http://localhost:8000/v1/chat/completions \
#     --model FrenzyMath/Herald_translator \
#     --max-workers 6
#
# Output:
#   results/oneshot_herald_results/lean_output/<row>_<name>.lean
#   results/oneshot_herald_results/agent_run_summary.csv
#
import sys
import argparse
import csv
import json
import logging
import time
import re
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Any, Dict, List, Tuple, Optional

import requests
from tqdm import tqdm

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

# Import tools
try:
    from agents.tools.run_lean_tool import LeanReplTool
    from agents.tools.base_tool import BaseTool
except Exception as e:
    LeanReplTool = None
    BaseTool = None
    _IMPORT_ERR = e
else:
    _IMPORT_ERR = None


SYSTEM_PROMPT = r"""
You are an expert Lean4 translation agent.

Task: Translate the given natural-language mathematical statement into Lean4 (Mathlib) as a theorem/definition statement ONLY (NOT a proof).

Hard requirements:
- Output ONLY Lean code (no markdown fences, no explanations, no surrounding commentary).
- The first line MUST be exactly: `import Mathlib`
- Do NOT output any other `import ...` lines anywhere.
- Do NOT use `open` or `open scoped` at the top level.
- The final theorem/definition MUST end with `:= by sorry`
- The statement should be well-typed and semantically faithful to the natural-language statement.

Return only the Lean file content.
"""


def setup_logging(log_path: Path) -> None:
    log_path.parent.mkdir(parents=True, exist_ok=True)
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(levelname)s - %(message)s",
        handlers=[logging.FileHandler(log_path, mode="a", encoding="utf-8"), logging.StreamHandler()],
        force=True,
    )


def safe_name(raw: str) -> str:
    return (raw or "unnamed").replace("|", "_").replace("/", "_").replace("\\", "_").strip()


def output_stem(idx: int, name: str) -> str:
    return safe_name(f"{idx + 1:04d}_{name}")


def extract_repl_pass(x: Any) -> Optional[int]:
    if isinstance(x, dict):
        rp = x.get("repl_pass", None)
        if isinstance(rp, bool):
            return 1 if rp else 0
        if isinstance(rp, int):
            return 1 if rp == 1 else 0
        if isinstance(rp, str) and rp.strip().isdigit():
            return 1 if int(rp.strip()) == 1 else 0

        ro = x.get("repl_output", None)
        if isinstance(ro, str):
            try:
                return extract_repl_pass(json.loads(ro))
            except Exception:
                pass
        return None

    if isinstance(x, str):
        try:
            return extract_repl_pass(json.loads(x))
        except Exception:
            if '"repl_pass": 1' in x or "'repl_pass': 1" in x:
                return 1
            if '"repl_pass": 0' in x or "'repl_pass': 0" in x:
                return 0
            return None

    return None


def strip_lean_fences(text: str) -> str:
    if not text:
        return ""
    s = text.strip()
    m = re.search(r"```(?:lean|Lean|LEAN)?\s*\n([\s\S]*?)\n```", s)
    if m:
        return m.group(1).strip()
    if s.startswith("```"):
        s = re.sub(r"^```[^\n]*\n?", "", s)
        s = re.sub(r"\n?```$", "", s)
        return s.strip()
    return s


def load_entries(input_file: Path) -> List[Dict[str, Any]]:
    with input_file.open("r", encoding="utf-8") as f:
        return [json.loads(line) for line in f]


def first_error_snip(repl_output: Any, limit: int = 400) -> str:
    if repl_output is None:
        return ""
    return str(repl_output).replace("\n", " ").strip()[:limit]


def herald_translate(nl: str, api_url: str, model: str, temperature: float, timeout: float) -> str:
    payload = {
        "model": model,
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": nl},
        ],
        "temperature": temperature,
    }

    resp = requests.post(api_url, json=payload, timeout=timeout)
    if resp.status_code != 200:
        raise RuntimeError(f"Herald API error {resp.status_code}: {resp.text}")

    data = resp.json()
    content = data["choices"][0]["message"]["content"]
    return strip_lean_fences((content or "").strip())


def process_one(idx, entry, lean_output_dir, api_url, model, temperature, timeout, repl_tool):
    name = safe_name(entry.get("name", ""))
    nl = entry.get("nl_statement", "") or ""
    domain = entry.get("domain", "")

    out_path = lean_output_dir / f"{output_stem(idx, name)}.lean"

    try:
        lean_code = herald_translate(nl, api_url, model, temperature, timeout)
        out_path.write_text(lean_code, encoding="utf-8")

        repl = repl_tool.run(path=str(out_path))
        rp = extract_repl_pass(repl)
        compile_status = 1 if rp == 1 else 0
        status = "success" if compile_status == 1 else "compile_failed"

        return {
            "row_index": idx + 1,
            "name": name,
            "domain": domain,
            "status": status,
            "steps": 1,
            "compile_status": compile_status,
            "io_error": "",
            "nl_statement": nl,
            "lean4_code": lean_code,
            "repl_output": first_error_snip(repl.get("repl_output") if isinstance(repl, dict) else repl),
        }

    except Exception as e:
        logging.error(f"{name}: {type(e).__name__}: {e}")
        return {
            "row_index": idx + 1,
            "name": name,
            "domain": domain,
            "status": "oneshot_crashed",
            "steps": 0,
            "compile_status": 0,
            "io_error": f"{type(e).__name__}: {e}",
            "nl_statement": nl,
            "lean4_code": "",
            "repl_output": "",
        }


def parse_args():
    p = argparse.ArgumentParser(description="One-shot Lean translation (Herald) + REPL check.")
    p.add_argument("--api-url", default="http://localhost:8000/v1/chat/completions")
    p.add_argument("--model", default="FrenzyMath/Herald_translator")
    p.add_argument("--input", default=None)
    p.add_argument("--max-workers", type=int, default=6)
    p.add_argument("--temperature", type=float, default=0.2)
    p.add_argument("--timeout", type=float, default=60.0)
    return p.parse_args()


def main():
    args = parse_args()

    if LeanReplTool is None or BaseTool is None:
        raise SystemExit(f"REPL tool import failed: {_IMPORT_ERR}")

    results_root = PROJECT_ROOT / "results" / "oneshot_herald_results"
    lean_output_dir = results_root / "lean_output"
    lean_output_dir.mkdir(parents=True, exist_ok=True)

    BaseTool.allowed_root = str(lean_output_dir)
    setup_logging(results_root / "translation.log")

    input_file = Path(args.input) if args.input else (PROJECT_ROOT.parent / "benchmark/benchmark.jsonl")
    entries = load_entries(input_file)

    repl_tool = LeanReplTool()

    csv_path = results_root / "agent_run_summary.csv"
    fieldnames = ["row_index", "name", "domain", "status", "steps", "compile_status",
                  "io_error", "nl_statement", "lean4_code", "repl_output"]

    t0 = time.perf_counter()

    rows = []
    with ThreadPoolExecutor(max_workers=args.max_workers) as ex:
        futures = {
            ex.submit(process_one, i, e, lean_output_dir, args.api_url, args.model, args.temperature, args.timeout, repl_tool): i
            for i, e in enumerate(entries)
        }
        with tqdm(total=len(entries)) as pbar:
            for fut in as_completed(futures):
                rows.append((futures[fut], fut.result()))
                pbar.update(1)

    rows.sort(key=lambda x: x[0])

    with csv_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for _, row in rows:
            w.writerow(row)

    print(f"Done. CSV: {csv_path}")
    print(f"Lean outputs: {lean_output_dir}")
    print(f"Time: {time.perf_counter() - t0:.2f}s")


if __name__ == "__main__":
    main()
