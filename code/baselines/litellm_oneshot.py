#!/usr/bin/env python3
# litellm_oneshot.py
#
# One-shot Lean4 translation using LiteLLM (supports OpenAI/Anthropic/Gemini),
# then compile-check via Lean REPL tool.
#
# Usage:
#   python litellm_oneshot.py --model anthropic/claude-sonnet-4-6 --max-workers 3
#   python litellm_oneshot.py --model gemini/gemini-2.5-pro --max-workers 3
#   python litellm_oneshot.py --model gpt-5.2 --max-workers 6
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

import litellm
litellm.suppress_debug_info = True
from tqdm import tqdm

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

try:
    from agents.tools.run_lean_tool import LeanReplTool
    from agents.tools.base_tool import BaseTool
except Exception as e:
    LeanReplTool = None
    BaseTool = None
    _IMPORT_ERR = e
else:
    _IMPORT_ERR = None

logging.getLogger("LiteLLM").setLevel(logging.WARNING)
logging.getLogger("litellm").setLevel(logging.WARNING)

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
                ro_obj = json.loads(ro)
                return extract_repl_pass(ro_obj)
            except Exception:
                pass
        return None
    if isinstance(x, str):
        try:
            obj = json.loads(x)
            return extract_repl_pass(obj)
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


def translate(nl_statement: str, model: str) -> str:
    resp = litellm.completion(
        model=model,
        messages=[
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": nl_statement},
        ],
    )
    content = resp.choices[0].message.content or ""
    return strip_lean_fences(content.strip())


def first_error_snip(repl_output: Any, limit: int = 400) -> str:
    if repl_output is None:
        return ""
    s = str(repl_output).replace("\n", " ").strip()
    return s[:limit]


def process_one(idx: int, entry: Dict[str, Any], lean_output_dir: Path, model: str, repl_tool: Any) -> Dict[str, Any]:
    name = safe_name(entry.get("name", ""))
    nl = entry.get("nl_statement", "") or ""
    domain = entry.get("domain", "")
    out_path = lean_output_dir / f"{output_stem(idx, name)}.lean"

    try:
        lean_code = translate(nl, model=model)
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
        logging.error(f"Error processing {name}: {type(e).__name__}: {e}")
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


def model_to_dirname(model: str) -> str:
    """Convert model name to a clean directory name."""
    return model.replace("/", "_").replace(".", "_").replace("-", "_")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="One-shot Lean translation (LiteLLM) + REPL compile check.")
    p.add_argument("--model", required=True, help="LiteLLM model name (e.g. anthropic/claude-sonnet-4-6).")
    p.add_argument("--input", default=None, help="Path to input JSONL.")
    p.add_argument("--max-workers", type=int, default=3, help="Thread workers (default: 3).")
    return p.parse_args()


def main() -> None:
    args = parse_args()

    if LeanReplTool is None or BaseTool is None:
        raise SystemExit(f"REPL tool import failed: {_IMPORT_ERR}")

    results_root = PROJECT_ROOT / "results"
    dir_name = f"oneshot_{model_to_dirname(args.model)}_results"
    config_results_dir = results_root / dir_name
    lean_output_dir = config_results_dir / "lean_output"
    config_results_dir.mkdir(parents=True, exist_ok=True)
    lean_output_dir.mkdir(parents=True, exist_ok=True)

    BaseTool.allowed_root = str(lean_output_dir)

    setup_logging(config_results_dir / "translation.log")

    input_file = Path(args.input) if args.input else (PROJECT_ROOT.parent / "benchmark/benchmark.jsonl")
    if not input_file.exists():
        raise SystemExit(f"Input JSONL not found at: {input_file}")

    entries = load_entries(input_file)
    logging.info(f"Loaded {len(entries)} entries from {input_file}")
    logging.info(f"Model: {args.model}, Workers: {args.max_workers}")

    repl_tool = LeanReplTool()

    csv_path = config_results_dir / "agent_run_summary.csv"
    fieldnames = [
        "row_index", "name", "domain", "status", "steps", "compile_status",
        "io_error", "nl_statement", "lean4_code", "repl_output"
    ]

    t0 = time.perf_counter()

    rows: List[Tuple[int, Dict[str, Any]]] = []
    with ThreadPoolExecutor(max_workers=args.max_workers) as ex:
        futures = {ex.submit(process_one, i, entry, lean_output_dir, args.model, repl_tool): i
                   for i, entry in enumerate(entries)}
        with tqdm(total=len(entries), desc="Processing entries") as pbar:
            for fut in as_completed(futures):
                rows.append((futures[fut], fut.result()))
                pbar.update(1)

    rows.sort(key=lambda x: x[0])

    with csv_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for _, row in rows:
            w.writerow(row)

    t1 = time.perf_counter()
    print(f"\nDone. Wrote CSV: {csv_path}")
    print(f"Lean outputs: {lean_output_dir}")
    print(f"Time: {t1 - t0:.2f}s")


if __name__ == "__main__":
    main()
