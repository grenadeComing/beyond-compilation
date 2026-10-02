#!/usr/bin/env python3
"""
One-shot Lean 4 statement formalization through an OpenAI-compatible vLLM server.

By default this uses the same simple request shape as herald.py:
system prompt + raw natural-language statement + temperature.

This runner is intended for external formalizer baselines such as:
  - stepfun-ai/StepFun-Formalizer-7B
  - AI-MO/Kimina-Autoformalizer-7B

It mirrors the existing one-shot baseline CSV format so the current judging
scripts can be reused directly:
  cp results/oneshot_baselines/stepfun_7b/agent_run_summary.csv \
     results/oneshot_baselines/stepfun_7b/agent_run_summary_gpt_judge.csv
  cp results/oneshot_baselines/stepfun_7b/agent_run_summary.csv \
     results/oneshot_baselines/stepfun_7b/agent_run_summary_gmn_judge.csv
  python judgement_GPT.py results/oneshot_baselines/stepfun_7b/agent_run_summary_gpt_judge.csv
  python judgement_GMN.py results/oneshot_baselines/stepfun_7b/agent_run_summary_gmn_judge.csv

Example:
  python oneshot_translation_generation/vllm_formalizer.py \
    --model stepfun-ai/StepFun-Formalizer-7B \
    --output-name stepfun_7b \
    --max-workers 4 \
    --resume
"""

from __future__ import annotations

import argparse
import csv
import json
import logging
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

import requests
from tqdm import tqdm

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

try:
    from agents.tools.base_tool import BaseTool
    from agents.tools.run_lean_tool import LeanReplTool
except Exception as e:  # pragma: no cover - fail fast in main
    BaseTool = None
    LeanReplTool = None
    _IMPORT_ERR = e
else:
    _IMPORT_ERR = None


STRICT_SYSTEM_PROMPT = r"""
You are an expert Lean 4 formalization model.

Task: Translate the given natural-language mathematical statement into Lean 4
Mathlib code as a theorem/definition statement ONLY. Do not prove it.

Hard requirements:
- Output ONLY Lean code.
- Do not include markdown fences or explanatory text.
- The first line must be: import Mathlib
- Use exactly the theorem name requested by the user when possible.
- The final theorem/definition must end with := by sorry
- The statement should be well-typed and semantically faithful.
""".strip()


HERALD_SYSTEM_PROMPT = r"""
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
""".strip()


MODEL_CARD_SYSTEM_PROMPT = "You are an expert in mathematics and Lean 4."


def setup_logging(log_path: Path) -> None:
    log_path.parent.mkdir(parents=True, exist_ok=True)
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(levelname)s - %(message)s",
        handlers=[
            logging.FileHandler(log_path, mode="a", encoding="utf-8"),
            logging.StreamHandler(),
        ],
        force=True,
    )


def safe_filename(raw: str) -> str:
    return (raw or "unnamed").replace("|", "_").replace("/", "_").replace("\\", "_").strip()


def lean_identifier(raw: str) -> str:
    ident = re.sub(r"[^0-9A-Za-z_]", "_", raw or "generated_theorem")
    ident = re.sub(r"_+", "_", ident).strip("_")
    if not ident:
        ident = "generated_theorem"
    if ident[0].isdigit():
        ident = f"thm_{ident}"
    return ident


def output_name_from_model(model: str) -> str:
    tail = model.rstrip("/").split("/")[-1]
    tail = tail.replace("StepFun-Formalizer-", "stepfun_")
    tail = tail.replace("Kimina-Autoformalizer-", "kimina_autoformalizer_")
    tail = tail.replace("-", "_").lower()
    return tail or "vllm_formalizer"


DECL_RE = re.compile(r"\b(theorem|lemma|def|example|axiom|instance)\b")
PROMPT_ECHO_MARKERS = (
    "Hard requirements:",
    "Output ONLY Lean code",
    "Return only the Lean file content",
    "Natural-language statement:",
    "Task: Translate",
    "You are an expert Lean",
)


def gpt2_byte_decoder() -> Dict[str, int]:
    bs = (
        list(range(ord("!"), ord("~") + 1))
        + list(range(ord("¡"), ord("¬") + 1))
        + list(range(ord("®"), ord("ÿ") + 1))
    )
    cs = bs[:]
    n = 0
    for b in range(256):
        if b not in bs:
            bs.append(b)
            cs.append(256 + n)
            n += 1
    return {chr(c): b for b, c in zip(bs, cs)}


BYTE_DECODER = gpt2_byte_decoder()


def repair_token_artifacts(text: str) -> str:
    """Repair common byte-level tokenizer artifacts seen in some vLLM outputs."""
    if not text:
        return ""
    buf = bytearray()
    for ch in text:
        b = BYTE_DECODER.get(ch)
        if b is not None:
            buf.append(b)
        else:
            buf.extend(ch.encode("utf-8"))
    return buf.decode("utf-8", errors="replace")


def remove_prompt_echo_comments(code: str) -> str:
    """Drop block comments that are clearly echoed task instructions, not Lean code."""
    if not code:
        return ""

    def repl(match: re.Match[str]) -> str:
        text = match.group(0)
        return "" if any(marker in text for marker in PROMPT_ECHO_MARKERS) else text

    return re.sub(r"/-[\s\S]*?-/", repl, code).strip()


def strip_comments_for_detection(code: str) -> str:
    """Remove comments for lightweight declaration/plausibility checks."""
    no_block = re.sub(r"/-[\s\S]*?-/", " ", code)
    return re.sub(r"--[^\n]*", " ", no_block)


def first_regex_outside_comments(code: str, pattern: re.Pattern[str]) -> Optional[re.Match[str]]:
    i = 0
    block_depth = 0
    line_comment = False
    in_string = False
    escape = False

    while i < len(code):
        ch = code[i]

        if line_comment:
            if ch == "\n":
                line_comment = False
            i += 1
            continue

        if block_depth:
            if code.startswith("/-", i):
                block_depth += 1
                i += 2
                continue
            if code.startswith("-/", i):
                block_depth -= 1
                i += 2
                continue
            i += 1
            continue

        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if code.startswith("--", i):
            line_comment = True
            i += 2
            continue
        if code.startswith("/-", i):
            block_depth = 1
            i += 2
            continue
        if ch == '"':
            in_string = True
            i += 1
            continue

        m = pattern.match(code, i)
        if m:
            return m
        i += 1

    return None


SORRY_RE = re.compile(r":=\s*by\s+sorry\b")
TERM_SORRY_RE = re.compile(r":=\s*sorry\b")
BY_PROOF_RE = re.compile(r":=\s*by\b")


def normalize_statement_body(code: str) -> str:
    """Normalize proof bodies to statement-only `:= by sorry`.

    This is deliberately model-agnostic: statement formalization evaluates the
    declaration before the proof, so generated proof terms/tactics are stripped
    for all models equally.
    """
    if not code:
        return ""

    term_sorry = first_regex_outside_comments(code, TERM_SORRY_RE)
    by_proof = first_regex_outside_comments(code, BY_PROOF_RE)

    if term_sorry and (by_proof is None or term_sorry.start() < by_proof.start()):
        return code[: term_sorry.start()] + ":= by sorry"

    if by_proof:
        return code[: by_proof.start()] + ":= by sorry"

    return code


def cut_after_first_sorry(code: str) -> str:
    m = first_regex_outside_comments(code, SORRY_RE)
    if not m:
        return code
    line_end = code.find("\n", m.end())
    return code[: line_end if line_end != -1 else m.end()]


def clean_code_candidate(text: str) -> str:
    s = text.strip()
    s = re.sub(r"^```[^\n]*\n?", "", s)
    s = re.sub(r"\n?```[\s\S]*$", "", s).strip()
    s = remove_prompt_echo_comments(s)

    import_match = first_regex_outside_comments(s, re.compile(r"import\s+Mathlib"))
    decl_match = first_regex_outside_comments(s, DECL_RE)
    if import_match:
        s = s[import_match.start() :]
    elif decl_match:
        s = "import Mathlib\n\n" + s[decl_match.start() :]

    s = remove_prompt_echo_comments(s)
    s = cut_after_first_sorry(s)
    s = normalize_statement_body(s)
    s = s.replace("```", "").strip()
    if s and "import Mathlib" not in s.splitlines()[:5]:
        s = "import Mathlib\n\n" + s
    return s.strip()


def candidate_score(code: str, theorem_name: Optional[str] = None) -> int:
    score = 0
    detect = strip_comments_for_detection(remove_prompt_echo_comments(code))
    if "import Mathlib" in code.splitlines()[:5]:
        score += 2
    if DECL_RE.search(detect):
        score += 5
    if SORRY_RE.search(detect):
        score += 5
    if theorem_name:
        if re.search(rf"\b(theorem|lemma|def|example)\s+{re.escape(theorem_name)}\b", detect):
            score += 20
        elif theorem_name in detect:
            score += 5
    if "Logical Structure" in code or "Mathematical Concepts" in code or code.count("##") >= 2:
        score -= 4
    return score


def is_plausible_lean_code(code: str) -> bool:
    if not code or not code.strip():
        return False
    detect = strip_comments_for_detection(remove_prompt_echo_comments(code))
    return "import Mathlib" in code.splitlines()[:5] and bool(DECL_RE.search(detect))


def invalid_placeholder(raw_path: Path) -> str:
    return (
        "import Mathlib\n\n"
        "/-\n"
        "No Lean theorem/definition was extracted from the model output.\n"
        f"See raw output: {raw_path.name}\n"
        "-/\n\n"
        "#check __NO_LEAN_CODE_EXTRACTED__\n"
    )


def strip_lean_fences(text: str, theorem_name: Optional[str] = None) -> str:
    if not text:
        return ""
    s = repair_token_artifacts(text).strip()

    # Remove closed reasoning wrappers while preserving any later Lean code.
    without_closed_think = re.sub(r"<think>[\s\S]*?</think>", "", s, flags=re.IGNORECASE).strip()

    candidates: List[Tuple[int, str]] = []
    order = 0
    for source in (without_closed_think, s):
        for fenced in re.finditer(r"```(?:lean4?|Lean4?|LEAN4?)?\s*\n([\s\S]*?)\n```", source):
            candidates.append((order, clean_code_candidate(fenced.group(1))))
            order += 1

        for m in re.finditer(r"import\s+Mathlib", source):
            candidates.append((order, clean_code_candidate(source[m.start() :])))
            order += 1

        for m in re.finditer(DECL_RE, source):
            candidates.append((order, clean_code_candidate(source[m.start() :])))
            order += 1

    candidates = [(i, c) for i, c in candidates if c]
    if not candidates:
        return ""

    _, best = max(candidates, key=lambda item: (candidate_score(item[1], theorem_name), item[0]))
    return best if is_plausible_lean_code(best) else ""


def normalize_lean_code(text: str, theorem_name: Optional[str] = None) -> str:
    code = strip_lean_fences(text, theorem_name=theorem_name)
    if not code:
        return ""
    if "import Mathlib" not in code.splitlines()[:5]:
        code = "import Mathlib\n\n" + code
    return code.strip() + "\n"


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


def first_error_snip(repl_output: Any, limit: int = 800) -> str:
    if repl_output is None:
        return ""
    return str(repl_output).replace("\n", " ").strip()[:limit]


def load_entries(input_file: Path) -> List[Dict[str, Any]]:
    with input_file.open("r", encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def row_key(idx: int, name: str) -> str:
    return f"{idx}:{name}"


def output_stem(idx: int, name: str) -> str:
    return safe_filename(f"{idx + 1:04d}_{name}")


def load_existing(csv_path: Path) -> Dict[str, Dict[str, Any]]:
    if not csv_path.exists():
        return {}
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        if "row_index" not in (reader.fieldnames or []):
            # Legacy outputs keyed by theorem name are unsafe for this dataset:
            # several rows intentionally share the same name but have different
            # natural-language statements.
            logging.warning("Ignoring legacy summary without row_index: %s", csv_path)
            return {}
        rows = list(reader)
    existing: Dict[str, Dict[str, Any]] = {}
    for fallback_idx, row in enumerate(rows):
        name = row.get("name", "")
        if not name:
            continue
        raw_idx = row.get("row_index", "")
        try:
            idx = int(str(raw_idx).strip()) - 1
        except Exception:
            idx = fallback_idx
        existing[row_key(idx, name)] = row
    return existing


def reusable_existing(row: Dict[str, Any]) -> bool:
    status = (row.get("status") or "").strip()
    code = row.get("lean4_code") or ""
    return bool(status and is_plausible_lean_code(code))


def build_messages(nl: str, theorem_name: str, prompt_style: str) -> List[Dict[str, str]]:
    if prompt_style == "herald":
        return [
            {"role": "system", "content": HERALD_SYSTEM_PROMPT},
            {"role": "user", "content": nl},
        ]

    if prompt_style == "strict":
        user_prompt = (
            f"Use theorem name: {theorem_name}\n\n"
            f"Natural-language statement:\n{nl}\n\n"
            "Return only a complete Lean file."
        )
        return [
            {"role": "system", "content": STRICT_SYSTEM_PROMPT},
            {"role": "user", "content": user_prompt},
        ]

    # Matches the public Kimina/StepFun model-card prompt style more closely.
    user_prompt = (
        "Please autoformalize the following problem in Lean 4 with a header. "
        f"Use the following theorem names: {theorem_name}.\n\n"
        f"{nl}\n\n"
        "Your code should start with:\n```Lean4\nimport Mathlib\n```\n"
        "End the final theorem or definition with `:= by sorry`."
    )
    return [
        {"role": "system", "content": MODEL_CARD_SYSTEM_PROMPT},
        {"role": "user", "content": user_prompt},
    ]


def call_vllm_chat(
    api_url: str,
    model: str,
    messages: List[Dict[str, str]],
    temperature: float,
    top_p: Optional[float],
    max_tokens: Optional[int],
    timeout: float,
    api_key: str,
    retries: int,
) -> str:
    headers = {}
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"

    payload = {
        "model": model,
        "messages": messages,
        "temperature": temperature,
    }
    if top_p is not None:
        payload["top_p"] = top_p
    if max_tokens is not None:
        payload["max_tokens"] = max_tokens

    last_err: Optional[Exception] = None
    for attempt in range(retries + 1):
        try:
            resp = requests.post(api_url, json=payload, headers=headers, timeout=timeout)
            if resp.status_code != 200:
                raise RuntimeError(f"vLLM API error {resp.status_code}: {resp.text[:1000]}")
            data = resp.json()
            return data["choices"][0]["message"]["content"] or ""
        except Exception as e:
            last_err = e
            if attempt < retries:
                time.sleep(min(10.0, 1.5 * (attempt + 1)))

    raise RuntimeError(str(last_err))


def process_one(
    idx: int,
    entry: Dict[str, Any],
    lean_output_dir: Path,
    raw_output_dir: Path,
    api_url: str,
    model: str,
    prompt_style: str,
    temperature: float,
    top_p: Optional[float],
    max_tokens: Optional[int],
    timeout: float,
    api_key: str,
    retries: int,
    prefer_existing_raw: bool,
    repl_tool: Any,
) -> Dict[str, Any]:
    name = safe_filename(entry.get("name", ""))
    theorem_name = lean_identifier(name)
    nl = entry.get("nl_statement", "") or ""
    domain = entry.get("domain", "")
    stem = output_stem(idx, name)

    lean_path = lean_output_dir / f"{stem}.lean"
    raw_path = raw_output_dir / f"{stem}.txt"

    try:
        if prefer_existing_raw and raw_path.exists():
            raw = raw_path.read_text(encoding="utf-8")
            source_status = "raw_recovered"
        else:
            messages = build_messages(nl, theorem_name, prompt_style)
            raw = call_vllm_chat(
                api_url=api_url,
                model=model,
                messages=messages,
                temperature=temperature,
                top_p=top_p,
                max_tokens=max_tokens,
                timeout=timeout,
                api_key=api_key,
                retries=retries,
            )
            source_status = ""
        lean_code = normalize_lean_code(raw, theorem_name=theorem_name)
        raw_path.write_text(raw, encoding="utf-8")

        if not is_plausible_lean_code(lean_code):
            lean_path.write_text(invalid_placeholder(raw_path), encoding="utf-8")
            return {
                "row_index": idx + 1,
                "name": name,
                "domain": domain,
                "status": "no_lean_code" if not source_status else f"{source_status}_no_lean_code",
                "steps": 1,
                "compile_status": 0,
                "io_error": "",
                "nl_statement": nl,
                "lean4_code": "",
                "repl_output": "No Lean theorem/definition extracted from model output.",
                "raw_model_output": raw[:4000],
            }

        lean_path.write_text(lean_code, encoding="utf-8")

        repl = repl_tool.run(path=str(lean_path))
        rp = extract_repl_pass(repl)
        compile_status = 1 if rp == 1 else 0
        status = "success" if compile_status == 1 else "compile_failed"
        if source_status:
            status = f"{source_status}_{status}"
        repl_output = repl.get("repl_output") if isinstance(repl, dict) else repl

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
            "repl_output": first_error_snip(repl_output),
            "raw_model_output": raw[:4000],
        }

    except Exception as e:
        logging.error("%s: %s: %s", name, type(e).__name__, e)
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
            "raw_model_output": "",
        }


def write_summary(csv_path: Path, rows: Iterable[Dict[str, Any]]) -> None:
    fieldnames = [
        "row_index",
        "name",
        "domain",
        "status",
        "steps",
        "compile_status",
        "io_error",
        "nl_statement",
        "lean4_code",
        "repl_output",
        "raw_model_output",
    ]
    tmp_path = csv_path.with_suffix(csv_path.suffix + ".tmp")
    with tmp_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)
    tmp_path.replace(csv_path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="One-shot vLLM formalizer baseline + Lean compile.")
    parser.add_argument("--api-url", default="http://localhost:8000/v1/chat/completions")
    parser.add_argument("--api-key", default="")
    parser.add_argument("--model", default="stepfun-ai/StepFun-Formalizer-7B")
    parser.add_argument("--output-name", default=None)
    parser.add_argument("--input", default=str(PROJECT_ROOT.parent / "benchmark/benchmark.jsonl"))
    parser.add_argument("--max-workers", type=int, default=6)
    parser.add_argument("--temperature", type=float, default=0.2)
    parser.add_argument("--top-p", type=float, default=None, help="Optional sampling top_p; omitted by default.")
    parser.add_argument("--max-tokens", type=int, default=None, help="Optional max_tokens; omitted by default.")
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--retries", type=int, default=2)
    parser.add_argument("--prompt-style", choices=("herald", "model-card", "strict"), default="herald")
    parser.add_argument("--resume", action="store_true", help="Reuse existing rows in output CSV.")
    parser.add_argument("--overwrite", action="store_true", help="Ignore existing rows even with --resume.")
    parser.add_argument(
        "--no-prefer-existing-raw",
        action="store_true",
        help="When rerunning, ignore existing raw_model_output/*.txt and call the model again.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    if LeanReplTool is None or BaseTool is None:
        raise SystemExit(f"REPL tool import failed: {_IMPORT_ERR}")

    output_name = args.output_name or output_name_from_model(args.model)
    results_root = PROJECT_ROOT / "results" / "oneshot_baselines" / output_name
    lean_output_dir = results_root / "lean_output"
    raw_output_dir = results_root / "raw_model_output"
    lean_output_dir.mkdir(parents=True, exist_ok=True)
    raw_output_dir.mkdir(parents=True, exist_ok=True)

    BaseTool.allowed_root = str(lean_output_dir)
    setup_logging(results_root / "translation.log")

    input_file = Path(args.input)
    entries = load_entries(input_file)
    csv_path = results_root / "agent_run_summary.csv"
    existing = load_existing(csv_path) if args.resume and not args.overwrite else {}

    rows_by_key: Dict[str, Dict[str, Any]] = {}
    pending: List[Tuple[int, Dict[str, Any]]] = []
    for idx, entry in enumerate(entries):
        name = safe_filename(entry.get("name", ""))
        key = row_key(idx, name)
        old = existing.get(key)
        if old and reusable_existing(old):
            rows_by_key[key] = old
        else:
            pending.append((idx, entry))

    logging.info("Model: %s", args.model)
    logging.info("API URL: %s", args.api_url)
    logging.info("Output: %s", results_root)
    logging.info("Loaded %d entries; %d pending; %d reused", len(entries), len(pending), len(rows_by_key))

    repl_tool = LeanReplTool()
    t0 = time.perf_counter()

    if pending:
        with ThreadPoolExecutor(max_workers=args.max_workers) as executor:
            futures = {
                executor.submit(
                    process_one,
                    idx,
                    entry,
                    lean_output_dir,
                    raw_output_dir,
                    args.api_url,
                    args.model,
                    args.prompt_style,
                    args.temperature,
                    args.top_p,
                    args.max_tokens,
                    args.timeout,
                    args.api_key,
                    args.retries,
                    (not args.no_prefer_existing_raw) and (not args.overwrite),
                    repl_tool,
                ): (idx, entry)
                for idx, entry in pending
            }

            with tqdm(total=len(futures)) as pbar:
                for future in as_completed(futures):
                    idx, entry = futures[future]
                    name = safe_filename(entry.get("name", ""))
                    key = row_key(idx, name)
                    rows_by_key[key] = future.result()
                    pbar.update(1)

                    # Checkpoint after each item so interruption can resume.
                    ordered = [
                        rows_by_key[row_key(i, safe_filename(e.get("name", "")))]
                        for i, e in enumerate(entries)
                        if row_key(i, safe_filename(e.get("name", ""))) in rows_by_key
                    ]
                    write_summary(csv_path, ordered)

    ordered_rows = [
        rows_by_key[row_key(i, safe_filename(e.get("name", "")))]
        for i, e in enumerate(entries)
        if row_key(i, safe_filename(e.get("name", ""))) in rows_by_key
    ]
    write_summary(csv_path, ordered_rows)

    compile_pass = sum(1 for row in ordered_rows if str(row.get("compile_status", "")).strip() == "1")
    print(f"Done. Rows: {len(ordered_rows)} / {len(entries)}")
    print(f"Compile pass: {compile_pass} / {len(ordered_rows)}")
    print(f"CSV: {csv_path}")
    print(f"Lean outputs: {lean_output_dir}")
    print(f"Raw outputs: {raw_output_dir}")
    print(f"Time: {time.perf_counter() - t0:.2f}s")


if __name__ == "__main__":
    main()
