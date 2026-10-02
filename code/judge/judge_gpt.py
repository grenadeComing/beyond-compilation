import argparse
import csv
import json
import re
import shutil
import time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait
from typing import Any, Dict, Iterable, Optional, Tuple

# === CSV columns in YOUR file (match screenshot exactly) ===
COL_NAME = "name"
COL_NL = "nl_statement"
COL_LEAN = "lean4_code"
COL_COMPILE = "compile_status"   # NOTE: has a space

# Output columns we add to the CSV (if missing)
RESULT_COLUMNS = ("validate_score", "validate_reason", "equivalent")

def validate_translation(
    nl_statement: str,
    lean4_code: str,
    compile_pass: bool,
    model: str = "gpt-5.2",
) -> Dict[str, Any]:
    messages = [
        {
            "role": "system",
            "content": r"""
You are an expert in Lean 4, Mathlib, and mathematics. You are judging TRANSLATION-ONLY.

Input: (1) a natural-language statement, (2) a Lean 4 code snippet, (3) compile_pass boolean.
Your job: decide whether the Lean code, AS A STATEMENT, matches the meaning of the natural-language statement.

Key policy (NOT PICKY):
- If compile_pass = False: the translation is NOT faithful. grade must be 0..3. faithful=false.
- If compile_pass = True: ignore the proof/body entirely (including `by sorry`). Proof completeness is NOT part of the evaluation.
- A translation is faithful if the Lean statement expresses the same mathematical claim as the NL statement.

Auxiliary definitions policy (lenient but not allowing cheating):
- Auxiliary defs/lemmas are allowed if they are reasonable encodings/abbreviations and do not change the meaning.
- However, if the code introduces a clearly vacuous placeholder for a nontrivial concept (e.g. `def X := True`, `:= none`, `:= 0` for something meant to be meaningful), and that placeholder is essential to making the final theorem appear to match, then the translation is NOT faithful.

How to judge meaning (focus):
- Compare the MAIN theorem/definition statement(s) to the NL statement.
- Check quantifiers (∀/∃), logical structure (→/↔/∧/∨), and key hypotheses.
- Check main objects/domains: ℕ/ℤ/ℝ, rings/groups, ZMod n, matrices, etc.
- Small implementation details are OK if the meaning is preserved.

Scoring guide (integer 0..10):
- 0: unrelated.
- 1-3: compile_pass is False OR statement is clearly wrong.
- 4-6: compiles, but meaning is materially different / missing key hypotheses / wrong domain; might be “in the ballpark”.
- 7-8: compiles, mostly matches, but has a noticeable mismatch (e.g. strengthened/weakened in an important way).
- 9: compiles, very close; only tiny mismatch.
- 10: compiles and meaning matches.

Output contract (STRICT):
Return a single JSON object with exactly these fields:
{
  "faithful": true or false,
  "grade": 0..10,
  "thought": "### BEGIN THOUGHT\n<short explanation focusing on statement-level comparison>\n### END THOUGHT"
}
Return ONLY valid JSON. No extra keys. No markdown outside JSON.

""".strip(),
        },
        {
            "role": "user",
            "content": (
                f"Natural language statement:\n{nl_statement}\n\n"
                f"Lean4 code:\n{lean4_code}\n\n"
                f"Compilation result: pass = {compile_pass}\n"
            ),
        },
    ]

    try:
        if model.startswith(("anthropic/", "claude-")):
            from anthropic import Anthropic

            anthropic_model = model.removeprefix("anthropic/")
            response = Anthropic().messages.create(
                model=anthropic_model,
                max_tokens=4096,
                system=messages[0]["content"],
                messages=[messages[1]],
            )
            text = "\n".join(
                block.text for block in response.content if getattr(block, "type", "") == "text"
            ).strip()
        else:
            from openai import OpenAI

            response = OpenAI().responses.create(
                model=model,
                reasoning={"effort": "medium"},
                input=messages,
            )
            text = (response.output_text or "").strip()

        # best-effort: extract first {...} block if the model wrapped it
        if not text.startswith("{"):
            l = text.find("{")
            r = text.rfind("}")
            if l != -1 and r != -1 and r > l:
                text = text[l : r + 1]

        obj = json.loads(text)

        # basic sanity + enforce compile-fail cap
        faithful = bool(obj.get("faithful", False))
        grade = int(obj.get("grade", -1))
        thought = obj.get("thought", "")

        if not compile_pass:
            faithful = False
            if grade >= 0:
                grade = min(grade, 3)

        return {"faithful": faithful, "grade": grade, "thought": thought}

    except json.JSONDecodeError:
        recovered = _recover_from_invalid_json(text, compile_pass)
        if recovered is not None:
            return recovered
        return {
            "faithful": False,
            "grade": -1,
            "thought": "### BEGIN THOUGHT\nERROR: Invalid JSON from model\n### END THOUGHT",
        }
    except Exception as e:
        return {
            "faithful": False,
            "grade": -1,
            "thought": f"### BEGIN THOUGHT\nERROR: {type(e).__name__}: {e}\n### END THOUGHT",
        }


def _recover_from_invalid_json(
    raw: str, compile_pass: bool
) -> Optional[Dict[str, Any]]:
    """Recover the required fields from near-JSON without another API call."""
    if not raw:
        return None

    faithful = None
    grade = None

    match = re.search(r'\bfaithful\b[^a-zA-Z0-9]*\b(true|false)\b', raw, re.IGNORECASE)
    if match:
        faithful = match.group(1).lower() == "true"

    match = re.search(r'\bgrade\b[^0-9-]*(-?\d+)', raw, re.IGNORECASE)
    if match:
        grade = int(match.group(1))

    if grade is None and faithful is None:
        return None
    if grade is None:
        grade = 10 if faithful else 0
    if faithful is None:
        faithful = grade >= 9

    if not compile_pass:
        faithful = False
        grade = min(grade, 3)

    thought = raw.strip()
    if "### BEGIN THOUGHT" not in thought:
        thought = f"### BEGIN THOUGHT\n{thought}\n### END THOUGHT"
    return {"faithful": faithful, "grade": grade, "thought": thought}


def _to_bool_compile(v: Any) -> bool:
    """Robustly interpret compile status from CSV (0/1, True/False, etc)."""
    if v is None:
        return False
    if isinstance(v, bool):
        return v
    s = str(v).strip().lower()
    if s in ("1", "true", "yes", "y"):
        return True
    if s in ("0", "false", "no", "n", ""):
        return False
    try:
        return bool(int(s))
    except Exception:
        return False


def _augment_row(row: Dict[str, Any], judge: Dict[str, Any]) -> Tuple[Dict[str, Any], bool]:
    updated = row.copy()

    compile_pass = _to_bool_compile(row.get(COL_COMPILE, 0))
    raw_grade = int(judge.get("grade", -1))

    # Your rule: if it doesn't compile, cap at 3
    final_grade = min(raw_grade, 3) if not compile_pass else raw_grade
    equivalent = bool(compile_pass and final_grade >= 9)

    updated["validate_score"] = final_grade
    updated["validate_reason"] = judge.get("thought", "")
    updated["equivalent"] = 1 if equivalent else 0

    return updated, final_grade >= 0


def _ensure_fieldnames(existing: Iterable[str]) -> Tuple[str, ...]:
    fieldnames = list(existing)
    for col in RESULT_COLUMNS:
        if col not in fieldnames:
            fieldnames.append(col)
    return tuple(fieldnames)


def _evaluate_single(
    args: Tuple[int, Dict[str, Any], str, bool, bool]
) -> Tuple[int, str, Dict[str, Any], bool]:
    idx, row, model, should_call, preserve_uncalled = args
    name = row.get(COL_NAME, f"row_{idx}")

    nl = (row.get(COL_NL, "") or "").strip()
    lean = (row.get(COL_LEAN, "") or "").strip()
    compile_pass = _to_bool_compile(row.get(COL_COMPILE, 0))

    if not should_call:
        if preserve_uncalled:
            return idx, name, row.copy(), True
        updated = row.copy()
        updated["validate_score"] = 0 if not compile_pass else -1
        updated["validate_reason"] = (
            "SKIPPED: compile_status is false; semantic judge not called."
            if not compile_pass
            else "SKIPPED: max API call limit reached."
        )
        updated["equivalent"] = 0
        return idx, name, updated, not compile_pass

    try:
        judge = validate_translation(nl, lean, compile_pass, model=model)
        updated_row, success = _augment_row(row, judge)
        return idx, name, updated_row, success
    except Exception as e:
        updated = row.copy()
        updated["validate_score"] = -1
        updated["validate_reason"] = f"ERROR: {type(e).__name__}: {e}"
        updated["equivalent"] = 0
        return idx, name, updated, False


def evaluate_summary_csv(
    summary_path: Path,
    max_workers: int = 12,
    model: str = "gpt-5.2",
    skip_noncompile: bool = False,
    max_api_calls: Optional[int] = None,
    retry_errors: bool = False,
) -> None:
    with open(summary_path, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        rows = list(reader)

    total = len(rows)
    if total == 0:
        print("No rows to process!")
        return

    # Basic header sanity check (fail fast if export headers changed)
    required = {COL_NAME, COL_NL, COL_LEAN, COL_COMPILE}
    missing = required - set(rows[0].keys())
    if missing:
        raise SystemExit(f"Missing required columns in CSV: {sorted(missing)}")

    fieldnames = _ensure_fieldnames(rows[0].keys())

    if retry_errors:
        eligible_indices = [
            idx
            for idx, row in enumerate(rows)
            if _to_bool_compile(row.get(COL_COMPILE, 0))
            and str(row.get("validate_score", "")).strip() == "-1"
        ]
    else:
        eligible_indices = [
            idx
            for idx, row in enumerate(rows)
            if not (skip_noncompile and not _to_bool_compile(row.get(COL_COMPILE, 0)))
        ]
    if max_api_calls is not None:
        eligible_indices = eligible_indices[:max_api_calls]
    call_indices = set(eligible_indices)

    temp_path = summary_path.with_suffix(summary_path.suffix + ".tmp")
    print(f"Processing {total} rows from {summary_path} ...")
    print(f"Model: {model}; planned API calls: {len(call_indices)}")

    api_successes = 0
    api_failures = 0
    skipped_noncompile = 0
    skipped_by_limit = 0
    preserved_existing = 0
    next_to_write = 0
    result_buffer: Dict[int, Tuple[Dict[str, Any], bool, str]] = {}

    with open(temp_path, "w", newline="", encoding="utf-8") as tmp_file:
        writer = csv.DictWriter(tmp_file, fieldnames=fieldnames)
        writer.writeheader()

        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            pending = {}

            def handle_done(done_futures) -> None:
                nonlocal api_successes, api_failures, skipped_noncompile
                nonlocal skipped_by_limit, preserved_existing, next_to_write
                for future in done_futures:
                    idx, name, updated_row, success = future.result()
                    result_buffer[idx] = (updated_row, success, name)
                    pending.pop(future, None)

                while next_to_write in result_buffer:
                    row_data, success, name = result_buffer.pop(next_to_write)
                    reason = str(row_data.get("validate_reason", ""))
                    was_called = next_to_write in call_indices
                    if not was_called and retry_errors:
                        status = "–"
                        preserved_existing += 1
                    elif reason.startswith("SKIPPED: compile_status"):
                        status = "–"
                        skipped_noncompile += 1
                    elif reason.startswith("SKIPPED:"):
                        status = "–"
                        skipped_by_limit += 1
                    elif success:
                        status = "✓"
                        api_successes += 1
                    else:
                        status = "✗"
                        api_failures += 1
                    print(f"{status} [{next_to_write + 1}/{total}] {name}")
                    writer.writerow(row_data)
                    next_to_write += 1

            for idx, row in enumerate(rows):
                fut = executor.submit(
                    _evaluate_single,
                    (idx, row, model, idx in call_indices, retry_errors),
                )
                pending[fut] = idx

                if len(pending) >= max_workers:
                    done, _ = wait(list(pending.keys()), return_when=FIRST_COMPLETED)
                    handle_done(done)

            while pending:
                done, _ = wait(list(pending.keys()), return_when=FIRST_COMPLETED)
                handle_done(done)

    backup_path = summary_path.with_suffix(summary_path.suffix + ".bak")
    shutil.copy(summary_path, backup_path)
    temp_path.replace(summary_path)

    print(
        "✅ Completed evaluation. "
        f"API: {api_successes} succeeded, {api_failures} failed; "
        f"locally skipped: {skipped_noncompile} non-compiling, "
        f"{skipped_by_limit} by call limit; "
        f"preserved: {preserved_existing} existing rows."
    )


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Validate Lean translations recorded in a summary CSV.")
    p.add_argument("csv_path", help="Path to the exported CSV (from your XLSX).")
    p.add_argument("--max-workers", type=int, default=12)
    p.add_argument("--model", default="gpt-5.2")
    p.add_argument(
        "--skip-noncompile",
        action="store_true",
        help="Do not call the semantic judge for rows that failed compilation.",
    )
    p.add_argument(
        "--max-api-calls",
        type=int,
        default=None,
        help="Cap model calls for smoke testing; remaining eligible rows receive score -1.",
    )
    p.add_argument(
        "--retry-errors",
        action="store_true",
        help="Only re-evaluate compiling rows whose existing validate_score is -1.",
    )
    return p.parse_args()


if __name__ == "__main__":
    start = time.time()
    args = parse_args()

    summary_path = Path(args.csv_path)
    if not summary_path.exists():
        raise SystemExit(f"CSV not found at {summary_path}")

    evaluate_summary_csv(
        summary_path,
        max_workers=args.max_workers,
        model=args.model,
        skip_noncompile=args.skip_noncompile,
        max_api_calls=args.max_api_calls,
        retry_errors=args.retry_errors,
    )
    print(f"Execution time: {time.time() - start:.2f}s")
