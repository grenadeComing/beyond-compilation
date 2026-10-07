"""Grade each item with the unchanged GPT-5.2 judge, without (A) and with (B) the extracted Mathlib definitions.

    python beyond_v3_227/new_models/definitions_experiment/run_judge.py [--repeats 3] [--workers 8]

Condition A is judgement_GPT.validate_translation as used in the paper. Condition B sends the same system prompt
(read verbatim from judgement_GPT.py) and the same user message with one added block, the definitions from
defs.jsonl, placed after the Lean code. human74 items run under A and B; newer54 items run under B only (their
condition-A grades are the re-grading runs in review_rejected/regrade.jsonl). Calls are interleaved by repeat and
condition; answers are appended to grades.jsonl, so a rerun only makes the missing calls.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT))
import judgement_GPT as jg  # noqa: E402

SOURCE = (ROOT / "judgement_GPT.py").read_text(encoding="utf-8")
SYSTEM = re.search(r'"content": r"""(.*?)""".strip\(\)', SOURCE, re.S).group(1).strip()
assert SYSTEM.startswith("You are an expert in Lean 4") and "Output contract" in SYSTEM
OUT = HERE / "grades.jsonl"


def with_definitions(nl: str, lean: str, defs: str) -> dict:
    messages = [
        {"role": "system", "content": SYSTEM},
        {"role": "user", "content": (
            f"Natural language statement:\n{nl}\n\n"
            f"Lean4 code:\n{lean}\n\n"
            "Mathlib definitions used by the Lean code (extracted automatically from the Lean environment; for reference):\n"
            f"{defs}\n\n"
            "Compilation result: pass = True\n")},
    ]
    from openai import OpenAI
    try:
        r = OpenAI().responses.create(model="gpt-5.2", reasoning={"effort": "medium"}, input=messages)
        text = (r.output_text or "").strip()
        text = text[text.find("{"): text.rfind("}") + 1]
        obj = json.loads(text)
        return {"grade": int(obj.get("grade", -1)), "thought": obj.get("thought", "")}
    except Exception as e:  # recorded and retried on the next run
        return {"grade": -1, "thought": f"ERROR: {type(e).__name__}: {e}"}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repeats", type=int, default=3)
    ap.add_argument("--workers", type=int, default=8)
    args = ap.parse_args()
    items = [json.loads(l) for l in (HERE / "items.jsonl").read_text().splitlines()]
    defs = {json.loads(l)["key"]: json.loads(l)["material"] for l in (HERE / "defs.jsonl").read_text().splitlines()}
    jobs = []
    for rep in range(args.repeats):
        for it in items:
            for cond in (("A", "B") if it["set"] == "human74" else ("B",)):
                jobs.append((it, cond, rep))
    done = set()
    if OUT.exists():
        for l in OUT.read_text().splitlines():
            r = json.loads(l)
            if r["grade"] >= 0:
                done.add((r["key"], r["condition"], r["repeat"]))
    todo = [j for j in jobs if (j[0]["key"], j[1], j[2]) not in done]
    print(f"{len(jobs)} calls planned, {len(todo)} to run", flush=True)
    lock = threading.Lock()

    def run(job) -> None:
        it, cond, rep = job
        if cond == "A":
            res = jg.validate_translation(it["nl"].strip(), it["lean"].strip(), True, model="gpt-5.2")
        else:
            res = with_definitions(it["nl"].strip(), it["lean"].strip(), defs[it["key"]])
        rec = {"key": it["key"], "set": it["set"], "condition": cond, "repeat": rep,
               "grade": res.get("grade", -1), "thought": str(res.get("thought", ""))[:1500]}
        with lock, OUT.open("a", encoding="utf-8") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")

    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        list(ex.map(run, todo))
    print("done", flush=True)


if __name__ == "__main__":
    main()
