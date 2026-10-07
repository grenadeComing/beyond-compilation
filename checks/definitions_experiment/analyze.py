"""Summarize the definitions experiment (fixed before looking at results).

    python beyond_v3_227/new_models/definitions_experiment/analyze.py

An output counts as accepted under a condition if at least 2 of its 3 grades are >= 9. human74: accepted counts
under A and B, separately for human-faithful (16) and human-unfaithful (58) outputs, with paired exact McNemar
tests. newer54: condition A from the first three re-grading calls (review_rejected/regrade.jsonl), condition B
from grades.jsonl, by the review's final category. Writes summary.json.
"""

from __future__ import annotations

import json
import math
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent


def mcnemar(b: int, c: int) -> float:
    n = b + c
    return 1.0 if n == 0 else min(1.0, 2 * sum(math.comb(n, i) for i in range(min(b, c) + 1)) / 2 ** n)


def main() -> None:
    items = {json.loads(l)["key"]: json.loads(l) for l in (HERE / "items.jsonl").read_text().splitlines()}
    g = defaultdict(list)
    for l in (HERE / "grades.jsonl").read_text().splitlines():
        r = json.loads(l)
        if r["grade"] >= 0:
            g[(r["key"], r["condition"])].append((r["repeat"], r["grade"]))
    for l in (HERE.parent / "review_rejected" / "regrade.jsonl").read_text().splitlines():
        r = json.loads(l)
        if r["group"] == "rejected" and r.get("grade", -1) >= 0 and r["repeat"] < 3:
            g[(r["key"], "A")].append((r["repeat"], r["grade"]))

    def acc(key, cond):
        gs = [x for _, x in sorted(g[(key, cond)])[:3]]
        return (sum(x >= 9 for x in gs) >= 2) if len(gs) == 3 else None, (sum(gs) / len(gs) if gs else None), len(gs)

    out = {}
    h = [k for k, it in items.items() if it["set"] == "human74"]
    for label, keys in (("human_faithful", [k for k in h if items[k]["human_faithful"]]),
                        ("human_unfaithful", [k for k in h if not items[k]["human_faithful"]])):
        rows = [(k, acc(k, "A"), acc(k, "B")) for k in keys]
        complete = [r for r in rows if r[1][0] is not None and r[2][0] is not None]
        a_acc = sum(r[1][0] for r in complete)
        b_acc = sum(r[2][0] for r in complete)
        only_b = [r[0] for r in complete if r[2][0] and not r[1][0]]
        only_a = [r[0] for r in complete if r[1][0] and not r[2][0]]
        out[label] = {"n": len(keys), "complete": len(complete), "accepted_A": a_acc, "accepted_B": b_acc,
                      "accepted_only_B": only_b, "accepted_only_A": only_a, "mcnemar_p": round(mcnemar(len(only_a), len(only_b)), 4),
                      "mean_grade_A": round(sum(r[1][1] for r in complete) / len(complete), 2) if complete else None,
                      "mean_grade_B": round(sum(r[2][1] for r in complete) / len(complete), 2) if complete else None}
    n_new = defaultdict(lambda: {"n": 0, "accepted_A": 0, "accepted_B": 0, "complete": 0})
    for k, it in items.items():
        if it["set"] != "newer54":
            continue
        cat = it["review_category"]
        a, b = acc(k, "A"), acc(k, "B")
        d = n_new[cat]
        d["n"] += 1
        if a[0] is not None and b[0] is not None:
            d["complete"] += 1
            d["accepted_A"] += a[0]
            d["accepted_B"] += b[0]
    out["newer54_by_review_category"] = dict(n_new)
    (HERE / "summary.json").write_text(json.dumps(out, indent=1))
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
