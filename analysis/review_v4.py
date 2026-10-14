"""Numbers for the validated review of rejected outputs (arXiv v4), from the released files.

    python analysis/review_v4.py        # writes analysis/review_v4.json

Inputs: checks/review_validation.jsonl (the two-stage review of the 69 compiling outputs that GPT-5.2
rejects and that humans labeled: the full agent in Batch A and Aristotle in Batch B),
checks/earlier_systems_review.jsonl (the same review of the seven earlier one-shot systems' rejections),
checks/newer_models_review.jsonl, checks/reviewer_validation.jsonl, human_audits/, outputs/.

A review label T is a translation error. The review's sensitivity bounds the number X of real errors among
a system's rejections whatever its false-flag rate: observed T = sens*X + fpr*(R - X) >= sens*X, so
X <= T / sens. For systems whose accepted outputs were not reviewed, T / compiling is a lower bound on the
unfaithful share e of compiling outputs.
"""

from __future__ import annotations

import csv
import json
import math
from collections import Counter
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
ONE_SHOT = {"GPT-5.2": "gpt-52", "Gemini-2.5-Pro": "gemini-25-pro", "Herald": "herald",
            "Kimina-Autoformalizer": "kimina_autof", "StepFun-Formalizer": "stepfun",
            "Kimina-Prover": "kimina_prover", "Goedel-Prover": "goedel_prover"}


def jsonl(path: Path) -> list[dict]:
    return [json.loads(l) for l in path.read_text(encoding="utf-8").splitlines() if l.strip()]


def wilson(k: int, n: int, z: float = 1.959963984540054) -> dict:
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return {"k": k, "n": n, "pct": round(100 * p, 1), "ci95": [round(100 * (c - h), 1), round(100 * (c + h), 1)]}


def kappa(pairs: list[tuple[int, int]]) -> dict:
    n = len(pairs)
    po = sum(a == b for a, b in pairs) / n
    pa, pb = sum(a for a, _ in pairs) / n, sum(b for _, b in pairs) / n
    pe = pa * pb + (1 - pa) * (1 - pb)
    return {"n": n, "agreement_pct": round(100 * po, 1), "kappa": round((po - pe) / (1 - pe), 2)}


def validation() -> dict:
    rev = jsonl(REPO / "checks" / "review_validation.jsonl")
    human = {}
    for f in ("batch_A_agent_rejected.csv", "batch_B_aristotle_random.csv"):
        for r in csv.DictReader((REPO / "human_audits" / f).open(encoding="utf-8")):
            human[r["case_id"]] = r
    err = lambda r: int(human[r["case_id"]]["human_majority_faithful"]) == 0  # noqa: E731
    final_t = lambda r: r["final_category"] == "T"  # noqa: E731
    either_t = lambda r: "T" in (r["first_review"]["category"], r["second_review"]["category"])  # noqa: E731
    errs, oks = [r for r in rev if err(r)], [r for r in rev if not err(r)]
    out = {"n": len(rev), "human_errors": len(errs), "human_faithful": len(oks),
           "final_T": {"finds_errors": wilson(sum(map(final_t, errs)), len(errs)),
                       "leaves_faithful": wilson(sum(not final_t(r) for r in oks), len(oks))},
           "either_stage_T": {"finds_errors": wilson(sum(map(either_t, errs)), len(errs)),
                              "leaves_faithful": wilson(sum(not either_t(r) for r in oks), len(oks))},
           "flagged_but_human_faithful": sorted(f"{r['case_id']} ({r['id']})" for r in oks if final_t(r)),
           "by_system": {}}
    for s in ("GPT-5.2 agent", "Aristotle"):
        mine = [r for r in rev if r["model"] == s]
        out["by_system"][s] = {"rejected": len(mine), "human_errors": sum(map(err, mine)),
                               "review_T": sum(map(final_t, mine)), "review_T_either": sum(map(either_t, mine))}
    solo = {r["case_id"]: r["category"] == "T" for r in jsonl(REPO / "checks" / "reviewer_validation.jsonl")}
    out["single_reviewer_same_outputs"] = {
        "finds_errors": wilson(sum(solo[r["case_id"]] for r in errs), len(errs)),
        "leaves_faithful": wilson(sum(not solo[r["case_id"]] for r in oks), len(oks))}
    # Agreement with the human labels, against the agreement of a held-out reviewer with the other two.
    votes = []
    for r in rev:
        h = human[r["case_id"]]
        v = {k: (None if h[k] == "" else int(float(h[k]) < 9)) for k in ("R2", "R3", "R4")}
        votes.append({**v, "review": int(final_t(r)), "majority": int(err(r))})
    out["agreement_with_majority"] = kappa([(v["review"], v["majority"]) for v in votes])
    out["held_out_reviewer"] = {}
    for j in ("R2", "R3", "R4"):
        a, b = [x for x in ("R2", "R3", "R4") if x != j]
        sub = [v for v in votes if None not in (v[j], v[a], v[b]) and v[a] == v[b]]
        out["held_out_reviewer"][j] = {"reference": f"{a}+{b} agree", "reviewer": kappa([(v[j], v[a]) for v in sub]),
                                       "review": kappa([(v["review"], v[a]) for v in sub])}
    out["reviewer_pairs"] = {f"{a}-{b}": kappa([(v[a], v[b]) for v in votes if None not in (v[a], v[b])])
                             for a, b in (("R2", "R3"), ("R2", "R4"), ("R3", "R4"))}
    return out


def earlier_systems(sens: float) -> dict:
    rev = jsonl(REPO / "checks" / "earlier_systems_review.jsonl")
    out = {}
    for s, f in ONE_SHOT.items():
        rows = [r for r in jsonl(REPO / "outputs" / "one_shot" / f"{f}.jsonl") if r.get("input_matches_benchmark", True) is not False]
        c = sum(r["compiles"] for r in rows)
        rejected = sum(1 for r in rows if r["compiles"] and r["gpt52_grade"] < 9)
        mine = [r for r in rev if r["model"] == s]
        assert len(mine) == rejected, (s, len(mine), rejected)
        t = sum(r["final_category"] == "T" for r in mine)
        te = sum("T" in (r["first_review"]["category"], r["second_review"]["category"]) for r in mine)
        out[s] = {"statements": len(rows), "compiling": c, "accepted": c - rejected, "rejected": rejected,
                  "compile_pct": round(100 * c / len(rows), 1), "accepted_pct": round(100 * (c - rejected) / len(rows), 1),
                  "gap_pts": round(100 * rejected / len(rows), 1),
                  "translation_errors": t, "translation_errors_either_stage": te,
                  "translation_errors_pts": round(100 * t / len(rows), 1),
                  "translation_errors_either_pts": round(100 * te / len(rows), 1),
                  "final_classes": dict(Counter(r["final_category"] for r in mine)),
                  "real_error_share_of_rejections": round(t / rejected, 4),
                  "unfaithful_share": round(t / c, 4),
                  "errors_upper_bound": round(min(rejected, t / sens), 1)}
    tot = Counter()
    for v in out.values():
        tot.update({"rejected": v["rejected"], "T": v["translation_errors"], "T_either": v["translation_errors_either_stage"]})
    out["total"] = dict(tot)
    return out


def newer_bound(sens: float) -> dict:
    rev = jsonl(REPO / "checks" / "newer_models_review.jsonl")
    out = {}
    for s in ("GPT-6 Astra", "Claude Opus 5.5"):
        mine = [r for r in rev if r["model"] == s]
        t = sum(r["final_category"] == "T" for r in mine)
        out[s] = {"rejected": len(mine), "translation_errors": t, "errors_upper_bound": round(t / sens, 1)}
    return out


def discussion_side() -> dict:
    """Which review the discussion round's decision matches (its adjudicator is the second reviewer's model)."""
    out = {}
    for name, f in (("newer models", "newer_models_review.jsonl"), ("validation", "review_validation.jsonl"),
                    ("earlier systems", "earlier_systems_review.jsonl")):
        side = Counter()
        for r in jsonl(REPO / "checks" / f):
            d = r.get("discussion")
            if not d:
                continue
            final = d.get("final_category", d.get("category"))
            side["second" if final == r["second_review"]["category"] else
                 "first" if final == r["first_review"]["category"] else "neither"] += 1
        out[name] = dict(side)
    return out


def main() -> None:
    val = validation()
    sens = val["final_T"]["finds_errors"]["k"] / val["final_T"]["finds_errors"]["n"]
    res = {"validation": val, "earlier_systems": earlier_systems(sens), "newer_models_bound": newer_bound(sens),
           "discussion_followed": discussion_side()}
    (REPO / "analysis" / "review_v4.json").write_text(json.dumps(res, indent=1) + "\n")
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
