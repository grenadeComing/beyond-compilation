"""Recompute the numbers reported in "Beyond Compilation" from the released data.

    python analysis/reproduce.py            # writes analysis/results.json

Conventions
- Faithful = compiles and GPT-5.2 grade >= 9 and Gemini-2.5-Pro grade >= 9.
- Kimina Prover, Kimina Autoformalizer and StepFun are evaluated on the 217
  statements where `input_matches_benchmark` is true.
- Effects are average high-minus-low differences over the other factors, with
  95% intervals from paired item-level bootstrap resampling (B = 10,000).
- Newer models (GPT-6 Astra, Claude Opus 5.5) were not graded by Gemini-2.5-Pro, so
  their table accepts an output if it compiles and GPT-5.2 grades it at least 9, and
  applies that rule to every row.
"""

from __future__ import annotations

import csv
import json
import math
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[1]
OUT = REPO / "outputs"
CONFIGS = ("000", "001", "010", "011", "100", "101", "110", "111")
DOMAINS = ("Algebra", "Complex Analysis", "Real Analysis", "Topology")
REVIEWERS = ("R2", "R3", "R4")
STEP_BINS = ((1, 2), (3, 5), (6, 9), (10, 12), (13, 18), (19, 24))
B = 10_000
ONE_SHOT = {"Kimina Prover": "kimina_prover", "Goedel Prover": "goedel_prover", "Kimina AutoF": "kimina_autof",
            "Herald": "herald", "StepFun": "stepfun", "GPT-5.2": "gpt-52", "Gemini-2.5-Pro": "gemini-25-pro",
            "Sonnet 4.5": "sonnet_45"}
FIGURE1 = ("Kimina Prover", "Goedel Prover", "Kimina AutoF", "Herald", "StepFun", "GPT-5.2", "Gemini-2.5-Pro")
NEWER = {"GPT-6 Astra": "gpt-6-astra", "Claude Opus 5.5": "claude-opus-5-5"}


def jsonl(path):
    with open(path, encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def table(path):
    with open(path, newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def num(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return math.nan


def pct(a, b):
    return round(100 * a / b, 1) if b else math.nan


def wilson(k, n, z=1.959963984540054):
    if not n:
        return [math.nan, math.nan]
    p = k / n
    c = (p + z * z / (2 * n)) / (1 + z * z / n)
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / (1 + z * z / n)
    return [round(100 * (c - h), 1), round(100 * (c + h), 1)]


def rate(k, n):
    return {"k": k, "n": n, "pct": pct(k, n), "wilson95": wilson(k, n)}


def mcnemar(b, c):
    n = b + c
    return 1.0 if n == 0 else min(1.0, 2 * sum(math.comb(n, i) for i in range(min(b, c) + 1)) / 2 ** n)


def boolv(x):
    return str(x) == "True" or x is True


# ---------------------------------------------------------------- data

BENCH = jsonl(REPO / "benchmark" / "benchmark.jsonl")
IDS = [r["id"] for r in BENCH]
DOMAIN = {r["id"]: r["domain"] for r in BENCH}
# Bootstrap order: sorted by (name, statement), as in the original analysis.
BOOT_IDS = [r["id"] for r in sorted(BENCH, key=lambda r: (r["name"], r["nl_statement"]))]


def system(path):
    return {r["id"]: r for r in jsonl(path)}


one_shot = {s: system(OUT / "one_shot" / f"{f}.jsonl") for s, f in ONE_SHOT.items()}
cfg = {c: system(OUT / "gpt52_agent" / f"config_{c}.jsonl") for c in CONFIGS}
newer = {s: system(OUT / "newer_models" / f"{f}.jsonl") for s, f in NEWER.items()}
alt = {"Sonnet 4.5": system(OUT / "other_orchestrators" / "sonnet45_agent_config_111.jsonl"),
       "Gemini-2.5-Pro": system(OUT / "other_orchestrators" / "gemini25pro_agent_config_111.jsonl")}


def faithful(r, t=9):
    return r["compiles"] and (r["gpt52_grade"] or 0) >= t and (r["gemini25pro_grade"] or 0) >= t


def eval_ids(sys_):
    return [i for i in IDS if sys_[i]["input_matches_benchmark"]]


def counts(sys_, ids):
    rs = [sys_[i] for i in ids]
    gp = [r["compiles"] and (r["gpt52_grade"] or 0) >= 9 for r in rs]
    mp = [r["compiles"] and (r["gemini25pro_grade"] or 0) >= 9 for r in rs]
    comp, faith = sum(r["compiles"] for r in rs), sum(a and b for a, b in zip(gp, mp))
    return {"n": len(rs), "compile": comp, "faithful": faith, "compile_pct": pct(comp, len(rs)),
            "faithful_pct": pct(faith, len(rs)), "gap_pts": round(100 * (comp - faith) / len(rs), 1),
            "gpt_pos": sum(gp), "gem_pos": sum(mp), "consensus": faith,
            "gpt_only": sum(a and not b for a, b in zip(gp, mp))}


# ---------------------------------------------------------------- factorial


def main_effect(v, f, idx):
    hi = [v[c][idx].mean() * 100 for c in CONFIGS if c[f] == "1"]
    lo = [v[c][idx].mean() * 100 for c in CONFIGS if c[f] == "0"]
    return float(np.mean(hi) - np.mean(lo))


def interaction(v, a, b, idx):
    g = defaultdict(list)
    for c in CONFIGS:
        g[(c[a], c[b])].append(v[c][idx].mean() * 100)
    m = {k: np.mean(x) for k, x in g.items()}
    return float((m["1", "1"] - m["0", "1"]) - (m["1", "0"] - m["0", "0"]))


def conditional(v, f, cond, val, idx):
    hi = [v[c][idx].mean() * 100 for c in CONFIGS if c[f] == "1" and c[cond] == val]
    lo = [v[c][idx].mean() * 100 for c in CONFIGS if c[f] == "0" and c[cond] == val]
    return float(np.mean(hi) - np.mean(lo))


def factorial():
    ids = BOOT_IDS
    n = len(ids)
    idx = np.arange(n)
    comp = {c: np.array([cfg[c][i]["compiles"] for i in ids]) for c in CONFIGS}
    faith = {c: np.array([faithful(cfg[c][i]) for i in ids]) for c in CONFIGS}
    gap = {c: comp[c] & ~faith[c] for c in CONFIGS}
    out = {"configs": {}}
    for c in CONFIGS:
        cc, ff = int(comp[c].sum()), int(faith[c].sum())
        out["configs"][c] = {"compile": cc, "faithful": ff, "compile_pct": pct(cc, n), "faithful_pct": pct(ff, n),
                             "faithful_given_compile_pct": pct(ff, cc), "gap_count": cc - ff}
    rng = np.random.default_rng(42)
    fns = {"T": lambda i: main_effect(faith, 0, i), "F": lambda i: main_effect(faith, 1, i),
           "S": lambda i: main_effect(faith, 2, i), "FxS": lambda i: interaction(faith, 1, 2, i),
           "FxT": lambda i: interaction(faith, 1, 0, i), "SxT": lambda i: interaction(faith, 2, 0, i)}
    eff = {}
    for k, fn in fns.items():
        bs = np.array([fn(rng.choice(idx, size=n, replace=True)) for _ in range(B)])
        lo, hi = np.percentile(bs, [2.5, 97.5])
        eff[k] = {"effect": round(fn(idx), 1), "ci95": [round(lo, 1), round(hi, 1)]}
    out["effects_faithful"] = eff
    rng2 = np.random.default_rng(43)
    boot = [rng2.choice(idx, size=n, replace=True) for _ in range(B)]

    def ci(fn):
        lo, hi = np.percentile([fn(i) for i in boot], [2.5, 97.5])
        return {"effect": round(fn(idx), 1), "ci95": [round(lo, 1), round(hi, 1)]}

    metrics = {"faithful": faith, "compile": comp, "gap": gap}
    out["effects_all"] = {f: {m: ci(lambda i, v=v, k=k: main_effect(v, k, i)) for m, v in metrics.items()}
                          for f, k in (("T", 0), ("F", 1), ("S", 2))}
    out["conditional_all"] = {f"{f}|{g}={val}": {m: ci(lambda i, v=v, k=k, gk=gk, val=val: conditional(v, k, gk, val, i))
                                                 for m, v in metrics.items()}
                              for f, k, g, gk in (("S", 2, "F", 1), ("T", 0, "F", 1), ("F", 1, "S", 2)) for val in "01"}
    out["threshold"] = {}
    for t in (7, 8, 9, 10):
        v = {c: np.array([faithful(cfg[c][i], t) for i in ids]) for c in CONFIGS}
        out["threshold"][str(t)] = {"effects": {f: round(main_effect(v, k, idx), 1) for f, k in (("T", 0), ("F", 1), ("S", 2))},
                                    "gap_111_pts": round(comp["111"].mean() * 100 - v["111"].mean() * 100, 1)}
    out["transition_ledger"] = {}
    for a, b in (("000", "010"), ("001", "011"), ("101", "111"), ("010", "011"), ("110", "111"), ("011", "111")):
        new, lost = int((faith[b] & ~faith[a]).sum()), int((faith[a] & ~faith[b]).sum())
        out["transition_ledger"][f"{a}->{b}"] = {"new": new, "lost": lost, "net": new - lost}
    stack = np.vstack([faith[c] for c in CONFIGS])
    missed = ~faith["111"] & stack.any(axis=0)
    out["oracle"] = {"faithful_111": int(faith["111"].sum()), "any": int(stack.any(axis=0).sum()),
                     "all": int(stack.all(axis=0).sum()), "never": int((~stack.any(axis=0)).sum()),
                     "missed_by_111_faithful_elsewhere": int(missed.sum()),
                     "missed_compile_pass_111": int((missed & comp["111"]).sum())}
    return out


def trajectory():
    out = {}
    for label, cfgs in (("F1", ("010", "011", "110", "111")), ("F0", ("001", "100", "101"))):
        rows = [(cfg[c][i]["steps"], faithful(cfg[c][i])) for c in cfgs for i in IDS]
        out[label] = {f"{lo}-{hi}": {"faithful": sum(f for s, f in rows if lo <= s <= hi),
                                     "n": sum(1 for s, _ in rows if lo <= s <= hi)} for lo, hi in STEP_BINS}
    return out


def tool_usage():
    out = {}
    for c in ("010", "011", "110", "111"):
        tot = Counter()
        for r in jsonl(OUT / "trajectories" / f"gpt52_agent_config_{c}.jsonl"):
            for e in r["events"]:
                if e.get("action") == "model_reply:" and e.get("tools_requested"):
                    t = e["tools_requested"]
                    tot.update(t if isinstance(t, list) else [t])
        out[c] = {"translator": tot["lean4_translation"], "repl": tot["lean4_repl_runner"],
                  "search_total": tot["lean_resolve_name"] + tot["lean_inspect_name"] + tot["search_online"]}
    return out


def third_judge():
    def summ(cs):
        comp = res = agree = pos = pos_ok = neg = neg_ok = 0
        for c in cs:
            for i in IDS:
                r = cfg[c][i]
                if not r["compiles"]:
                    continue
                comp += 1
                if r["sonnet5_grade"] is None or r["sonnet5_grade"] < 0:
                    continue
                res += 1
                crit, son = faithful(r), r["sonnet5_grade"] >= 9
                agree += crit == son
                pos += crit
                pos_ok += crit and son
                neg += not crit
                neg_ok += (not crit) and (not son)
        return {"coverage": rate(res, comp), "agreement": rate(agree, res),
                "positive_confirmed": rate(pos_ok, pos), "negative_confirmed": rate(neg_ok, neg)}
    return {"all_8": summ(CONFIGS), "config_111": summ(("111",))}


# ---------------------------------------------------------------- human audits


def majority(scores, compiles):
    vals = [s for s in scores if not math.isnan(s)]
    if len(vals) < 2:
        return None
    return 0 if not compiles else int(sum(v >= 9 for v in vals) > len(vals) / 2)


def audits():
    out = {}
    r1 = table(REPO / "human_audits" / "reviewer1_accepted_outputs.csv")
    scored = [r for r in r1 if not math.isnan(num(r["R1_grade"]))]
    strict = [r for r in scored if boolv(r["criterion_faithful"])]
    out["reviewer1"] = {"scored": len(scored), "strict_positive": len(strict),
                        "precision_strict": rate(sum(num(r["R1_grade"]) >= 9 for r in strict), len(strict))}
    a = table(REPO / "human_audits" / "batch_A_agent_rejected.csv")
    dec = [r for r in a if r["human_majority_faithful"] != ""]
    out["batch_A"] = {"selected": len(a), "confirmed_negative": rate(sum(r["human_majority_faithful"] == "0" for r in dec), len(dec))}
    b = table(REPO / "human_audits" / "batch_B_aristotle_random.csv")
    eff = [r for r in b if boolv(r["aristotle_output"])]
    bd = [r for r in eff if r["human_majority_faithful"] != ""]
    crit = lambda r: boolv(r["criterion_faithful"])  # noqa: E731
    hum = lambda r: r["human_majority_faithful"] == "1"  # noqa: E731
    pos = [r for r in bd if crit(r)]
    neg = [r for r in bd if not crit(r)]
    out["batch_B"] = {"statements": len(b), "effective": len(eff),
                      "agreement": rate(sum(crit(r) == hum(r) for r in bd), len(bd)),
                      "precision": rate(sum(hum(r) for r in pos), len(pos)),
                      "compile_pass_negative_confirmed": rate(sum(not hum(r) for r in neg if boolv(r["compiles"])),
                                                              sum(boolv(r["compiles"]) for r in neg)),
                      "all_negative_confirmed": rate(sum(not hum(r) for r in neg), len(neg))}
    ls = {r["case_id"]: boolv(r["leanscorer_pass"]) for r in table(REPO / "checks" / "leanscorer_batch_B.csv")}
    both = ours = lso = 0
    for r in bd:
        x, y = crit(r) == hum(r), ls[r["case_id"]] == hum(r)
        both += x and y
        ours += x and not y
        lso += y and not x
    out["leanscorer"] = {"agreement_leanscorer": rate(both + lso, len(bd)), "paired": {"both": both, "ours_only": ours, "leanscorer_only": lso},
                         "mcnemar_exact_p": round(mcnemar(ours, lso), 4)}
    return out


def beq():
    # Anchors must be outputs that the expert confirmed in the released positive audit (score >= 9).
    # This drops two anchors (BC188, BC224) whose expert score was given to a mismatched Lean output
    # (the audit showed the output of another statement with the same name).
    r1 = {r["id"] for r in table(REPO / "human_audits" / "reviewer1_accepted_outputs.csv")
          if not math.isnan(num(r["R1_grade"])) and num(r["R1_grade"]) >= 9}
    all_rows = table(REPO / "checks" / "beq_pairs.csv")
    rows = [r for r in all_rows if r["id"] in r1]
    dropped = sorted({r["id"] for r in all_rows} - r1)
    by = defaultdict(list)
    for r in rows:
        by[r["anchor"]].append(boolv(r["certified"]))
    ids = sorted(by)
    k = np.array([sum(by[a]) for a in ids])
    n = np.array([len(by[a]) for a in ids])
    rng = np.random.default_rng(42)
    bs = []
    for _ in range(B):
        s = rng.integers(0, len(ids), len(ids))
        bs.append(k[s].sum() / n[s].sum() * 100)
    lo, hi = np.percentile(bs, [2.5, 97.5])
    same = [r for r in rows if boolv(r["same_normalized_encoding"])]
    diff = [r for r in rows if not boolv(r["same_normalized_encoding"])]
    return {"anchors": len(ids), "pairs": len(rows), "certified": int(k.sum()), "dropped_anchor_ids": dropped,
            "different_encoding": {"certified": sum(boolv(r["certified"]) for r in diff), "n": len(diff)},
            "certified_exact": sum(boolv(r["certified_by_exact"]) for r in rows),
            "anchor_bootstrap_ci95": [round(lo, 1), round(hi, 1)],
            "same_encoding": {"certified": sum(boolv(r["certified"]) for r in same), "n": len(same)}}


def domains():
    out = {}
    for d in DOMAINS:
        ids = [i for i in IDS if DOMAIN[i] == d]
        n = len(ids)
        comp = {c: np.array([cfg[c][i]["compiles"] for i in ids]) for c in CONFIGS}
        faith = {c: np.array([faithful(cfg[c][i]) for i in ids]) for c in CONFIGS}
        idx = np.arange(n)
        f1 = [c for c in CONFIGS if c[1] == "1"]
        d_comp, d_faith = main_effect(comp, 1, idx), main_effect(faith, 1, idx)
        out[d] = {"n": n,
                  "feedback": {"d_compile": round(d_comp, 1), "d_faithful": round(d_faith, 1), "d_gap": round(d_comp - d_faith, 1),
                               "faithful_given_compile_F1_pct": pct(sum(faith[c].sum() for c in f1), sum(comp[c].sum() for c in f1))},
                  "faithful_rate_by_config": {c: round(float(faith[c].mean()), 3) for c in CONFIGS}}
    return out


def judge_disagreement_by_domain():
    systems = [one_shot["Herald"], one_shot["GPT-5.2"], one_shot["Gemini-2.5-Pro"]] + [cfg[c] for c in CONFIGS if c != "000"]
    counts_ = Counter()
    for sys_ in systems:
        for i in IDS:
            r = sys_[i]
            if ((r["gpt52_grade"] or 0) >= 9) != ((r["gemini25pro_grade"] or 0) >= 9):
                counts_[DOMAIN[i]] += 1
    return dict(counts_)


def newer_models():
    """Newer one-shot models: compile, accepted (compiles and GPT-5.2 >= 9) and gap for every row,
    and the final classes from the review of the newer models' rejected compiling outputs."""
    def row(sys_, ids):
        rs = [sys_[i] for i in ids]
        comp = sum(r["compiles"] for r in rs)
        acc = sum(r["compiles"] and (r["gpt52_grade"] or 0) >= 9 for r in rs)
        return {"n": len(rs), "compile": comp, "accepted": acc, "compile_pct": pct(comp, len(rs)),
                "accepted_pct": pct(acc, len(rs)), "gap_pts": round(100 * (comp - acc) / len(rs), 1)}
    out = {s: row(one_shot[s], eval_ids(one_shot[s])) for s in ("GPT-5.2", "Gemini-2.5-Pro", "Sonnet 4.5")}
    out["GPT-5.2 agent"] = row(cfg["111"], IDS)
    # Under the same rule, every compiling output GPT-5.2 rejects for the agent is in Batch A.
    batch_a = {r["id"]: r["human_majority_faithful"] for r in table(REPO / "human_audits" / "batch_A_agent_rejected.csv")}
    rej = [i for i in IDS if cfg["111"][i]["compiles"] and (cfg["111"][i]["gpt52_grade"] or 0) < 9]
    assert all(i in batch_a for i in rej)
    errs = sum(batch_a[i] == "0" for i in rej)
    out["GPT-5.2 agent"]["human_audit"] = {"rejected": len(rej), "translation_errors": errs,
                                          "translation_errors_pts": round(100 * errs / len(IDS), 1)}
    review = jsonl(REPO / "checks" / "newer_models_review.jsonl")
    for s, sys_ in newer.items():
        out[s] = row(sys_, IDS)
        mine = [r for r in review if r["model"] == s]
        assert len(mine) == out[s]["compile"] - out[s]["accepted"]
        errors = sum(r["final_category"] == "T" for r in mine)
        out[s]["review"] = {"rejected": len(mine), "final": dict(Counter(r["final_category"] for r in mine)),
                            "translation_errors": errors, "translation_errors_pts": round(100 * errors / len(IDS), 1)}
    non_errors = [r for r in review if r["final_category"] != "T"]
    out["judge_failures"] = dict(Counter(r["judge_failure"] for r in non_errors))
    son = [newer[r["model"]][r["id"]]["sonnet5_grade"] for r in non_errors]
    graded = [g for g in son if g is not None and g >= 0]
    out["sonnet5_on_judge_failures"] = {"graded": len(graded), "also_rejects": sum(g < 9 for g in graded)}

    # How often faithful compiling outputs are rejected, by system, under acceptance by GPT-5.2 alone (the rule
    # of the newer-model table). Earlier systems use the human audits: all of Aristotle's sample, and for the
    # agent its rejections (all in Batch A) with its accepted outputs scaled by the positive audit's precision.
    # Newer models use the review (outputs that are not translation errors, and only those judged faithful).
    # e = unfaithful share of compiling outputs; for the newer models only rejected outputs were reviewed, so
    # e counts only errors among them (a lower bound).
    gacc = lambda r: (num(r["gpt52_grade"]) if not math.isnan(num(r["gpt52_grade"])) else 0) >= 9  # noqa: E731
    b = table(REPO / "human_audits" / "batch_B_aristotle_random.csv")
    comp = [r for r in b if boolv(r["compiles"]) and r["human_majority_faithful"] != ""]
    ar = [r for r in comp if not gacc(r)]
    fa = sum(r["human_majority_faithful"] == "1" for r in comp)
    fr = sum(r["human_majority_faithful"] == "1" for r in ar)
    unf = sum(r["human_majority_faithful"] == "0" for r in comp)
    fr_rate = {"Aristotle": {"rule": "compiles and GPT-5.2 >= 9", "rejected_faithful": fr, "faithful": fa, "pct": pct(fr, fa),
                             "unfaithful_share": round(unf / len(comp), 4),
                             "real_error_share_of_rejections": round((len(ar) - fr) / len(ar), 4)}}
    a = {r["id"]: r["human_majority_faithful"] for r in table(REPO / "human_audits" / "batch_A_agent_rejected.csv")}
    r1 = [r for r in table(REPO / "human_audits" / "reviewer1_accepted_outputs.csv")
          if boolv(r["criterion_faithful"]) and not math.isnan(num(r["R1_grade"]))]
    precision = sum(num(r["R1_grade"]) >= 9 for r in r1) / len(r1)
    c111 = [i for i in IDS if cfg["111"][i]["compiles"]]
    g_ok = lambda i: (cfg["111"][i]["gpt52_grade"] or 0) >= 9  # noqa: E731
    rej = [i for i in c111 if not g_ok(i)]
    cons = [i for i in c111 if faithful(cfg["111"][i])]
    gem_rej = [i for i in c111 if g_ok(i) and not faithful(cfg["111"][i])]   # GPT accepts, Gemini rejects: in Batch A
    assert all(i in a for i in rej + gem_rej)
    rescued = sum(a[i] == "1" for i in rej)
    acc_faithful = len(cons) * precision + sum(a[i] == "1" for i in gem_rej)
    acc_unf = len(cons) * (1 - precision) + sum(a[i] == "0" for i in gem_rej)
    fr_rate["GPT-5.2 agent"] = {"rule": "compiles and GPT-5.2 >= 9", "rejected_faithful": rescued, "rejected": len(rej),
                                "audit_precision": round(precision, 3),
                                "pct_estimated": round(100 * rescued / (acc_faithful + rescued), 1),
                                "unfaithful_share": round((len(rej) - rescued + acc_unf) / len(c111), 4),
                                "real_error_share_of_rejections": round((len(rej) - rescued) / len(rej), 4)}
    for s_, sys_ in newer.items():
        mine = [r for r in review if r["model"] == s_]
        nonerr = sum(r["final_category"] != "T" for r in mine)
        judged_faithful = sum(r["final_category"] == "J" for r in mine)
        err = len(mine) - nonerr
        fr_rate[s_] = {"rule": "compiles and GPT-5.2 >= 9", "rejected_not_at_fault": nonerr, "accepted": out[s_]["accepted"],
                       "pct": pct(nonerr, out[s_]["accepted"] + nonerr),
                       "pct_judged_faithful_only": pct(judged_faithful, out[s_]["accepted"] + judged_faithful),
                       "unfaithful_share": round(err / out[s_]["compile"], 4),
                       "real_error_share_of_rejections": round(err / len(mine), 4)}
    out["false_rejection_rate"] = fr_rate

    # Sensitivity: the same numbers without the statements flagged in benchmark/known_issues.csv.
    flagged = {r["id"] for r in table(REPO / "benchmark" / "known_issues.csv")}
    keep = [i for i in IDS if i not in flagged]
    sens = {"flagged": len(flagged), "statements": len(keep), "criterion": {}, "gpt_only": {}}
    for s_, sys_ in one_shot.items():
        sens["criterion"][s_] = counts(sys_, [i for i in eval_ids(sys_) if i not in flagged])
    sens["criterion"]["GPT-5.2 agent"] = counts(cfg["111"], keep)
    sens["gpt_only"]["GPT-5.2 agent"] = row(cfg["111"], keep)
    a_lab = {r["id"]: r["human_majority_faithful"] for r in table(REPO / "human_audits" / "batch_A_agent_rejected.csv")}
    rej = [i for i in keep if cfg["111"][i]["compiles"] and (cfg["111"][i]["gpt52_grade"] or 0) < 9]
    errs = sum(a_lab[i] == "0" for i in rej)
    sens["gpt_only"]["GPT-5.2 agent"]["human_audit"] = {"rejected": len(rej), "translation_errors": errs,
                                                        "translation_errors_pts": round(100 * errs / len(keep), 1)}
    for s_, sys_ in newer.items():
        mine = [r for r in review if r["model"] == s_ and r["id"] not in flagged]
        sens["gpt_only"][s_] = row(sys_, keep)
        sens["gpt_only"][s_]["review"] = {"rejected": len(mine), "final": dict(Counter(r["final_category"] for r in mine)),
                                          "either_review_T": sum("T" in (r["first_review"]["category"], r["second_review"]["category"]) for r in mine)}
    out["sensitivity_without_flagged"] = sens

    # The reviewer model against human labels: rejected compiling outputs of earlier systems with a
    # human-majority label; a translation error (T) should match human-majority unfaithful.
    human = {r["case_id"]: r["human_majority_faithful"] for r in table(REPO / "human_audits" / "batch_A_agent_rejected.csv")}
    human.update({r["case_id"]: r["human_majority_faithful"] for r in table(REPO / "human_audits" / "batch_B_aristotle_random.csv")})
    val = jsonl(REPO / "checks" / "reviewer_validation.jsonl")
    unf = [r for r in val if human[r["case_id"]] == "0"]
    fai = [r for r in val if human[r["case_id"]] == "1"]
    out["reviewer_validation"] = {
        "n": len(val), "agreement": rate(sum((r["category"] == "T") == (human[r["case_id"]] == "0") for r in val), len(val)),
        "unfaithful_classified_T": rate(sum(r["category"] == "T" for r in unf), len(unf)),
        "faithful_classified_not_T": rate(sum(r["category"] != "T" for r in fai), len(fai)),
        "classes_unfaithful": dict(Counter(r["category"] for r in unf)),
        "classes_faithful": dict(Counter(r["category"] for r in fai))}

    # Re-grading: five more GPT-5.2 calls per output; "majority" = at least three of five grades >= 9.
    final = {(r["id"], r["model"]): r["final_category"] for r in review}
    rg = jsonl(REPO / "checks" / "newer_models_regrade.jsonl")
    def flips(rows, want_accept):
        maj = [sum(g >= 9 for g in r["regrades"]) > len(r["regrades"]) / 2 for r in rows]
        return {"n": len(rows), "majority_accepts": sum(maj),
                "at_least_one_accepts": sum(any(g >= 9 for g in r["regrades"]) for r in rows),
                "at_least_one_rejects": sum(any(g < 9 for g in r["regrades"]) for r in rows)}
    rej = [r for r in rg if r["group"] == "rejected"]
    out["regrade"] = {
        "rejected_not_errors": flips([r for r in rej if final[(r["id"], r["model"])] != "T"], True),
        "rejected_errors": flips([r for r in rej if final[(r["id"], r["model"])] == "T"], True),
        "accepted_sample": flips([r for r in rg if r["group"] == "accepted_sample"], False)}
    return out


def main():
    res = {"n": len(IDS), "domains": dict(Counter(DOMAIN.values()))}
    res["one_shot"] = {s: counts(sys_, eval_ids(sys_)) for s, sys_ in one_shot.items()}
    res["configs"] = {c: counts(cfg[c], IDS) for c in CONFIGS}
    res["alt_orchestrators"] = {s: counts(sys_, IDS) for s, sys_ in alt.items()}
    res["figure1"] = {s: res["one_shot"][s] for s in FIGURE1} | {"GPT-5.2 agent": res["configs"]["111"]}
    res["factorial"] = factorial()
    res["trajectory"] = trajectory()
    res["tool_usage"] = tool_usage()
    res["third_judge"] = third_judge()
    res["human"] = audits()
    res["beq"] = beq()
    res["domain"] = domains()
    res["judge_disagreement_by_domain"] = judge_disagreement_by_domain()
    res["newer_models"] = newer_models()
    path = REPO / "analysis" / "results.json"
    path.write_text(json.dumps(res, indent=1, ensure_ascii=False))
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
