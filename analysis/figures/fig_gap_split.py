"""Measured gap split into translation errors and rejections that are not, under acceptance by GPT-5.2
alone, for the three systems whose rejected compiling outputs were all labeled: our GPT-5.2 agent (human
audit, Batch A) and the two newer models (model review). Same style as Figure 1 (bars, colours, group
braces) and the judge-regime figure (single column, bold text); printed to PDF with headless Chrome.

    python analysis/figures/fig_gap_split.py [out.pdf]

Bars are points of the 227 statements; numbers count rejected compiling outputs. For the newer models,
the dashed mark is the count when every output that either review stage classifies as a translation error
is counted.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from fig_judge_regime import render, text
from fig_main_results import GREY, GRID, GROUP, INK, ORANGE, RED, RES, bar_path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
W, H = 1000, 820                      # same page size as fig_judge_regime.render
X0, X1, Y0 = 150, 965, 610            # plot box; Y0 is the baseline
PX = 14.0                             # pixels per percentage point
BAR = 120
LIGHT = "#dfe8f4"                     # the band colour of the judge-regime figure
CENTERS = (330, 605, 845)


def counts() -> list[dict]:
    n = RES["n"]
    agent = RES["newer_models"]["GPT-5.2 agent"]["human_audit"]
    rows = [{"label": "Our agent", "rejected": agent["rejected"], "errors": agent["translation_errors"], "either": None}]
    review = [json.loads(l) for l in (REPO / "checks" / "newer_models_review.jsonl").read_text().splitlines()]
    for key, label in (("GPT-6 Astra", "GPT-6 Astra"), ("Claude Opus 5.5", "Opus 5.5")):
        mine = [r for r in review if r["model"] == key]
        rows.append({"label": label, "rejected": len(mine),
                     "errors": sum(r["final_category"] == "T" for r in mine),
                     "either": sum("T" in (r["first_review"]["category"], r["second_review"]["category"]) for r in mine)})
    for r in rows:
        r["gap"], r["err_pts"] = 100 * r["rejected"] / n, 100 * r["errors"] / n
        r["either_pts"] = None if r["either"] is None else 100 * r["either"] / n
    return rows


def svg() -> str:
    rows = counts()
    p = [f'<rect x="12.5" y="12.5" width="{W - 25}" height="{H - 25}" rx="3" fill="#fff" stroke="{INK}" stroke-width="3"/>']
    for v in (0, 10, 20, 30):
        y = Y0 - v * PX
        if v:
            p.append(f'<line x1="{X0}" x2="{X1}" y1="{y}" y2="{y}" stroke="{GRID}" stroke-width="2.5" stroke-dasharray="7 7"/>')
        p.append(text(X0 - 16, y + 12, f"{v}", 36, "serif", GREY, "end"))
    p.append(f'<line x1="{X0}" x2="{X1}" y1="{Y0}" y2="{Y0}" stroke="{INK}" stroke-width="3"/>')
    mid = (Y0 + Y0 - 30 * PX) / 2
    p.append(text(62, mid, "measured gap (points)", 36, "serif", GREY, extra=f'transform="rotate(-90 62 {mid})"'))
    # legend, as in Figure 1
    lx, ly = X0 + 380, 62
    p.append(f'<rect x="{lx}" y="{ly}" width="32" height="27" rx="4" fill="{ORANGE}"/>')
    p.append(text(lx + 44, ly + 24, "translation errors", 34, "serif", INK, "start"))
    p.append(f'<rect x="{lx}" y="{ly + 44}" width="32" height="27" rx="4" fill="{LIGHT}"/>')
    p.append(text(lx + 44, ly + 68, "not translation errors", 34, "serif", INK, "start"))
    for r, cx in zip(rows, CENTERS):
        x = cx - BAR / 2
        p.append(bar_path(x, r["gap"], LIGHT, Y0, PX, BAR))
        ye = Y0 - r["err_pts"] * PX
        p.append(f'<rect x="{x}" y="{ye}" width="{BAR}" height="{Y0 - ye}" fill="{ORANGE}"/>')
        if r["either_pts"] is not None:
            yx = Y0 - r["either_pts"] * PX
            p.append(f'<line x1="{x - 8}" x2="{x + BAR + 8}" y1="{yx}" y2="{yx}" stroke="{INK}" stroke-width="3" stroke-dasharray="9 6"/>')
        top = Y0 - r["gap"] * PX
        p.append(text(cx, top - 18, f"gap {r['gap']:.1f}", 36, "hand", RED, extra=f'stroke="{RED}" stroke-width="0.35"'))
        non = r["rejected"] - r["errors"]
        p.append(text(cx, (top + ye) / 2 + 12, f"{non}", 36, "serif", INK))
        if Y0 - ye > 50:
            p.append(text(cx, (ye + Y0) / 2 + 12, f"{r['errors']}", 36, "serif", "#fff"))
        else:
            p.append(text(cx + BAR / 2 + 12, ye - 4, f"{r['errors']}", 34, "serif", ORANGE, "start"))
        p.append(text(cx, Y0 + 46, r["label"], 36, "serif", INK))
    # group braces, as in Figure 1
    for name, a, b in (("human audit", CENTERS[0] - 80, CENTERS[0] + 80), ("model review", CENTERS[1] - 80, CENTERS[2] + 80)):
        rr, yb = 11, Y0 + 72
        p.append(f'<path d="M{a},{yb} Q{a},{yb + 11} {a + rr},{yb + 11} H{b - rr} Q{b},{yb + 11} {b},{yb}" '
                 f'fill="none" stroke="{GROUP}" stroke-width="3" stroke-linecap="round"/>')
        p.append(text((a + b) / 2, yb + 56, name, 36, "hand", GROUP))
    return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{W / 300}in" height="{H / 300}in" '
            f'viewBox="0 0 {W} {H}">' + "".join(p) + "</svg>")


if __name__ == "__main__":
    render(svg(), Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "fig_gap_split.pdf")
