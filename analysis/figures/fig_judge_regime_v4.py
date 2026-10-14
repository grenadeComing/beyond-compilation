"""Figure 3 of arXiv v4: the judge-regime figure with every system whose rejections were classified.

    python analysis/figures/fig_judge_regime_v4.py [out.pdf]

Same drawing as fig_judge_regime.py (band, f = 10% curve, human-audit points for the agent and Aristotle,
review points for GPT-6 Astra and Opus 5.5), plus the seven earlier one-shot systems from
analysis/review_v4.json (run analysis/review_v4.py first). Their rejections were classified by the same
two-stage review, so they are open points, and only rejected outputs were reviewed, so their e is a lower
bound (arrow to the right). The x range is extended to 100% to include them.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import fig_judge_regime as base
from fig_judge_regime import HALO, band, curve, render, share, text, y_of
from fig_main_results import GREY, GRID, INK, ORANGE, RED, RES, BLUE

HERE = Path(__file__).resolve().parent
V4 = json.loads((HERE.parent / "review_v4.json").read_text())
base.E_MAX = 1.0
x_of = base.x_of

# label text, anchor, label x, label y (pixels), arrow length (0: no room for the lower-bound arrow)
EARLIER = {"GPT-5.2": ("GPT-5.2", "start", 600, 278, 50), "Gemini-2.5-Pro": ("Gemini-2.5-Pro", "start", 425, 510, 50),
           "Herald": ("Herald", "start", 868, 168, 30), "StepFun-Formalizer": ("StepFun", "start", 790, 232, 30),
           "Kimina-Autoformalizer": (None, None, 0, 0, 0), "Kimina-Prover": (None, None, 0, 0, 0),
           "Goedel-Prover": (None, None, 0, 0, 0)}
# The three overlapping points at the top right (Goedel-Prover, Kimina-Prover, Kimina-AutoF) are named in the caption.


def point(p: list, x: float, y: float, human: bool, arrow: float) -> None:
    if not human and arrow:
        p.append(f'<line x1="{x + 16:.1f}" y1="{y:.1f}" x2="{x + 16 + arrow:.1f}" y2="{y:.1f}" stroke="{ORANGE}" stroke-width="4"/>')
        p.append(f'<path d="M{x + 28 + arrow:.1f},{y:.1f} L{x + 12 + arrow:.1f},{y - 9:.1f} L{x + 12 + arrow:.1f},{y + 9:.1f} Z" fill="{ORANGE}"/>')
    fill = ORANGE if human else "#fff"
    p.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="14" fill="{fill}" stroke="{ORANGE}" stroke-width="5"/>')


def svg() -> str:
    W, H, X0, X1, Y0, Y1 = base.W, base.H, base.X0, base.X1, base.Y0, base.Y1
    rates = RES["newer_models"]["false_rejection_rate"]
    p = [f'<rect x="12.5" y="12.5" width="{W - 25}" height="{H - 25}" rx="3" fill="#fff" stroke="{INK}" stroke-width="3"/>']
    for v in (0.25, 0.5, 0.75, 1.0):
        p.append(f'<line x1="{X0}" x2="{X1}" y1="{y_of(v)}" y2="{y_of(v)}" stroke="{GRID}" stroke-width="2.5" stroke-dasharray="7 7"/>')
    for v in (0, 0.25, 0.5, 0.75, 1.0):
        p.append(text(X0 - 16, y_of(v) + 12, f"{int(v * 100)}", 36, "serif", GREY, "end"))
    for e in (0.003, 0.01, 0.03, 0.1, 0.3, 1.0):
        x = x_of(e)
        p.append(f'<line x1="{x}" x2="{x}" y1="{Y0}" y2="{Y0 + 10}" stroke="{INK}" stroke-width="3"/>')
        p.append(text(x - (14 if e == 1.0 else 0), Y0 + 48, f"{e * 100:g}%", 36, "serif", GREY))
    p.append(f'<line x1="{X0}" x2="{X1}" y1="{Y0}" y2="{Y0}" stroke="{INK}" stroke-width="3"/>')
    p.append(f'<line x1="{X0}" x2="{X0}" y1="{Y0}" y2="{Y1}" stroke="{INK}" stroke-width="3"/>')
    p.append(text((X0 + X1) / 2, Y0 + 100, "unfaithful share of compiling outputs", 36, "serif", GREY))
    mid = (Y0 + Y1) / 2
    p.append(text(62, mid, "rejections that are real errors (%)", 36, "serif", GREY, extra=f'transform="rotate(-90 62 {mid})"'))
    p.append(band(0.02, 0.12, "#dfe8f4"))
    p.append(curve(0.10, BLUE, 6))
    p.append(text(600, 470, "f = 10%", 36, "hand", BLUE, "start", HALO))
    labels = []
    for name, (lab, anchor, lx, ly, arrow) in EARLIER.items():
        r = V4["earlier_systems"][name]
        x, y = x_of(r["unfaithful_share"]), y_of(r["real_error_share_of_rejections"])
        point(p, x, y, False, arrow)
        if lab:
            labels.append(text(lx, ly, lab, 32, "serif", INK, anchor, HALO))
    for name, key, human, anchor, lx, ly in [("GPT-5.2 agent", "GPT-5.2 agent", True, "end", 835, 125),
                                             ("Aristotle", "Aristotle", True, "end", 655, 158),
                                             ("Opus 5.5", "Claude Opus 5.5", False, "start", None, None),
                                             ("GPT-6 Astra", "GPT-6 Astra", False, "start", None, None)]:
        r = rates[key]
        x, y = x_of(r["unfaithful_share"]), y_of(r["real_error_share_of_rejections"])
        if name == "GPT-6 Astra":
            p.append(f'<line x1="{x:.1f}" y1="{y - 14:.1f}" x2="{x + 18:.1f}" y2="{y - 52:.1f}" stroke="{GREY}" stroke-width="2.5"/>')
            lx, ly = x + 22, y - 62
        if name == "Opus 5.5":
            lx, ly = x + 6, y + 54
        point(p, x, y, human, 68 if not human else 0)
        labels.append(text(lx, ly, name, 34, "serif", INK, anchor, HALO))
    p += labels
    lx, ly = X0 + 34, Y1 + 42
    p.append(f'<circle cx="{lx}" cy="{ly}" r="13" fill="{ORANGE}" stroke="{ORANGE}" stroke-width="5"/>')
    p.append(text(lx + 26, ly + 12, "human audit", 34, "hand", RED, "start"))
    p.append(f'<circle cx="{lx}" cy="{ly + 48}" r="13" fill="#fff" stroke="{ORANGE}" stroke-width="5"/>')
    p.append(text(lx + 26, ly + 60, "Opus 5.5 +", 34, "hand", RED, "start"))
    p.append(text(lx + 26, ly + 100, "GPT-6.1 Sol", 34, "hand", RED, "start"))
    return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{W / 300}in" height="{H / 300}in" '
            f'viewBox="0 0 {W} {H}">' + "".join(p) + "</svg>")


if __name__ == "__main__":
    render(svg(), Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "fig_judge_regime_v4.pdf")
