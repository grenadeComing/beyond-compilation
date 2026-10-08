"""Figure 2 (full agent with three orchestrators) in the style of Figure 1,
drawn from results_227.json and printed to PDF with headless Chrome.

    python analysis/figures/fig_multi_model.py [out.pdf]
"""

from __future__ import annotations

import sys
from pathlib import Path

from fig_main_results import (BLUE, GREY, GRID, INK, ORANGE, RED, RES, bar_path, render, text)

HERE = Path(__file__).resolve().parent

# Geometry in 300-dpi pixels; the aspect ratio matches Figure 1 (agent_logic.png).
W, H = 810, 904
Y0, PX = 816, 6.25  # baseline and pixels per percentage point
BAR, GAP = 70, 4
X0, X1 = 112, 790  # plot area
SYSTEMS = [
    ("GPT-5.2", RES["configs"]["111"], 238),
    ("Sonnet 4.5", RES["alt_orchestrators"]["Sonnet 4.5"], 451),
    ("Gemini 2.5 Pro", RES["alt_orchestrators"]["Gemini-2.5-Pro"], 664),
]


def svg() -> str:
    parts = [f'<rect x="12.5" y="12.5" width="{W - 25}" height="{H - 25}" rx="3" fill="#fff" stroke="{INK}" stroke-width="2.5"/>']
    for v in (20, 40, 60, 80, 100):
        y = Y0 - v * PX
        parts.append(f'<line x1="{X0}" x2="{X1}" y1="{y}" y2="{y}" stroke="{GRID}" stroke-width="2" stroke-dasharray="6.5 6.5"/>')
        parts.append(text(X0 - 18, y + 8.5, v, 27, "serif", GREY, "end"))
    parts.append(text(42, (Y0 + Y0 - 100 * PX) / 2, "% of statements", 27, "serif", GREY,
                      extra=f'transform="rotate(-90 42 {(Y0 + Y0 - 100 * PX) / 2})"'))
    parts.append(f'<line x1="{X0}" x2="{X1}" y1="{Y0}" y2="{Y0}" stroke="{INK}" stroke-width="2"/>')
    parts.append(f'<rect x="{X0 + 18}" y="40" width="30" height="25" rx="4" fill="{ORANGE}"/>')
    parts.append(text(X0 + 61, 63.5, "Compiles", 31.2, "serif", anchor="start"))
    parts.append(f'<rect x="{X0 + 233}" y="40" width="30" height="25" rx="4" fill="{BLUE}"/>')
    parts.append(text(X0 + 276, 63.5, "Compiles and accepted", 31.2, "serif", anchor="start"))
    parts.append(text(X0 + 18, 112, "gap = compiles minus accepted (points)", 29.7, "hand", GREY, "start"))
    for label, r, c in SYSTEMS:
        comp, faith, gap = r["compile_pct"], r["faithful_pct"], r["gap_pts"]
        xo, xb = c - GAP / 2 - BAR, c + GAP / 2
        parts += [bar_path(xo, comp, ORANGE, Y0, PX, BAR), bar_path(xb, faith, BLUE, Y0, PX, BAR)]
        parts.append(text(xo + BAR / 2, Y0 - comp * PX - 12, f"{comp:.1f}", 29, "serif"))
        parts.append(text(xb + BAR / 2, Y0 - faith * PX - 12, f"{faith:.1f}", 29, "serif"))
        parts.append(text(c, Y0 - comp * PX - 56, f"gap {gap:.1f}", 30, "hand", RED,
                          extra=f'stroke="{RED}" stroke-width="0.35"'))
        parts.append(text(c, Y0 + 44, label, 28.3, "serif"))
    return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{W / 300}in" height="{H / 300}in" '
            f'viewBox="0 0 {W} {H}">' + "".join(parts) + "</svg>")


if __name__ == "__main__":
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "multi_model_agent.pdf"
    render(svg(), W, H, out, HERE / "fig_multi_model.html")
