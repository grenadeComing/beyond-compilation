"""GPT-5.2 vs. Gemini-2.5-Pro disagreement by domain, in the style of Figure 1,
drawn from analysis/results.json and printed to PDF with headless Chrome.

    python analysis/figures/fig_disagreement.py [out.pdf]
"""

from __future__ import annotations

import sys
from pathlib import Path

from fig_main_results import BLUE, GREY, GRID, INK, RED, RES, bar_path, render, text

HERE = Path(__file__).resolve().parent
N_SYSTEMS = 10  # Herald, GPT-5.2 and Gemini-2.5-Pro one-shot, seven agent configurations

W, H = 1050, 640
Y0, PX = 520, 24.0  # baseline and pixels per percentage point (axis 0-15%)
BAR = 120
X0, X1 = 130, 1020
ORDER = ("Real Analysis", "Complex Analysis", "Algebra", "Topology")


def svg() -> str:
    counts = RES["judge_disagreement_by_domain"]
    parts = [f'<rect x="12.5" y="12.5" width="{W - 25}" height="{H - 25}" rx="3" fill="#fff" stroke="{INK}" stroke-width="2.5"/>']
    for v in (5, 10, 15):
        y = Y0 - v * PX
        parts.append(f'<line x1="{X0}" x2="{X1}" y1="{y}" y2="{y}" stroke="{GRID}" stroke-width="2" stroke-dasharray="6.5 6.5"/>')
        parts.append(text(X0 - 18, y + 8.5, v, 27, "serif", GREY, "end"))
    mid = (Y0 + Y0 - 15 * PX) / 2
    parts.append(text(48, mid, "% of outputs", 27, "serif", GREY, extra=f'transform="rotate(-90 48 {mid})"'))
    parts.append(f'<line x1="{X0}" x2="{X1}" y1="{Y0}" y2="{Y0}" stroke="{INK}" stroke-width="2"/>')
    parts.append(text(X0 + 10, 66, "GPT-5.2 and Gemini-2.5-Pro disagree",
                      29.7, "hand", GREY, "start"))
    step = (X1 - X0) / len(ORDER)
    for j, d in enumerate(ORDER):
        n = RES["domain"][d]["n"] * N_SYSTEMS
        k = counts.get(d, 0)
        r = 100 * k / n
        c = X0 + step * (j + 0.5)
        parts.append(bar_path(c - BAR / 2, r, BLUE, Y0, PX, BAR))
        parts.append(text(c, Y0 - r * PX - 12, f"{r:.1f}", 29, "serif"))
        parts.append(text(c, Y0 - r * PX - 50, f"{k} of {n}", 30, "hand", RED,
                          extra=f'stroke="{RED}" stroke-width="0.35"'))
        parts.append(text(c, Y0 + 40, d, 28.3, "serif"))
        parts.append(text(c, Y0 + 73, f"({RES['domain'][d]['n']} statements)", 25, "serif", GREY))
    return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{W / 300}in" height="{H / 300}in" '
            f'viewBox="0 0 {W} {H}">' + "".join(parts) + "</svg>")


if __name__ == "__main__":
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "overall_domain_disagreement.pdf"
    render(svg(), W, H, out, HERE / "fig_disagreement.html")
