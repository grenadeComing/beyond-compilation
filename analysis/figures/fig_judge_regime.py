"""Share of a judge's rejections that are real errors, against how often a system errs, in the style of
Figure 1, from analysis/results.json; printed to PDF with headless Chrome.

    python analysis/figures/fig_judge_regime.py [out.pdf]

If a judge rejects a fraction f of faithful compiling outputs and accepts a fraction m of unfaithful ones,
a system whose compiling outputs are unfaithful at rate e has a share e(1-m) / (e(1-m) + (1-e) f) of
rejections that are real errors. The band spans f = 2% to 12%, the range measured on the four systems,
and the solid curve is f = 10%, all with m = 10%; acceptance is by GPT-5.2 alone. Points are the systems (filled: human audit; open: review by Claude Opus 5.5 and GPT-6.1 Sol, where e counts errors among
rejected outputs only). All text is bold so that it stays legible at column width.
"""

from __future__ import annotations

import math
import subprocess
import sys
from pathlib import Path

from fig_main_results import BLUE, CHROME, GREY, GRID, INK, ORANGE, RED, RES

HERE = Path(__file__).resolve().parent
W, H = 1000, 820
X0, X1, Y0, Y1 = 185, 960, 660, 60       # plot box in pixels (y grows downwards)
E_MIN, E_MAX = 0.003, 0.5                # log-scaled x range
M = 0.10
HALO = 'stroke="#fff" stroke-width="9" stroke-linejoin="round" paint-order="stroke"'


def x_of(e: float) -> float:
    return X0 + (math.log10(e) - math.log10(E_MIN)) / (math.log10(E_MAX) - math.log10(E_MIN)) * (X1 - X0)


def y_of(s: float) -> float:
    return Y0 - s * (Y0 - Y1)


def share(e: float, f: float) -> float:
    return e * (1 - M) / (e * (1 - M) + (1 - e) * f)


def text(x, y, s, size, font="serif", color=INK, anchor="middle", extra=""):
    fam = "Excalifont" if font == "hand" else "TeX Gyre Termes"
    return (f'<text x="{x:.1f}" y="{y:.1f}" font-family="{fam}" font-size="{size}" font-weight="700" '
            f'fill="{color}" text-anchor="{anchor}" {extra}>{s}</text>')


def points(f: float, n: int = 200) -> list[str]:
    out = []
    for i in range(n + 1):
        e = 10 ** (math.log10(E_MIN) + i / n * (math.log10(E_MAX) - math.log10(E_MIN)))
        out.append(f"{x_of(e):.1f},{y_of(share(e, f)):.1f}")
    return out


def curve(f: float, color: str, width: float) -> str:
    return f'<polyline points="{" ".join(points(f))}" fill="none" stroke="{color}" stroke-width="{width}"/>'


def band(f_lo: float, f_hi: float, color: str) -> str:
    # the upper edge is the lower false-rejection rate
    return f'<polygon points="{" ".join(points(f_lo) + points(f_hi)[::-1])}" fill="{color}" stroke="none"/>'


def svg() -> str:
    rates = RES["newer_models"]["false_rejection_rate"]
    p = [f'<rect x="12.5" y="12.5" width="{W - 25}" height="{H - 25}" rx="3" fill="#fff" stroke="{INK}" stroke-width="3"/>']
    for v in (0.25, 0.5, 0.75, 1.0):
        y = y_of(v)
        p.append(f'<line x1="{X0}" x2="{X1}" y1="{y}" y2="{y}" stroke="{GRID}" stroke-width="2.5" stroke-dasharray="7 7"/>')
    for v in (0, 0.25, 0.5, 0.75, 1.0):
        p.append(text(X0 - 16, y_of(v) + 12, f"{int(v * 100)}", 36, "serif", GREY, "end"))
    for e in (0.003, 0.01, 0.03, 0.1, 0.3):
        x = x_of(e)
        p.append(f'<line x1="{x}" x2="{x}" y1="{Y0}" y2="{Y0 + 10}" stroke="{INK}" stroke-width="3"/>')
        p.append(text(x, Y0 + 48, f"{e * 100:g}%", 36, "serif", GREY))
    p.append(f'<line x1="{X0}" x2="{X1}" y1="{Y0}" y2="{Y0}" stroke="{INK}" stroke-width="3"/>')
    p.append(f'<line x1="{X0}" x2="{X0}" y1="{Y0}" y2="{Y1}" stroke="{INK}" stroke-width="3"/>')
    p.append(text((X0 + X1) / 2, Y0 + 100, "unfaithful share of compiling outputs", 36, "serif", GREY))
    mid = (Y0 + Y1) / 2
    p.append(text(62, mid, "rejections that are real errors (%)", 36, "serif", GREY,
                  extra=f'transform="rotate(-90 62 {mid})"'))
    p.append(band(0.02, 0.12, "#dfe8f4"))
    p.append(curve(0.10, BLUE, 6))
    p.append(text(x_of(0.04) - 10, y_of(share(0.04, 0.10)) - 30, "f = 10%", 36, "hand", BLUE, "end", HALO))
    pts = [("GPT-5.2 agent", rates["GPT-5.2 agent"], True, "end", -26, -14),
           ("Aristotle", rates["Aristotle"], True, "end", -24, 14),
           ("Opus 5.5", rates["Claude Opus 5.5"], False, "start", 26, 12),
           ("GPT-6 Astra", rates["GPT-6 Astra"], False, "start", 22, -62)]
    for name, r, human, anchor, dx, dy in pts:
        x, y = x_of(r["unfaithful_share"]), y_of(r["real_error_share_of_rejections"])
        if name == "GPT-6 Astra":
            p.append(f'<line x1="{x:.1f}" y1="{y - 14:.1f}" x2="{x + 18:.1f}" y2="{y + dy + 10:.1f}" stroke="{GREY}" stroke-width="2.5"/>')
        fill = ORANGE if human else "#fff"
        p.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="14" fill="{fill}" stroke="{ORANGE}" stroke-width="5"/>')
        p.append(text(x + dx, y + dy, name, 38, "serif", INK, anchor, HALO))
    lx, ly = X0 + 34, Y1 + 42
    p.append(f'<circle cx="{lx}" cy="{ly}" r="13" fill="{ORANGE}" stroke="{ORANGE}" stroke-width="5"/>')
    p.append(text(lx + 26, ly + 12, "human audit", 34, "hand", RED, "start"))
    p.append(f'<circle cx="{lx}" cy="{ly + 48}" r="13" fill="#fff" stroke="{ORANGE}" stroke-width="5"/>')
    p.append(text(lx + 26, ly + 60, "Opus 5.5 +", 34, "hand", RED, "start"))
    p.append(text(lx + 26, ly + 100, "GPT-6.1 Sol", 34, "hand", RED, "start"))
    return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{W / 300}in" height="{H / 300}in" '
            f'viewBox="0 0 {W} {H}">' + "".join(p) + "</svg>")


def render(svg_text: str, out: Path) -> None:
    """Like fig_main_results.render, but also loads the bold face of TeX Gyre Termes."""
    fonts = HERE / "fonts"
    page = HERE / "fig_judge_regime.html"
    page.write_text(f"""<!doctype html><html><head><meta charset="utf-8"><style>
@font-face {{ font-family: "Excalifont"; src: url("{(fonts / 'Excalifont-Latin.ttf').as_uri()}"); }}
@font-face {{ font-family: "TeX Gyre Termes"; src: url("{(fonts / 'texgyretermes-regular.otf').as_uri()}"); font-weight: 400; }}
@font-face {{ font-family: "TeX Gyre Termes"; src: url("{(fonts / 'texgyretermes-bold.otf').as_uri()}"); font-weight: 700; }}
@page {{ size: {W / 300}in {H / 300}in; margin: 0; }}
html, body {{ margin: 0; padding: 0; }} svg {{ display: block; }}
</style></head><body>{svg_text}</body></html>""")
    subprocess.run([CHROME, "--headless=new", "--disable-gpu", "--no-pdf-header-footer",
                    "--allow-file-access-from-files", "--virtual-time-budget=5000",
                    f"--print-to-pdf={out}", page.as_uri()], check=True, capture_output=True)
    page.unlink()
    print(f"wrote {out}")


if __name__ == "__main__":
    render(svg(), Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "fig_judge_regime.pdf")
