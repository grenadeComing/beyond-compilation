"""Figure 1 (validity vs. semantic faithfulness) in the style of the MATH-AI 2026
version, drawn from results_227.json and printed to PDF with headless Chrome.

    python analysis/figures/fig_main_results.py [out.pdf]
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
RES = json.loads((HERE.parent / "results.json").read_text())
CHROME = os.environ.get("CHROME", "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")

# Geometry in 300-dpi pixels of a 5.5 in x 2.86 in figure.
W, H = 1650, 858.4
Y0, PX = 647.5, 4.96  # baseline and pixels per percentage point
BAR, GAP = 56, 3.5
ORANGE, BLUE, INK, GREY, GRID, GROUP, RED = (
    "#eb6834", "#2a78d6", "#1e1e1e", "#52514e", "#e4e3df", "#1557a0", "#b3261e")

SYSTEMS = [  # (key in results, label lines, pair centre)
    ("Kimina Prover", ("Kimina", "Prover"), 212.5),
    ("Goedel Prover", ("Goedel", "Prover"), 381),
    ("Kimina AutoF", ("Kimina", "AutoF"), 592),
    ("Herald", ("Herald",), 760.5),
    ("StepFun", ("StepFun",), 928.5),
    ("GPT-5.2", ("GPT-5.2",), 1140),
    ("Gemini-2.5-Pro", ("Gemini", "2.5 Pro"), 1308),
    ("GPT-5.2 agent", ("GPT-5.2", "agent"), 1519.5),
]
GROUPS = [("Provers", 141, 452), ("Formalizers", 522, 999),
          ("General LLMs", 1068, 1379), ("Our agent", 1448, 1591)]


def bar_path(x: float, v: float, color: str, y0: float, px: float, w: float) -> str:
    y, r = y0 - v * px, 4
    return (f'<path d="M{x},{y0} V{y + r} Q{x},{y} {x + r},{y} H{x + w - r} '
            f'Q{x + w},{y} {x + w},{y + r} V{y0} Z" fill="{color}"/>')


def bar(x: float, v: float, color: str) -> str:
    return bar_path(x, v, color, Y0, PX, BAR)


def text(x, y, s, size, font, color=INK, anchor="middle", weight=400, extra=""):
    fam = "Excalifont" if font == "hand" else "TeX Gyre Termes"
    return (f'<text x="{x}" y="{y}" font-family="{fam}" font-size="{size}" font-weight="{weight}" '
            f'fill="{color}" text-anchor="{anchor}" {extra}>{s}</text>')


def svg() -> str:
    n = RES["n"]
    parts = [f'<rect x="12.5" y="12.5" width="1624" height="833" rx="3" fill="#fff" stroke="{INK}" stroke-width="2.5"/>']
    for v in (20, 40, 60, 80, 100):
        y = Y0 - v * PX
        parts.append(f'<line x1="129" x2="1603" y1="{y}" y2="{y}" stroke="{GRID}" stroke-width="2" stroke-dasharray="6.5 6.5"/>')
        parts.append(text(110, y + 8.5, v, 27, "serif", GREY, "end"))
    parts.append(text(48, 398.5, "% of statements", 27, "serif", GREY,
                      extra='transform="rotate(-90 48 398.5)"'))
    parts.append(f'<line x1="129" x2="1603" y1="{Y0}" y2="{Y0}" stroke="{INK}" stroke-width="2"/>')
    # Legend and note.
    parts.append(f'<rect x="152" y="73" width="30" height="25" rx="4" fill="{ORANGE}"/>')
    parts.append(text(195, 96.5, "Compiles", 31.2, "serif", anchor="start"))
    parts.append(f'<rect x="367" y="73" width="30" height="25" rx="4" fill="{BLUE}"/>')
    parts.append(text(410, 96.5, "Compiles and faithful", 31.2, "serif", anchor="start"))
    parts.append(text(1601, 96, "gap = compiles minus faithful (points)", 29.7, "hand", GREY, "end"))
    for key, label, c in SYSTEMS:
        r = RES["figure1"][key]
        comp, faith, gap = r["compile_pct"], r["faithful_pct"], r["gap_pts"]
        xo, xb = c - GAP / 2 - BAR, c + GAP / 2
        parts += [bar(xo, comp, ORANGE), bar(xb, faith, BLUE)]
        parts.append(text(xo + BAR / 2, Y0 - comp * PX - 12, f"{comp:.1f}", 29, "serif"))
        parts.append(text(xb + BAR / 2, Y0 - faith * PX - 12, f"{faith:.1f}", 29, "serif"))
        color = RED
        parts.append(text(c, Y0 - comp * PX - 56, f"gap {gap:.1f}", 30, "hand", color,
                          extra=f'stroke="{color}" stroke-width="0.35"'))
        for i, line in enumerate(label):
            parts.append(text(c, 688.5 + 33 * i, line, 28.3, "serif"))
    for name, x0, x1 in GROUPS:
        r = 11
        parts.append(f'<path d="M{x0},{741} Q{x0},{752} {x0 + r},{752} H{x1 - r} Q{x1},{752} {x1},{741}" '
                     f'fill="none" stroke="{GROUP}" stroke-width="2.5" stroke-linecap="round"/>')
        parts.append(text((x0 + x1) / 2, 794, name, 33, "hand", GROUP))
    return (f'<svg xmlns="http://www.w3.org/2000/svg" width="5.5in" height="{H / 300}in" '
            f'viewBox="0 0 {W} {H}">' + "".join(parts) + "</svg>")


def render(svg_text: str, w: float, h: float, out: Path, page: Path) -> None:
    """Print an SVG to a PDF page of the same size with headless Chrome."""
    fonts = HERE / "fonts"
    html = f"""<!doctype html><html><head><meta charset="utf-8"><style>
@font-face {{ font-family: "Excalifont"; src: url("{(fonts / 'Excalifont-Latin.ttf').as_uri()}"); }}
@font-face {{ font-family: "TeX Gyre Termes"; src: url("{(fonts / 'texgyretermes-regular.otf').as_uri()}"); }}
@page {{ size: {w / 300}in {h / 300}in; margin: 0; }}
html, body {{ margin: 0; padding: 0; }} svg {{ display: block; }}
</style></head><body>{svg_text}</body></html>"""
    page.write_text(html)
    subprocess.run([CHROME, "--headless=new", "--disable-gpu", "--no-pdf-header-footer",
                    "--allow-file-access-from-files", "--virtual-time-budget=5000",
                    f"--print-to-pdf={out}", page.as_uri()], check=True, capture_output=True)
    print(f"wrote {out}")


def main() -> None:
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "fig_main_results.pdf"
    render(svg(), W, H, out, HERE / "fig_main_results.html")


if __name__ == "__main__":
    main()
