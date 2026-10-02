"""Appendix figures for v3 from results_227.json (needs matplotlib).

    python analysis/figures/appendix_figs.py [output dir]

Writes heatmap.pdf and overall_domain_disagreement.pdf.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

HERE = Path(__file__).resolve().parent
RES = json.loads((HERE.parent / "results.json").read_text())
DOMAINS = ("Algebra", "Complex Analysis", "Real Analysis", "Topology")
CONFIGS = ("001", "010", "011", "100", "101", "110", "111")
N_DISAGREE_SYSTEMS = 10  # Herald, GPT-5.2 and Gemini one-shot, seven agent configs


def heatmap(out: Path) -> None:
    dom = RES["domain"]
    m = np.array([[dom[d]["faithful_rate_by_config"][c] for c in CONFIGS] for d in DOMAINS])
    fig, ax = plt.subplots(figsize=(10, 6))
    im = ax.imshow(m, cmap="viridis", aspect="auto")
    for i in range(len(DOMAINS)):
        for j in range(len(CONFIGS)):
            ax.text(j, i, f"{m[i, j]:.2f}", ha="center", va="center", color="white",
                    fontsize=13, fontweight="bold")
    ax.set_xticks(range(len(CONFIGS)), CONFIGS, fontsize=12, fontweight="bold")
    ax.set_yticks(range(len(DOMAINS)), [f"{d}\n($n={dom[d]['n']}$)" for d in DOMAINS], fontsize=12, fontweight="bold")
    ax.set_xlabel("Tool configuration (T, F, S)", fontsize=12, fontweight="bold")
    ax.set_xticks(np.arange(-0.5, len(CONFIGS)), minor=True)
    ax.set_yticks(np.arange(-0.5, len(DOMAINS)), minor=True)
    ax.grid(which="minor", color="white", linewidth=1)
    ax.tick_params(which="minor", length=0)
    fig.colorbar(im, ax=ax, label="Faithful rate")
    fig.tight_layout()
    fig.savefig(out / "heatmap.pdf")
    plt.close(fig)


def disagreement(out: Path) -> None:
    counts = RES["judge_disagreement_by_domain"]
    n = {d: RES["domain"][d]["n"] * N_DISAGREE_SYSTEMS for d in DOMAINS}
    rates = [100 * counts.get(d, 0) / n[d] for d in DOMAINS]
    fig, ax = plt.subplots(figsize=(4.37, 3.36))
    bars = ax.bar(range(len(DOMAINS)), rates, width=0.6, color="#1f77b4")
    for b, d in zip(bars, DOMAINS):
        ax.text(b.get_x() + b.get_width() / 2, b.get_height() + 0.2,
                f"{counts.get(d, 0)}/{n[d]}", ha="center", va="bottom", fontsize=7)
    ax.set_xticks(range(len(DOMAINS)), DOMAINS, rotation=15, fontsize=8)
    ax.set_ylabel("Disagreements (% of outputs)", fontsize=8)
    ax.set_ylim(0, max(rates) * 1.25)
    ax.tick_params(axis="y", labelsize=8)
    ax.set_title("GPT--Gemini Disagreement by Domain".replace("--", "–"), fontsize=10)
    fig.tight_layout()
    fig.savefig(out / "overall_domain_disagreement.pdf")
    plt.close(fig)


def main() -> None:
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    heatmap(out)
    disagreement(out)
    print(f"wrote figures to {out}")


if __name__ == "__main__":
    main()
