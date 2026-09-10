"""
Regenerates figures/convergence_I4.png and data/spectra/plain_sg_spectra_levels1-6.csv
from scratch, using only src/. Run from the repository root:

    python3 reproducibility/regenerate_figures.py
"""
import csv
import sys
from pathlib import Path

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))

from moments.moments import normalized_invariant_I  # noqa: E402
from operators.operators import build_plain_sg  # noqa: E402


def regenerate_figure():
    levels = list(range(1, 8))
    vals = [normalized_invariant_I(m, np.pi / 2) for m in levels]
    limit = -8 / 9

    fig, ax = plt.subplots(figsize=(7, 4.5), dpi=150)
    ax.axhline(limit, color="#d62728", linestyle="--", linewidth=1, label=r"limit $-8/9$")
    ax.plot(levels, vals, "o-", color="#1f77b4", linewidth=1.5, markersize=6, label=r"$I_m(\pi/2)$")
    ax.set_xlabel("refinement level m")
    ax.set_ylabel(r"$I_m(\pi/2)$")
    ax.set_title("Convergence of the normalized H4 invariant to -8/9")
    ax.legend()
    ax.grid(alpha=0.3)
    fig.tight_layout()
    out = ROOT / "figures" / "convergence_I4.png"
    fig.savefig(out)
    print(f"wrote {out}")


def regenerate_spectra_csv():
    out = ROOT / "data" / "spectra" / "plain_sg_spectra_levels1-6.csv"
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["level", "k", "lambda_k"])
        for level in range(1, 7):
            H, n = build_plain_sg(level)
            eigs = np.linalg.eigvalsh(H)
            eigs.sort()
            for k, val in enumerate(eigs):
                w.writerow([level, k, f"{val:.10f}"])
    print(f"wrote {out}")


if __name__ == "__main__":
    regenerate_figure()
    regenerate_spectra_csv()
