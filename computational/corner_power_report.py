#!/usr/bin/env python3
"""Report vertex-corner blocks of powers of the level-m SU(2) SG operator.

Numerical diagnostic only; this is not a certificate for Lean's glued-state
corner hypotheses. Run from the repository root:
  PYTHONPATH=src python computational/corner_power_report.py --level 3
"""
import argparse
import json
import numpy as np
from graph.sg_graph import sg_tree_graph_with_faces
from operators.operators import build_su2_bundle


def _complex(z, digits=12):
    re = 0.0 if abs(z.real) < 10 ** (-digits) else round(float(z.real), digits)
    im = 0.0 if abs(z.imag) < 10 ** (-digits) else round(float(z.imag), digits)
    return {"re": re, "im": im}


def report(level, theta, commuting, max_power):
    vertices, _, _ = sg_tree_graph_with_faces(level)
    corners = [(0.0, 0.0), (1.0, 0.0), (0.0, 1.0)]
    indices = [vertices.index(point) for point in corners]
    H, n_vertices = build_su2_bundle(level, theta, commuting=commuting)
    power_matrix = np.eye(H.shape[0], dtype=complex)
    powers = []
    for p in range(1, max_power + 1):
        power_matrix = power_matrix @ H
        blocks = []
        same_corner_spin = []
        for i, source in enumerate(corners):
            diagonal_block = power_matrix[2*indices[i]:2*indices[i]+2,
                                          2*indices[i]:2*indices[i]+2]
            same_corner_spin.append({
                "corner": list(source),
                "spin_offdiag": _complex(diagonal_block[0, 1]),
                "spin_offdiag_abs": float(abs(diagonal_block[0, 1])),
            })
            for j, target in enumerate(corners):
                if i == j:
                    continue
                block = power_matrix[2*indices[i]:2*indices[i]+2,
                                     2*indices[j]:2*indices[j]+2]
                blocks.append({
                    "from": list(source), "to": list(target),
                    "max_abs": float(np.max(np.abs(block))),
                    "entries": [[_complex(z) for z in row] for row in block],
                })
        powers.append({
            "power": p,
            "corner_blocks": blocks,
            "same_corner_spin_offdiag": same_corner_spin,
        })
    return {
        "purpose": "Python vertex-corner diagnostic only; not a Lean proof",
        "level": level, "theta": theta, "commuting": commuting,
        "graph_vertices": n_vertices, "operator_dimension": int(H.shape[0]),
        "corner_coordinates": [list(p) for p in corners],
        "corner_vertex_indices": indices, "powers": powers,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--level", type=int, default=3)
    parser.add_argument("--theta", type=float, default=float(np.pi / 2))
    parser.add_argument("--commuting", action="store_true")
    parser.add_argument("--max-power", type=int, default=9)
    parser.add_argument("--output", default="-")
    args = parser.parse_args()
    if args.level < 0 or args.max_power < 1:
        parser.error("--level must be nonnegative and --max-power positive")
    result = json.dumps(report(args.level, args.theta, args.commuting, args.max_power),
                        indent=2, sort_keys=True)
    if args.output == "-":
        print(result)
    else:
        with open(args.output, "w", encoding="utf-8") as stream:
            stream.write(result + "\n")


if __name__ == "__main__":
    main()
