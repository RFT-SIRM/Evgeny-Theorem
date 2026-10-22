#!/usr/bin/env python3
"""Finite-level trace-defect regression at theta=pi using sparse matrix powers.

At theta=pi the SU(2) edge rotations are Gaussian-integer matrices. Sparse
multiplication keeps level 6 practical; all reported traces are checked to be
integer-valued and within the exactly representable integer range of float64.
This is a finite-level certificate, not an all-level proof.
"""
from __future__ import annotations

import numpy as np
from scipy.sparse import lil_matrix

from graph.sg_graph import sg_tree_graph_with_faces


I2 = np.array([[1, 0], [0, 1]], dtype=complex)
PAULI = (
    np.array([[0, 1], [1, 0]], dtype=complex),
    np.array([[0, -1j], [1j, 0]], dtype=complex),
    np.array([[1, 0], [0, -1]], dtype=complex),
)


def operator_at_pi(level: int, commuting: bool):
    """Build the repository's SU(2) operator as a sparse matrix."""
    vertices, edges, faces = sg_tree_graph_with_faces(level)
    n = len(vertices)
    degree = [0] * n
    for a, b in edges:
        degree[a] += 1
        degree[b] += 1

    edge_rotation = {tuple(sorted(e)): I2 for e in edges}
    for i, (a, b, _c) in enumerate(faces):
        axis = 2 if commuting else i % 3
        edge_rotation[tuple(sorted((a, b)))] = -1j * PAULI[axis]

    H = lil_matrix((2 * n, 2 * n), dtype=complex)
    for v, d in enumerate(degree):
        H[2*v:2*v+2, 2*v:2*v+2] = d * I2
    for a, b in edges:
        a, b = sorted((a, b))
        U = edge_rotation[(a, b)]
        H[2*a:2*a+2, 2*b:2*b+2] += -U
        H[2*b:2*b+2, 2*a:2*a+2] += -U.conj().T
    return H.tocsr()


def raw_trace_at_pi(level: int, power: int, commuting: bool) -> int:
    """Return Tr(H^power), validating integer-valued sparse arithmetic."""
    if power < 1:
        raise ValueError("power must be positive")
    H = operator_at_pi(level, commuting)
    Hp = H.copy()
    for _ in range(1, power):
        Hp = Hp @ H
        Hp.eliminate_zeros()
    tr = Hp.diagonal().sum()
    nearest = round(float(tr.real))
    if (abs(float(tr.imag)) > 0 or float(tr.real) != nearest
            or abs(nearest) >= 2**53):
        raise ArithmeticError(
            f"trace not safely integral at level={level}, p={power}: {tr}"
        )
    return int(nearest)


def delta_at_pi(level: int, power: int) -> int:
    return raw_trace_at_pi(level, power, False) - raw_trace_at_pi(level, power, True)


def residual_at_pi(level: int, power: int) -> int:
    if level < 2:
        raise ValueError("residual requires level >= 2")
    return delta_at_pi(level, power) - 3 * delta_at_pi(level - 1, power)


def certificate() -> dict[int, dict[str, list[int]]]:
    """Finite-level regression for p=6,8,10 and levels 1..6."""
    result = {}
    for p in (6, 8, 10):
        deltas = [delta_at_pi(m, p) for m in range(1, 7)]
        residuals = [deltas[m - 1] - 3 * deltas[m - 2] for m in range(2, 7)]
        result[p] = {
            "delta_levels_1_to_6": deltas,
            "residual_levels_2_to_6": residuals,
        }
    return result


if __name__ == "__main__":
    import json
    print(json.dumps(certificate(), indent=2))
