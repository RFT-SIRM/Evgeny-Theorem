"""
Three operator families on the SG graph, all sharing one convention:
flux (Abelian or non-Abelian) is injected through exactly one designated
edge per elementary (leaf) triangle.

    A: build_plain_sg        -- ordinary combinatorial Laplacian, no flux
    B: build_u1_magnetic     -- scalar U(1) phase e^{i theta} on flux edges
    C: build_su2_bundle      -- SU(2)-valued connection on flux edges

For C, `commuting=True` fixes the rotation axis to z for every triangle
(all edge matrices commute -> exactly equivalent to two decoupled U(1)
copies at flux +-theta/2). `commuting=False` cycles the axis x/y/z by
triangle index mod 3, which is verified (tests/test_gauge_invariance.py
and the derivation notes) to produce genuinely non-commuting holonomy.
"""
from typing import Tuple

import numpy as np

from graph.sg_graph import sg_tree_graph_with_faces
from su2.su2_utils import I2, su2_rotation


def _degrees(n: int, E) -> np.ndarray:
    deg = np.zeros(n)
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    return deg


def build_plain_sg(level: int) -> Tuple[np.ndarray, int]:
    """Ordinary combinatorial SG Laplacian L = D - A. Returns (H, n)."""
    V, E, _ = sg_tree_graph_with_faces(level)
    n = len(V)
    A = np.zeros((n, n))
    for a, b in E:
        A[a, b] = 1
        A[b, a] = 1
    D = np.diag(A.sum(axis=1))
    return D - A, n


def build_u1_magnetic(level: int, theta: float) -> Tuple[np.ndarray, int]:
    """U(1)-magnetic SG Laplacian, scalar phase e^{i theta} on flux edges."""
    V, E, faces = sg_tree_graph_with_faces(level)
    n = len(V)
    phase_of = {tuple(sorted(e)): 1.0 + 0j for e in E}
    for a, b, _c in faces:
        phase_of[tuple(sorted((a, b)))] = np.exp(1j * theta)

    deg = _degrees(n, E)
    H = np.zeros((n, n), dtype=complex)
    for x in range(n):
        H[x, x] = deg[x]
    for e in E:
        a, b = tuple(sorted(e))
        ph = phase_of[(a, b)]
        H[a, b] += -ph
        H[b, a] += -np.conj(ph)
    return (H + H.conj().T) / 2, n


def build_su2_bundle(
    level: int, theta: float, commuting: bool = False, gauge=None
) -> Tuple[np.ndarray, int]:
    """
    SU(2)-bundle Laplacian over SG. Hilbert space is C^n (x) C^2.

    Parameters
    ----------
    commuting : if True, all flux-edge rotations use the same (z) axis,
                giving a connection with abelian (commuting) holonomy.
                If False, axis cycles x/y/z by triangle index mod 3.
    gauge     : optional list of n SU(2) matrices (one per vertex); if
                given, edge matrices are transformed as
                U'(a,b) = gauge[a] . U(a,b) . gauge[b]^dagger
                (used only to test gauge invariance).
    """
    V, E, faces = sg_tree_graph_with_faces(level)
    n = len(V)
    deg = _degrees(n, E)

    U_of = {tuple(sorted(e)): I2 for e in E}
    for i, (a, b, _c) in enumerate(faces):
        axis = 2 if commuting else (i % 3)
        U_of[tuple(sorted((a, b)))] = su2_rotation(axis, theta)

    if gauge is not None:
        for e in E:
            a, b = tuple(sorted(e))
            U_of[(a, b)] = gauge[a] @ U_of[(a, b)] @ gauge[b].conj().T

    dim = 2 * n
    H = np.zeros((dim, dim), dtype=complex)
    for x in range(n):
        H[2 * x : 2 * x + 2, 2 * x : 2 * x + 2] = deg[x] * I2
    for e in E:
        a, b = tuple(sorted(e))
        U = U_of[(a, b)]
        H[2 * a : 2 * a + 2, 2 * b : 2 * b + 2] += -U
        H[2 * b : 2 * b + 2, 2 * a : 2 * a + 2] += -U.conj().T

    return (H + H.conj().T) / 2, n
