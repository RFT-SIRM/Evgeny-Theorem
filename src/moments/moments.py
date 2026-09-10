"""
Spectral observables used throughout this repository, plus the closed-form
expression for the fourth-moment invariant (Evgeny's Theorem, see
THEOREM.md) and the raw-trace helper used to verify it directly.
"""
from typing import Dict

import numpy as np

from operators.operators import build_su2_bundle


def normalized_moment(H: np.ndarray, dim: int, p: int) -> float:
    """M_p = tr(H^p) / dim, computed by repeated matrix multiplication
    (no eigendecomposition needed -- this is what makes level 7 tractable).

    Entries of H are provably bounded (vertex degree <= 4, off-diagonal
    blocks are unit-norm SU(2) rotations), so ||H|| is bounded by a small
    constant and no floating-point overflow is mathematically possible at
    the small powers (p<=6) used in this repository. Some numpy/BLAS
    backends (observed with numpy>=2.5 on Apple Silicon) emit spurious
    RuntimeWarnings ("overflow", "invalid value", "divide by zero") during
    complex matmul dispatch despite correct results; these are suppressed
    here explicitly rather than silently, and are unrelated to correctness,
    which is independently checked against closed-form and held-out values
    throughout tests/.
    """
    with np.errstate(over="ignore", invalid="ignore", divide="ignore"):
        Hp = np.eye(dim, dtype=complex)
        for _ in range(p):
            Hp = Hp @ H
        return float(np.real(np.trace(Hp)) / dim)


def raw_trace(H: np.ndarray, dim: int, p: int) -> float:
    """tr(H^p), unnormalized. See normalized_moment() for the note on
    why floating-point overflow is not possible here and why any
    RuntimeWarning from the underlying BLAS backend is spurious."""
    with np.errstate(over="ignore", invalid="ignore", divide="ignore"):
        Hp = np.eye(dim, dtype=complex)
        for _ in range(p):
            Hp = Hp @ H
        return float(np.real(np.trace(Hp)))


def heat_trace(eigenvalues: np.ndarray, t: float) -> float:
    """Z(t) = tr(exp(-t H)) from an eigenvalue array."""
    return float(np.sum(np.exp(-t * eigenvalues)))


def counting_function(eigenvalues: np.ndarray, lam: float) -> int:
    """N(lambda) = number of eigenvalues strictly below lambda."""
    return int(np.sum(eigenvalues < lam))


def raw_trace_diff_H4(level: int, theta: float) -> float:
    """Delta_m(H^4, theta) = tr(H_C^4) - tr(H_C'^4), computed directly
    (no formula used) -- the quantity Evgeny's Theorem gives a closed
    form for."""
    HC, n = build_su2_bundle(level, theta, commuting=False)
    HCp, _ = build_su2_bundle(level, theta, commuting=True)
    dim = 2 * n
    return raw_trace(HC, dim, 4) - raw_trace(HCp, dim, 4)


def evgeny_theorem_H4(level: int, theta: float) -> float:
    """
    Closed-form prediction of Delta_m(H^4, theta) (raw, unnormalized):

        Delta_m(H^4, theta) = -16 * (3^(m-1) + 1) * sin^2(theta/2)

    See THEOREM.md and DERIVATION.md for the statement and its supporting
    path-class argument, and tests/test_theta.py /
    tests/test_heldout.py for independent numerical verification.
    """
    return -16.0 * (3 ** (level - 1) + 1) * np.sin(theta / 2) ** 2


def normalized_invariant_I(level: int, theta: float) -> float:
    """
    I_m(theta) = Delta_m(H^4, theta) / dim(H),  dim(H) = 3^(m+1) + 3.

    At theta = pi/2, I_m(pi/2) -> -8/9 as m -> infinity (see VERIFICATION.md).
    """
    dim = 3 ** (level + 1) + 3
    return evgeny_theorem_H4(level, theta) / dim


def full_audit(H: np.ndarray, dim: int) -> Dict:
    """Convenience bundle of observables for a given operator, used by
    the reproducibility scripts (not required by the core theorem)."""
    w = np.linalg.eigvalsh(H)
    w.sort()
    return {
        "eigenvalues_first20": w[:20],
        "gap": w[1] if len(w) > 1 else float("nan"),
        "moments": {p: normalized_moment(H, dim, p) for p in (1, 2, 3, 4)},
        "heat_trace": {t: heat_trace(w, t) for t in (0.5, 1, 2, 5)},
        "counting_function": {lam: counting_function(w, lam) for lam in (0.1, 0.5, 1, 2)},
    }
