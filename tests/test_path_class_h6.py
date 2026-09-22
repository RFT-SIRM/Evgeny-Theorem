"""
tests/test_path_class_h6.py

H6 path-class structural results.

STATUS: COMPUTATIONAL / RESEARCH RESULTS
Reproducible numerical evidence for the H6 growth law, recurrence,
and path-class zero theorem. Not a machine-checked closed-form theorem.
"""

import sys, os
import numpy as np
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))
from operators.operators import build_su2_bundle


def _delta(level, power, theta):
    HC,  _ = build_su2_bundle(level, theta, commuting=False)
    HCp, _ = build_su2_bundle(level, theta, commuting=True)
    eC  = np.linalg.eigvalsh(HC)
    eCp = np.linalg.eigvalsh(HCp)
    return float(np.sum(eC ** power) - np.sum(eCp ** power))


def _recurrence_constant(theta):
    return _delta(4, 6, theta) - 3 * _delta(3, 6, theta)


def _triangle_delta_h6(axis_C, axis_Cp, theta):
    I2 = np.eye(2, dtype=complex)
    pauli = [
        np.array([[0,  1  ], [1,   0]], dtype=complex),
        np.array([[0, -1j ], [1j,  0]], dtype=complex),
        np.array([[1,  0  ], [0,  -1]], dtype=complex),
    ]
    c, s = np.cos(theta / 2), np.sin(theta / 2)
    def _build(ax):
        R = c * I2 + 1j * s * pauli[ax]
        H = np.zeros((6, 6), dtype=complex)
        for v in range(3):
            H[2*v:2*v+2, 2*v:2*v+2] = 2 * I2
        for a, b in [(0, 1), (1, 2), (0, 2)]:
            H[2*a:2*a+2, 2*b:2*b+2] = -R
            H[2*b:2*b+2, 2*a:2*a+2] = -R.conj().T
        return (H + H.conj().T) / 2
    eC  = np.linalg.eigvalsh(_build(axis_C))
    eCp = np.linalg.eigvalsh(_build(axis_Cp))
    return float(np.sum(eC ** 6) - np.sum(eCp ** 6))


class TestH6Recurrence:
    THETA_GRID = [0.3, 0.5, 1.0, np.pi / 3, np.pi / 2, 2.0, np.pi]

    def test_recurrence_m3_to_m4(self):
        for theta in self.THETA_GRID:
            C    = _recurrence_constant(theta)
            d3   = _delta(3, 6, theta)
            d4   = _delta(4, 6, theta)
            pred = 3 * d3 + C
            assert np.isclose(pred, d4, rtol=1e-9, atol=1e-4)

    def test_recurrence_m4_to_m5(self):
        for theta in [0.7, 1.5, np.pi / 2, np.pi]:
            C    = _recurrence_constant(theta)
            d4   = _delta(4, 6, theta)
            d5   = _delta(5, 6, theta)
            pred = 3 * d4 + C
            assert np.isclose(pred, d5, rtol=1e-9, atol=1e-3)

    def test_C_pi_equals_5280(self):
        C_pi = _recurrence_constant(np.pi)
        assert abs(C_pi - 5280.0) < 0.1, f"C(pi) = {C_pi:.4f}"

    def test_C_zero_vanishes(self):
        C_zero = _recurrence_constant(1e-8)
        assert abs(C_zero) < 2.0


class TestH6LinearGrowth:
    THETA_GRID = [0.5, 1.0, np.pi / 3, np.pi / 2, 2.0, np.pi]

    def test_linear_law_predicts_m3_from_m4_m5(self):
        for theta in self.THETA_GRID:
            d3 = _delta(3, 6, theta)
            d4 = _delta(4, 6, theta)
            d5 = _delta(5, 6, theta)
            alpha = (d5 - d4) / (243 - 81)
            beta  = d4 - 81 * alpha
            pred3 = alpha * 27 + beta
            assert np.isclose(pred3, d3, rtol=1e-7, atol=1e-3)

    def test_no_quadratic_9power_m_term(self):
        for theta in [0.7, np.pi / 2, 2.0]:
            d3 = _delta(3, 6, theta)
            d4 = _delta(4, 6, theta)
            d5 = _delta(5, 6, theta)
            M   = np.array([[729, 27, 1], [6561, 81, 1], [59049, 243, 1]])
            abc = np.linalg.solve(M, [d3, d4, d5])
            ratio = abs(abc[0]) / max(abs(abc[1]), 1e-10)
            assert ratio < 1e-10

    def test_alpha_pi_is_minus_4112_over_3(self):
        d4 = _delta(4, 6, np.pi)
        d5 = _delta(5, 6, np.pi)
        alpha = (d5 - d4) / (243 - 81)
        assert np.isclose(alpha, -4112 / 3, rtol=1e-8)

    def test_beta_pi_is_minus_2640(self):
        d4    = _delta(4, 6, np.pi)
        d5    = _delta(5, 6, np.pi)
        alpha = (d5 - d4) / (243 - 81)
        beta  = d4 - 81 * alpha
        assert abs(beta - (-2640.0)) < 0.01


class TestH6PathClassZeroTheorem:
    THETA_GRID = [0.3, 0.7, 1.0, 1.5, 2.0, np.pi / 2, np.pi]

    def test_x_vs_z_triangle_zero(self):
        for theta in self.THETA_GRID:
            assert abs(_triangle_delta_h6(0, 2, theta)) < 1e-7

    def test_y_vs_z_triangle_zero(self):
        for theta in self.THETA_GRID:
            assert abs(_triangle_delta_h6(1, 2, theta)) < 1e-7

    def test_x_vs_y_triangle_zero(self):
        for theta in self.THETA_GRID:
            assert abs(_triangle_delta_h6(0, 1, theta)) < 1e-7


def test_h6_vanishes_at_theta_zero():
    for m in [1, 2, 3]:
        assert abs(_delta(m, 6, 1e-9)) < 1e-2


class TestH6RegressionLock:
    DELTA_PI = {1: -6744.0, 2: -14976.0, 3: -39648.0, 4: -113664.0}

    def test_delta_h6_at_pi(self):
        for m, expected in self.DELTA_PI.items():
            assert np.isclose(_delta(m, 6, np.pi), expected, atol=0.1)

    def test_recurrence_constant_at_pi_across_levels(self):
        for m in [3, 4, 5]:
            C = _delta(m, 6, np.pi) - 3 * _delta(m - 1, 6, np.pi)
            assert abs(C - 5280.0) < 0.5
