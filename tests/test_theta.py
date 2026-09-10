"""
Direct verification of Evgeny's Theorem (the H^4 closed form) across a
grid of theta values at a fixed, small refinement level -- independent
of the held-out spot-checks in test_heldout.py.
"""
import numpy as np
import pytest

from moments.moments import evgeny_theorem_H4, raw_trace_diff_H4

THETAS = [0.05, 0.3, 0.7, 1.0, 1.5, np.pi / 2, 2.0, 2.5, 3.0, 3.13]


@pytest.mark.parametrize("theta", THETAS)
def test_theorem_matches_direct_computation_level2(theta):
    direct = raw_trace_diff_H4(level=2, theta=theta)
    formula = evgeny_theorem_H4(level=2, theta=theta)
    assert abs(direct - formula) < 1e-9


@pytest.mark.parametrize("theta", THETAS)
def test_theorem_matches_direct_computation_level3(theta):
    direct = raw_trace_diff_H4(level=3, theta=theta)
    formula = evgeny_theorem_H4(level=3, theta=theta)
    assert abs(direct - formula) < 1e-9


def test_theorem_is_zero_at_theta_zero():
    """No flux -> C and C' are identical -> the defect must vanish exactly."""
    for level in (1, 2, 3, 4):
        assert abs(evgeny_theorem_H4(level, 0.0)) < 1e-12
        assert abs(raw_trace_diff_H4(level, 0.0)) < 1e-9
