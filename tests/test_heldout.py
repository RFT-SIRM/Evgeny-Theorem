"""
The held-out verification set: (level, theta) pairs chosen after the
closed form in THEOREM.md was already fixed, specifically to avoid any
suspicion of curve-fitting. See VERIFICATION.md section 5.2 for the
original run this reproduces.

Also reproduces the m=1..7 refinement sequence at theta=pi/2 and checks
convergence toward the analytic limit -8/9 (VERIFICATION.md section 6).

test_level7_matches_formula is the slow test in this suite (dim=6564);
it is expected to take on the order of two minutes.
"""
import numpy as np
import pytest

from moments.moments import evgeny_theorem_H4, raw_trace_diff_H4, normalized_invariant_I

HELDOUT = [
    (2, 0.7, -7.5250500069),
    (3, 1.9, -105.8631653491),
    (5, 2.5, -1181.5502117988),
    (1, 3.0, -31.8398799456),
    (4, 0.3, -10.0046264358),
]


@pytest.mark.parametrize("level,theta,expected", HELDOUT)
def test_heldout_pairs_match_formula(level, theta, expected):
    formula = evgeny_theorem_H4(level, theta)
    assert abs(formula - expected) < 1e-6


@pytest.mark.parametrize("level,theta,expected", HELDOUT)
def test_heldout_pairs_match_direct_computation(level, theta, expected):
    direct = raw_trace_diff_H4(level, theta)
    assert abs(direct - expected) < 1e-6


def test_Im_sequence_theta_pi_over_2():
    expected = {
        1: -1.333333,
        2: -1.066667,
        3: -0.952381,
        4: -0.910569,
        5: -0.896175,
        6: -0.891324,
    }
    for level, exp in expected.items():
        got = normalized_invariant_I(level, np.pi / 2)
        assert abs(got - exp) < 1e-5


def test_Im_converges_towards_minus_8_over_9():
    theta = np.pi / 2
    vals = [normalized_invariant_I(m, theta) for m in range(1, 8)]
    # monotone approach and strictly decreasing distance to the limit
    limit = -8.0 / 9.0
    dists = [abs(v - limit) for v in vals]
    assert all(d2 < d1 for d1, d2 in zip(dists, dists[1:]))
    assert dists[-1] < 1e-3  # at m=7 already within 1e-3 of -8/9


@pytest.mark.slow
def test_level7_matches_formula():
    level, theta = 7, np.pi / 2
    direct = raw_trace_diff_H4(level, theta)
    formula = evgeny_theorem_H4(level, theta)
    assert abs(direct - formula) < 1e-6
