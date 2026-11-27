"""Exact explicit closed form of the H12 trace defect for every level m >= 3.

Lean (FinalClosed12.lean) proves, for every real theta and every m >= 3,

    D_{m+1} = 3 D_m + C_12,   hence   D_m = 3^(m-3) (D_3 + C_12/2) - C_12/2,

with D_3 and C_12 kept as exact finite trace expressions.  This module checks,
with exact integer arithmetic only (no floating point), that these two finite
quantities are the explicit polynomials

    D_3  = 32 s^2 Q_3(c, s),        C_12 = -64 s^2 Q_12(c, s),

with c = cos(theta/2), s = sin(theta/2), c^2 + s^2 = 1, so that

    D_m  = 32 s^2 (3^(m-3) (Q_3 - Q_12) + Q_12)    for m >= 3.

The two identities are exact computer-algebra certificates.  They are not
Lean-kernel theorems.
"""
from fractions import Fraction

import pytest

from computational.higher_moment_p12_level5_constant import (
    EXPECTED_C12_CIRCLE_NORMAL_FORM,
)
from computational.higher_moment_p12_symbolic import (
    _circle_normal_form,
    _linear_combination,
    _real_delta_polynomial,
)
from computational.higher_moment_pi_certificate import delta_at_pi

# Exponent keys are (power of c, power of s).
Q3 = {
    (6, 0): -12, (5, 1): 24, (5, 0): 1032, (4, 1): -2040, (4, 0): -80120,
    (3, 1): 42894, (3, 0): 2400282, (2, 1): -67494, (2, 0): -30361019,
    (1, 1): -2479593, (1, 0): 275590614, (0, 1): 3481440, (0, 0): -566815997,
}
Q12 = {
    (6, 0): 6, (5, 1): 6, (5, 0): 240, (4, 1): -456, (4, 0): -8858,
    (3, 1): 2466, (3, 0): -33138, (2, 1): 618, (2, 0): 1612501,
    (1, 1): 571254, (1, 0): -18512844, (0, 1): -3259668, (0, 0): 13167067,
}


def _times_s2(poly, factor):
    """factor * s^2 * poly."""
    return {(i, j + 2): factor * v for (i, j), v in poly.items()}


def _evaluate(poly, c, s):
    return sum(Fraction(v) * c**i * s**j for (i, j), v in poly.items())


def _closed_form_at(m, c, s):
    """32 s^2 (3^(m-3) (Q3 - Q12) + Q12) evaluated at (c, s)."""
    q3, q12 = _evaluate(Q3, c, s), _evaluate(Q12, c, s)
    return 32 * s**2 * (3 ** (m - 3) * (q3 - q12) + q12)


def test_h12_level3_defect_is_32_s2_q3():
    delta3 = _real_delta_polynomial(3)
    assert _circle_normal_form(delta3) == _circle_normal_form(_times_s2(Q3, 32))


def test_h12_residual_is_minus_64_s2_q12():
    delta3 = _real_delta_polynomial(3)
    delta4 = _real_delta_polynomial(4)
    residual = _circle_normal_form(
        _linear_combination([(1, delta4), (-3, delta3)])
    )
    assert residual == _circle_normal_form(_times_s2(Q12, -64))
    assert residual == EXPECTED_C12_CIRCLE_NORMAL_FORM


def test_h12_closed_form_at_exact_circle_points_levels_3_and_4():
    deltas = {3: _real_delta_polynomial(3), 4: _real_delta_polynomial(4)}
    points = [
        (Fraction(3, 5), Fraction(4, 5)),
        (Fraction(5, 13), Fraction(12, 13)),
        (Fraction(8, 17), Fraction(15, 17)),
        (Fraction(-3, 5), Fraction(4, 5)),
        (Fraction(0), Fraction(1)),
        (Fraction(1), Fraction(0)),
    ]
    for c, s in points:
        assert c * c + s * s == 1
        for m, delta in deltas.items():
            assert _evaluate(delta, c, s) == _closed_form_at(m, c, s)


@pytest.mark.parametrize("level", [3, 4, 5, 6])
def test_h12_closed_form_at_theta_pi(level):
    """Independent full-matrix Gaussian-integer calculation at theta = pi."""
    assert Fraction(delta_at_pi(level, 12)) == _closed_form_at(
        level, Fraction(0), Fraction(1)
    )
