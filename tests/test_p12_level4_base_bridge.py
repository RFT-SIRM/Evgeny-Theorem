"""Full-matrix exact check of the level-four H12 base residual.

The 17-term expected normal form is also checked independently against the
level-five corner/edge locality calculation by the Stage 4 constant test.
"""
from computational.higher_moment_p12_level5_constant import (
    EXPECTED_C12_CIRCLE_NORMAL_FORM,
)
from computational.higher_moment_p12_symbolic import (
    _circle_normal_form,
    _linear_combination,
    _real_delta_polynomial,
)


def test_exact_h12_level4_residual_equals_level5_tail_constant():
    delta3 = _real_delta_polynomial(3)
    delta4 = _real_delta_polynomial(4)
    residual4 = _circle_normal_form(
        _linear_combination([(1, delta4), (-3, delta3)])
    )
    assert residual4 == EXPECTED_C12_CIRCLE_NORMAL_FORM
