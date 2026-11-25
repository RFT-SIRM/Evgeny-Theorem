from fractions import Fraction

from computational.higher_moment_p12_level5_constant import (
    evaluate_p12_level5_affine_constant_at_rational_circle_point,
    p12_level5_affine_constant_matches_expected,
)


def test_exact_h12_level5_affine_constant():
    assert p12_level5_affine_constant_matches_expected()
    checks = [
        (0, 1, 1, Fraction(-634073536, 1)),
        (1, 0, 1, Fraction(0, 1)),
        (3, 4, 5, Fraction(-4777581144064, 390625)),
        (5, 12, 13, Fraction(-154683470170552320, 815730721)),
    ]
    for c, s, denominator, expected in checks:
        actual = evaluate_p12_level5_affine_constant_at_rational_circle_point(
            c, s, denominator
        )
        assert actual == expected
