from computational.higher_moment_pi_certificate import (
    delta_at_pi,
    residual_at_pi,
)


def test_theta_pi_higher_moments_level_six_direct_sparse_calculation():
    """Direct level-six values agree with the finite-data candidate recurrence."""
    expected = {
        6: (-1_001_856, 5_280),
        8: (-100_169_216, 277_504),
        10: (-7_512_392_320, 4_507_520),
    }
    for power, (delta6, stable_residual) in expected.items():
        assert delta_at_pi(6, power) == delta6
        # This only checks the computed m=6 transition; it does not prove
        # that the residual is constant at arbitrary levels or angles.
        assert residual_at_pi(6, power) == stable_residual
