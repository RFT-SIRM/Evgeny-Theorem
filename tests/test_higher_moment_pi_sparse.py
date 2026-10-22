from computational.higher_moment_pi_certificate import (
    delta_at_pi,
    residual_at_pi,
)


def test_theta_pi_higher_moments_exact_levels_one_through_six():
    """Exact Gaussian-integer calculation matches the full finite regression."""
    expected_deltas = {
        6: [-6744, -14976, -39648, -113664, -335712, -1001856],
        8: [-547552, -1373696, -3843584, -11253248, -33482240, -100169216],
        10: [
            -32992520,
            -94971520,
            -280407040,
            -836713600,
            -2505633280,
            -7512392320,
        ],
    }
    expected_residuals = {
        6: [5256, 5280, 5280, 5280, 5280],
        8: [268960, 277504, 277504, 277504, 277504],
        10: [4006040, 4507520, 4507520, 4507520, 4507520],
    }

    for power in (6, 8, 10):
        deltas = [delta_at_pi(level, power) for level in range(1, 7)]
        assert deltas == expected_deltas[power]
        residuals = [
            deltas[level - 1] - 3 * deltas[level - 2]
            for level in range(2, 7)
        ]
        assert residuals == expected_residuals[power]
        # Independently exercise the public transition helper at level six.
        assert residual_at_pi(6, power) == expected_residuals[power][-1]
