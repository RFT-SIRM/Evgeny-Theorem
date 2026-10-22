import numpy as np

from moments.moments import raw_trace_diff_H4
from operators.operators import build_su2_bundle


def raw_trace_diff(level: int, theta: float, p: int) -> float:
    HC, _ = build_su2_bundle(level, theta, commuting=False)
    HCp, _ = build_su2_bundle(level, theta, commuting=True)
    return float(np.trace(np.linalg.matrix_power(HC, p)).real
                  - np.trace(np.linalg.matrix_power(HCp, p)).real)


def test_h6_theta_pi_over_2_current_convention():
    expected = [
        -3180.000000000000,
        -6956.588745030516,
        -18274.354980121832,
        -52227.653685396537,
    ]
    for level, value in enumerate(expected, start=1):
        actual = raw_trace_diff(level, np.pi / 2, 6)
        assert np.isclose(actual, value, rtol=1e-11, atol=1e-8), (
            level, actual, value
        )


def test_h8_theta_pi_over_2_current_convention():
    expected = [
        -246909.026268397924,
        -595053.284942481667,
        -1632052.331668503582,
        -4743049.471846580505,
    ]
    for level, value in enumerate(expected, start=1):
        actual = raw_trace_diff(level, np.pi / 2, 8)
        assert np.isclose(actual, value, rtol=1e-11, atol=1e-7), (
            level, actual, value
        )


def test_h10_theta_pi_over_2_current_convention():
    expected = [
        -14013358.982483163476,
        -37686518.369789719582,
        -107772338.487565994263,
        -318029798.840893745422,
    ]
    for level, value in enumerate(expected, start=1):
        actual = raw_trace_diff(level, np.pi / 2, 10)
        assert np.isclose(actual, value, rtol=1e-11, atol=1e-5), (
            level, actual, value
        )


def test_higher_moment_residuals_at_theta_pi_levels_2_to_5():
    """Recompute R_m = Delta_m - 3 Delta_(m-1) from operator matrices."""
    expected = {
        6: [5256.0, 5280.0, 5280.0, 5280.0],
        8: [268960.0, 277504.0, 277504.0, 277504.0],
        10: [4006040.0, 4507520.0, 4507520.0, 4507520.0],
    }
    for power, residuals in expected.items():
        deltas = {
            level: raw_trace_diff(level, np.pi, power)
            for level in range(1, 6)
        }
        actual = [
            deltas[level] - 3 * deltas[level - 1]
            for level in range(2, 6)
        ]
        assert np.allclose(actual, residuals, rtol=1e-11, atol=1e-5), (
            power, actual, residuals
        )
