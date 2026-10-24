import numpy as np
import pytest

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


@pytest.mark.parametrize("power", [6, 8, 10])
@pytest.mark.parametrize("theta", [0.3, 0.7, 1.0, np.pi / 3, np.pi / 2, 2.0, np.pi])
def test_finite_base_transition_R3_equals_R4(power, theta):
    """Direct matrix calculation of the finite transition R_3 = R_4."""
    d2 = raw_trace_diff(2, theta, power)
    d3 = raw_trace_diff(3, theta, power)
    d4 = raw_trace_diff(4, theta, power)
    r3 = d3 - 3 * d2
    r4 = d4 - 3 * d3
    assert np.isclose(r3, r4, rtol=2e-10, atol=2e-6), (
        power, theta, r3, r4
    )


@pytest.mark.parametrize("level", [1, 2, 3])
@pytest.mark.parametrize("commuting", [False, True])
def test_exact_sparse_pi_operator_matches_production_operator(level, commuting):
    """Cross-check the exact certificate's operator builder against production.

    This guards the finite Gaussian-integer certificate against silently
    drifting from graph ordering, face-edge assignment, Pauli-axis convention,
    or the Hermitian-conjugate block used by build_su2_bundle.
    """
    from operators.operators import build_su2_bundle

    exact, dimension = _exact_sparse_operator_pi(level, commuting)
    production, vertices = build_su2_bundle(level, np.pi, commuting=commuting)
    assert production.shape == (dimension, dimension)
    assert dimension == 2 * vertices
    for i in range(dimension):
        for j in range(dimension):
            expected = exact.get((i, j), (0, 0))
            actual = production[i, j]
            assert np.isclose(actual.real, expected[0], atol=1e-12), (
                level, commuting, i, j, actual, expected
            )
            assert np.isclose(actual.imag, expected[1], atol=1e-12), (
                level, commuting, i, j, actual, expected
            )


def _gaussian_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def _gaussian_mul(a, b):
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0])


def _gaussian_neg(a):
    return (-a[0], -a[1])


def _gaussian_conj(a):
    return (a[0], -a[1])


def _exact_sparse_operator_pi(level, commuting):
    """Build H(theta=pi) with exact Gaussian-integer entries."""
    from graph.sg_graph import sg_tree_graph_with_faces

    vertices, edges, faces = sg_tree_graph_with_faces(level)
    n = len(vertices)
    degree = [0] * n
    for a, b in edges:
        degree[a] += 1
        degree[b] += 1

    zero, one = (0, 0), (1, 0)
    identity = [[one, zero], [zero, one]]
    pauli = [
        [[zero, one], [one, zero]],
        [[zero, (0, -1)], [(0, 1), zero]],
        [[one, zero], [zero, (-1, 0)]],
    ]
    edge_blocks = {tuple(sorted(edge)): identity for edge in edges}
    for index, (a, b, _c) in enumerate(faces):
        axis = 2 if commuting else index % 3
        # U = -i sigma_axis; all entries are Gaussian integers.
        edge_blocks[tuple(sorted((a, b)))] = [
            [(entry[1], -entry[0]) for entry in row]
            for row in pauli[axis]
        ]

    matrix = {}
    for vertex in range(n):
        for spin in range(2):
            matrix[(2 * vertex + spin, 2 * vertex + spin)] = (degree[vertex], 0)
    for (a, b), block in edge_blocks.items():
        for i in range(2):
            for j in range(2):
                value = _gaussian_neg(block[i][j])
                if value != zero:
                    key = (2 * a + i, 2 * b + j)
                    matrix[key] = _gaussian_add(matrix.get(key, zero), value)
                value = _gaussian_neg(_gaussian_conj(block[j][i]))
                if value != zero:
                    key = (2 * b + i, 2 * a + j)
                    matrix[key] = _gaussian_add(matrix.get(key, zero), value)
    return {key: value for key, value in matrix.items() if value != zero}, 2 * n


def _exact_sparse_product(left, right):
    """Sparse matrix product over Z[i], with arbitrary-precision integers."""
    right_rows = {}
    for (i, j), value in right.items():
        right_rows.setdefault(i, []).append((j, value))
    product = {}
    zero = (0, 0)
    for (i, k), a in left.items():
        for j, b in right_rows.get(k, ()):
            key = (i, j)
            product[key] = _gaussian_add(
                product.get(key, zero), _gaussian_mul(a, b)
            )
    return {key: value for key, value in product.items() if value != zero}


def _exact_sparse_trace_power_pi(level, power, commuting):
    matrix, dimension = _exact_sparse_operator_pi(level, commuting)
    result = {(i, i): (1, 0) for i in range(dimension)}
    for _ in range(power):
        result = _exact_sparse_product(result, matrix)
    trace = (0, 0)
    for i in range(dimension):
        trace = _gaussian_add(trace, result.get((i, i), (0, 0)))
    assert trace[1] == 0
    return trace[0]


@pytest.mark.parametrize("power,expected", [
    (6, [-6744, -14976, -39648, -113664, -335712]),
    (8, [-547552, -1373696, -3843584, -11253248, -33482240]),
    (10, [-32992520, -94971520, -280407040, -836713600, -2505633280]),
])
def test_exact_gaussian_integer_trace_defects_at_theta_pi(power, expected):
    """Exact sparse arithmetic certificate for Delta_m^(p)(pi), levels 1..5."""
    actual = []
    for level in range(1, 6):
        actual.append(
            _exact_sparse_trace_power_pi(level, power, False)
            - _exact_sparse_trace_power_pi(level, power, True)
        )
    assert actual == expected


@pytest.mark.parametrize("power,cycling,common_axis", [
    (6, 2080992, 2120640),
    (8, 89944892, 93788476),
    (10, 4082500316, 4362907356),
])
def test_exact_level_three_traces_disprove_unrestricted_axis_pattern_equality(
    power, cycling, common_axis
):
    """Pin both exact traces at theta=pi, not just their difference.

    The level-three graph has 42 vertices.  These Gaussian-integer traces
    show that cycling x/y/z axes and using a common z axis do not give equal
    traces individually for p=6,8,10.  This rules out the overly broad
    identity that the two arbitrary axis patterns have the same full trace;
    it does not rule out the stabilized level-residual identities.
    """
    actual_cycling = _exact_sparse_trace_power_pi(3, power, False)
    actual_common_axis = _exact_sparse_trace_power_pi(3, power, True)
    assert actual_cycling == cycling
    assert actual_common_axis == common_axis
    assert actual_cycling - actual_common_axis == {
        6: -39648,
        8: -3843584,
        10: -280407040,
    }[power]


@pytest.mark.parametrize("power,expected_residual", [
    (6, 5280),
    (8, 277504),
    (10, 4507520),
])
def test_exact_residual_stabilizes_from_level_three_at_theta_pi(power, expected_residual):
    """Check the finite pi-angle transition by exact integer arithmetic."""
    deltas = [
        _exact_sparse_trace_power_pi(level, power, False)
        - _exact_sparse_trace_power_pi(level, power, True)
        for level in range(1, 6)
    ]
    residuals = [deltas[level - 1] - 3 * deltas[level - 2]
                 for level in range(2, 6)]
    assert residuals[1:] == [expected_residual] * 3


@pytest.mark.parametrize("power", [6, 8, 10])
def test_finite_residual_transition_on_dense_angle_grid(power):
    """Numerically stress-test R3=R4; this is not an all-angle proof."""
    for theta in np.linspace(0.05, 2 * np.pi - 0.05, 17):
        d2 = raw_trace_diff(2, float(theta), power)
        d3 = raw_trace_diff(3, float(theta), power)
        d4 = raw_trace_diff(4, float(theta), power)
        r3 = d3 - 3 * d2
        r4 = d4 - 3 * d3
        assert np.isclose(r3, r4, rtol=3e-10, atol=3e-5), (
            power, float(theta), r3, r4
        )


@pytest.mark.parametrize("power", [6, 8, 10])
def test_finite_residual_stabilization_levels_three_to_five_angle_grid(power):
    """Numerically check R3=R4=R5 on a fixed non-singular angle grid."""
    for theta in np.linspace(0.07, 2 * np.pi - 0.07, 11):
        deltas = {
            level: raw_trace_diff(level, float(theta), power)
            for level in (2, 3, 4, 5)
        }
        residuals = {
            level: deltas[level] - 3 * deltas[level - 1]
            for level in (3, 4, 5)
        }
        assert np.isclose(residuals[3], residuals[4],
                          rtol=5e-10, atol=5e-5), (
            power, float(theta), residuals
        )
        assert np.isclose(residuals[4], residuals[5],
                          rtol=5e-10, atol=5e-5), (
            power, float(theta), residuals
        )


@pytest.mark.parametrize("power", [6, 8, 10])
def test_residual_transition_through_level_six_angle_grid(power):
    """Extend the numerical recurrence check to R5=R6 at several angles."""
    for theta in (0.23, 0.91, np.pi / 2, 2.4, np.pi):
        deltas = {
            level: raw_trace_diff(level, float(theta), power)
            for level in (4, 5, 6)
        }
        r5 = deltas[5] - 3 * deltas[4]
        r6 = deltas[6] - 3 * deltas[5]
        assert np.isclose(r5, r6, rtol=2e-9, atol=2e-4), (
            power, float(theta), r5, r6
        )


@pytest.mark.parametrize("power,expected_residual,expected_delta6", [
    (6, 5280, -1001856),
    (8, 277504, -100169216),
    (10, 4507520, -7512392320),
])
def test_exact_residual_transition_level_six_at_theta_pi(
    power, expected_residual, expected_delta6
):
    """Exact Gaussian-integer check of R6=R5, without floating-point tolerances."""
    deltas = {}
    for level in range(1, 7):
        deltas[level] = (
            _exact_sparse_trace_power_pi(level, power, False)
            - _exact_sparse_trace_power_pi(level, power, True)
        )
    residuals = {
        level: deltas[level] - 3 * deltas[level - 1]
        for level in range(2, 7)
    }
    assert deltas[6] == expected_delta6
    assert residuals[5] == expected_residual
    assert residuals[6] == expected_residual


@pytest.mark.parametrize("power,coefficient,constant", [
    (6, -37008, -2640),
    (8, -3704832, -138752),
    (10, -278153280, -2253760),
])
def test_exact_pi_angle_candidate_formula_levels_three_to_six(
    power, coefficient, constant
):
    """Check the candidate affine-in-3^m formula on exact levels 3..6 only."""
    for level in range(3, 7):
        delta = (
            _exact_sparse_trace_power_pi(level, power, False)
            - _exact_sparse_trace_power_pi(level, power, True)
        )
        assert delta == coefficient * (3 ** (level - 3)) + constant


@pytest.mark.parametrize("power", [6, 8, 10])
def test_residual_transition_r5_r6_extended_angle_grid(power):
    """Check the next-level residual transition across an independent angle grid."""
    for theta in np.linspace(0.11, 2 * np.pi - 0.11, 9):
        deltas = {
            level: raw_trace_diff(level, float(theta), power)
            for level in (4, 5, 6)
        }
        residual5 = deltas[5] - 3 * deltas[4]
        residual6 = deltas[6] - 3 * deltas[5]
        assert np.isclose(
            residual5, residual6, rtol=3e-9, atol=3e-4
        ), (power, float(theta), residual5, residual6)
