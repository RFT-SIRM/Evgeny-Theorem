"""Exact symbolic certificate for the p=12 affine-tail constant at level five.

Write c = cos(theta/2), s = sin(theta/2).  The Lean recurrence proved for
m >= 4 has a level-five constant

    C_12(theta) = B_5(theta) - (D_5^num(theta) - D_5^til(theta)),

where B_5 is the axis-dependent H12 gluing boundary term and D_5^num,
D_5^til are the two orientation-specific trace defects.  This module computes
that exact finite expression with sparse polynomials over Gaussian integers.

Only radius-five graph neighborhoods are needed:
* a corner diagonal entry (K^n)_{xx}, n <= 11, is determined by closed
  walks of length n based at x, all lying within distance floor(n/2) <= 5;
* a closed walk of length 12 that uses the single flipped edge lies in the
  radius-five neighborhood of the two endpoints of that edge.

The result is reduced modulo c^2 + s^2 = 1.  This is an exact finite
computational certificate, not a Lean-kernel proof of the polynomial identity.
"""
from __future__ import annotations

from functools import lru_cache
from fractions import Fraction
from math import comb
from typing import TypeAlias

from graph.sg_graph import sg_tree_graph_with_faces

Gaussian: TypeAlias = tuple[int, int]
Exponent: TypeAlias = tuple[int, int]
Polynomial: TypeAlias = dict[Exponent, Gaussian]
IntegerPolynomial: TypeAlias = dict[Exponent, int]
Block: TypeAlias = list[list[Polynomial]]
SparseBlockMatrix: TypeAlias = list[dict[int, Block]]

ZERO: Gaussian = (0, 0)
ONE: Gaussian = (1, 0)

EXPECTED_C12_CIRCLE_NORMAL_FORM: IntegerPolynomial = {
    (0, 0): -842692288,
    (0, 1): 208618752,
    (1, 0): 1184822016,
    (1, 1): -36560256,
    (2, 0): 739492224,
    (2, 1): -208658304,
    (3, 0): -1182701184,
    (3, 1): 36402432,
    (4, 0): 103766976,
    (4, 1): 68736,
    (5, 0): -2136192,
    (5, 1): 157440,
    (6, 0): -567296,
    (6, 1): -29184,
    (7, 0): 15360,
    (7, 1): 384,
    (8, 0): 384,
}


def _gadd(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] + b[0], a[1] + b[1]


def _gneg(a: Gaussian) -> Gaussian:
    return -a[0], -a[1]


def _gmul(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def _gconj(a: Gaussian) -> Gaussian:
    return a[0], -a[1]


def _padd(a: Polynomial, b: Polynomial) -> Polynomial:
    out = dict(a)
    for monomial, coefficient in b.items():
        value = _gadd(out.get(monomial, ZERO), coefficient)
        if value == ZERO:
            out.pop(monomial, None)
        else:
            out[monomial] = value
    return out


def _pscale(a: Polynomial, scalar: Gaussian) -> Polynomial:
    if scalar == ZERO:
        return {}
    out = {}
    for monomial, coefficient in a.items():
        value = _gmul(coefficient, scalar)
        if value != ZERO:
            out[monomial] = value
    return out


def _pmul(a: Polynomial, b: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for (ac, ass), za in a.items():
        for (bc, bs), zb in b.items():
            monomial = (ac + bc, ass + bs)
            value = _gadd(out.get(monomial, ZERO), _gmul(za, zb))
            if value == ZERO:
                out.pop(monomial, None)
            else:
                out[monomial] = value
    return out


def _pconj(a: Polynomial) -> Polynomial:
    return {monomial: _gconj(coefficient) for monomial, coefficient in a.items()}


def _pconst(value: Gaussian) -> Polynomial:
    return {} if value == ZERO else {(0, 0): value}


def _pmon(c_power: int, s_power: int, value: Gaussian = ONE) -> Polynomial:
    return {} if value == ZERO else {(c_power, s_power): value}


def _block_zero() -> Block:
    return [[{}, {}], [{}, {}]]


def _block_scale_identity(value: int) -> Block:
    scalar = _pconst((value, 0))
    return [[scalar, {}], [{}, scalar]]


def _block_add(a: Block, b: Block) -> Block:
    return [[_padd(a[i][j], b[i][j]) for j in range(2)] for i in range(2)]


def _block_mul(a: Block, b: Block) -> Block:
    return [
        [
            _padd(_pmul(a[i][0], b[0][j]), _pmul(a[i][1], b[1][j]))
            for j in range(2)
        ]
        for i in range(2)
    ]


def _block_dagger(a: Block) -> Block:
    return [[_pconj(a[j][i]) for j in range(2)] for i in range(2)]


def _block_is_zero(a: Block) -> bool:
    return not any(a[i][j] for i in range(2) for j in range(2))


def _edge_hamiltonian_block(axis: int) -> Block:
    """Forward block -U for U = c I - i s sigma_axis."""
    minus_c = _pmon(1, 0, (-1, 0))
    if axis == 0:
        off_diagonal = _pmon(0, 1, (0, 1))
        return [[minus_c, off_diagonal], [off_diagonal, minus_c]]
    if axis == 1:
        return [
            [minus_c, _pmon(0, 1, ONE)],
            [_pmon(0, 1, (-1, 0)), minus_c],
        ]
    if axis == 2:
        return [
            [_padd(minus_c, _pmon(0, 1, (0, 1))), {}],
            [{}, _padd(minus_c, _pmon(0, 1, (0, -1)))],
        ]
    raise ValueError(f"unsupported SU(2) axis: {axis}")


def _graph_data(level: int):
    vertices, edges, faces = sg_tree_graph_with_faces(level)
    degrees = [0] * len(vertices)
    adjacency = [set() for _ in vertices]
    for a, b in edges:
        degrees[a] += 1
        degrees[b] += 1
        adjacency[a].add(b)
        adjacency[b].add(a)
    # face order is the repo's flux-index order; matrix orientation is by
    # vertex-list index, as in Lean's vIdx/oNum, not coordinate lexicographic order.
    flux_axes = {
        tuple(sorted((a, b))): index % 3
        for index, (a, b, _third) in enumerate(faces)
    }
    left = vertices.index((round((2**level - 1) / (2**level), 10), 0.0))
    right = vertices.index((1.0, 0.0))
    if left >= right:
        raise ArithmeticError("the exceptional corner edge is not in oNum order")
    flipped_edge = (left, right)
    if flipped_edge not in flux_axes:
        raise ArithmeticError("the exceptional corner edge is not a flux edge")
    return vertices, edges, degrees, adjacency, flux_axes, flipped_edge


def _radius_ball(adjacency: list[set[int]], roots: set[int], radius: int) -> set[int]:
    seen = set(roots)
    frontier = set(roots)
    for _ in range(radius):
        following = {v for u in frontier for v in adjacency[u]} - seen
        seen.update(following)
        frontier = following
    return seen


def _local_operator_rows(
    axes_mode: str,
    flip_orientation: bool,
    ball: set[int],
    data,
) -> tuple[SparseBlockMatrix, dict[int, int]]:
    vertices, edges, degrees, _adjacency, flux_axes, flipped_edge = data
    local_vertices = sorted(ball)
    local_index = {vertex: index for index, vertex in enumerate(local_vertices)}
    rows: SparseBlockMatrix = [dict() for _ in local_vertices]

    # Keep the full graph degree on the diagonal, even at the edge of the ball.
    for vertex in local_vertices:
        rows[local_index[vertex]][local_index[vertex]] = _block_scale_identity(
            degrees[vertex]
        )

    for a, b in edges:
        if a not in ball or b not in ball:
            continue
        edge = tuple(sorted((a, b)))
        if edge in flux_axes:
            axis = 2 if axes_mode == "const" else flux_axes[edge]
            forward = _edge_hamiltonian_block(axis)
            reverse = _block_dagger(forward)
            if flip_orientation and edge == flipped_edge:
                forward, reverse = reverse, forward
        else:
            forward = _block_scale_identity(-1)
            reverse = forward
        rows[local_index[a]][local_index[b]] = forward
        rows[local_index[b]][local_index[a]] = reverse
    return rows, local_index


def _sparse_right_multiply(
    a: SparseBlockMatrix, b: SparseBlockMatrix
) -> SparseBlockMatrix:
    out: SparseBlockMatrix = []
    for row in a:
        accumulated: dict[int, Block] = {}
        for middle, left_block in row.items():
            for column, right_block in b[middle].items():
                product = _block_mul(left_block, right_block)
                if column in accumulated:
                    accumulated[column] = _block_add(accumulated[column], product)
                else:
                    accumulated[column] = product
        out.append(
            {column: block for column, block in accumulated.items() if not _block_is_zero(block)}
        )
    return out


def _trace_polynomial_on_ball(
    rows: SparseBlockMatrix, local_index: dict[int, int], power_n: int
) -> Polynomial:
    power = rows
    for _ in range(power_n - 1):
        power = _sparse_right_multiply(power, rows)
    trace: Polynomial = {}
    for index, row in enumerate(power):
        diagonal = row.get(index)
        if diagonal:
            trace = _padd(trace, diagonal[0][0])
            trace = _padd(trace, diagonal[1][1])
    if any(coefficient[1] != 0 for coefficient in trace.values()):
        raise ArithmeticError("the trace polynomial has a nonzero imaginary coefficient")
    return {monomial: value for monomial, value in trace.items() if value[0] != 0}


def _orientation_gap_polynomial(level: int) -> Polynomial:
    """Compute D_num(level)-D_til(level) for p=12 exactly."""
    data = _graph_data(level)
    _vertices, _edges, _degrees, adjacency, _flux_axes, flipped_edge = data
    ball = _radius_ball(adjacency, set(flipped_edge), 5)
    result: Polynomial = {}
    for axes_mode, sign in (("face", 1), ("const", -1)):
        for flipped, orientation_sign in ((False, 1), (True, -1)):
            rows, local_index = _local_operator_rows(axes_mode, flipped, ball, data)
            trace = _trace_polynomial_on_ball(rows, local_index, 12)
            signed = {
                monomial: (sign * orientation_sign * value[0], 0)
                for monomial, value in trace.items()
            }
            result = _padd(result, signed)
    return {monomial: value for monomial, value in result.items() if value != ZERO}


def _corner_diagonal_powers(
    level: int, axes_mode: str, flip_orientation: bool, data
) -> dict[str, dict[int, list[Polynomial]]]:
    vertices, _edges, _degrees, adjacency, _flux_axes, _flipped_edge = data
    corners = {"O": (0.0, 0.0), "X": (1.0, 0.0), "Y": (0.0, 1.0)}
    result: dict[str, dict[int, list[Polynomial]]] = {}
    for corner_name, point in corners.items():
        root = vertices.index(point)
        ball = _radius_ball(adjacency, {root}, 5)
        rows, local_index = _local_operator_rows(
            axes_mode, flip_orientation, ball, data
        )
        root_index = local_index[root]
        vector: dict[int, Block] = {
            root_index: [[_pconst(ONE), {}], [{}, _pconst(ONE)]]
        }
        values: dict[int, list[Polynomial]] = {0: [{(0, 0): 1}, {(0, 0): 1}]}
        for exponent in range(1, 12):
            following: dict[int, Block] = {}
            for middle, left_block in vector.items():
                for target, right_block in rows[middle].items():
                    product = _block_mul(left_block, right_block)
                    if target in following:
                        following[target] = _block_add(following[target], product)
                    else:
                        following[target] = product
            vector = following
            diagonal = vector.get(root_index, _block_zero())
            first, second = diagonal[0][0], diagonal[1][1]
            if any(z[1] != 0 for z in first.values()) or any(
                z[1] != 0 for z in second.values()
            ):
                raise ArithmeticError(
                    f"non-real corner diagonal at {corner_name}, exponent {exponent}"
                )
            values[exponent] = [
                {monomial: coefficient[0] for monomial, coefficient in first.items()},
                {monomial: coefficient[0] for monomial, coefficient in second.items()},
            ]
        result[corner_name] = values
    return result


def _integer_polynomial_add(a: IntegerPolynomial, b: IntegerPolynomial) -> IntegerPolynomial:
    out = dict(a)
    for monomial, coefficient in b.items():
        value = out.get(monomial, 0) + coefficient
        if value:
            out[monomial] = value
        else:
            out.pop(monomial, None)
    return out


def _integer_polynomial_multiply(
    a: IntegerPolynomial, b: IntegerPolynomial
) -> IntegerPolynomial:
    out: IntegerPolynomial = {}
    for (ac, ass), ca in a.items():
        for (bc, bs), cb in b.items():
            monomial = (ac + bc, ass + bs)
            value = out.get(monomial, 0) + ca * cb
            if value:
                out[monomial] = value
            else:
                out.pop(monomial, None)
    return out


def _scale_fraction(poly: IntegerPolynomial, scalar: Fraction) -> dict[Exponent, Fraction]:
    return {monomial: Fraction(coefficient) * scalar for monomial, coefficient in poly.items()}


def _fraction_polynomial_add(
    a: dict[Exponent, Fraction], b: dict[Exponent, Fraction]
) -> dict[Exponent, Fraction]:
    out = dict(a)
    for monomial, coefficient in b.items():
        value = out.get(monomial, Fraction(0)) + coefficient
        if value:
            out[monomial] = value
        else:
            out.pop(monomial, None)
    return out


def _positive_compositions(total: int, parts: int):
    if parts == 1:
        yield (total,)
        return
    for first in range(1, total - parts + 2):
        for tail in _positive_compositions(total - first, parts - 1):
            yield (first,) + tail


def _glue_rhs12_from_corner_diagonals(
    level: int,
    diagonal_data: dict[str, dict[str, dict[str, dict[int, list[Polynomial]]]]],
    axes_mode: str,
) -> dict[Exponent, Fraction]:
    """Evaluate the six-pair H12 boundary formula from corner diagonals.

    The weighted word-to-gap identity supplies a factor 12/r for each
    positive composition of 12 into r parts.  The three glued endpoint pairs
    are A-X <-> B-O, A-Y <-> C-O, and B-Y <-> C-X.  The sum over `x` in
    glueRHS8_pair_sum includes both orientations of each endpoint pair.
    """
    copy_diagonals = {
        "A": diagonal_data[axes_mode]["num"],
        "B": diagonal_data[axes_mode]["num"],
        "C": diagonal_data[axes_mode]["til"],
    }
    endpoint_pairs = [
        (("A", "X"), ("B", "O")),
        (("A", "Y"), ("C", "O")),
        (("B", "Y"), ("C", "X")),
    ]
    total: dict[Exponent, Fraction] = {}
    for insertion_count in (2, 4, 6, 8, 10, 12):
        subtotal: IntegerPolynomial = {}
        for composition in _positive_compositions(12, insertion_count):
            padded = [composition[0]] + [0] * (12 - insertion_count) + list(composition[1:])
            pairs = list(zip(padded[::2], padded[1::2]))
            if len(padded) != 12 or len(pairs) != 6:
                raise ArithmeticError("invalid p=12 gap padding")
            if any(a > 11 or b > 11 for a, b in pairs):
                raise ArithmeticError("p=12 boundary exponent exceeds degree eleven")
            for (copy_a, corner_a), (copy_b, corner_b) in endpoint_pairs:
                for spin in (0, 1):
                    forward: IntegerPolynomial = {(0, 0): 1}
                    reverse: IntegerPolynomial = {(0, 0): 1}
                    for first, second in pairs:
                        forward = _integer_polynomial_multiply(
                            forward, copy_diagonals[copy_a][corner_a][first][spin]
                        )
                        forward = _integer_polynomial_multiply(
                            forward, copy_diagonals[copy_b][corner_b][second][spin]
                        )
                        reverse = _integer_polynomial_multiply(
                            reverse, copy_diagonals[copy_b][corner_b][first][spin]
                        )
                        reverse = _integer_polynomial_multiply(
                            reverse, copy_diagonals[copy_a][corner_a][second][spin]
                        )
                    subtotal = _integer_polynomial_add(subtotal, forward)
                    subtotal = _integer_polynomial_add(subtotal, reverse)
        total = _fraction_polynomial_add(
            total, _scale_fraction(subtotal, Fraction(12, insertion_count))
        )
    return total


def _circle_normal_form(poly: dict[Exponent, Fraction]) -> dict[Exponent, Fraction]:
    """Reduce s^2 to 1-c^2, leaving s-exponents zero or one."""
    out: dict[Exponent, Fraction] = {}
    for (c_power, s_power), coefficient in poly.items():
        quotient, remainder = divmod(s_power, 2)
        for k in range(quotient + 1):
            monomial = (c_power + 2 * k, remainder)
            value = out.get(monomial, Fraction(0)) + (
                coefficient * comb(quotient, k) * (-1 if k % 2 else 1)
            )
            if value:
                out[monomial] = value
            else:
                out.pop(monomial, None)
    return out


@lru_cache(maxsize=1)
def p12_level5_affine_constant_circle_normal_form() -> IntegerPolynomial:
    """Return the exact circle-normal form of the H12 tail coefficient C_12.

    This computes B_5 - (D_5^num - D_5^til) for the actual level-five SG
    graph and reduces it modulo c^2+s^2=1.  No floating-point arithmetic is
    used.  The result is independent of the chosen point on the unit circle.
    """
    level = 5
    data = _graph_data(level)
    diagonal_data: dict[str, dict[str, dict[str, dict[int, list[Polynomial]]]]] = {}
    for axes_mode in ("face", "const"):
        diagonal_data[axes_mode] = {
            "num": _corner_diagonal_powers(level, axes_mode, False, data),
            "til": _corner_diagonal_powers(level, axes_mode, True, data),
        }

    boundary_face = _glue_rhs12_from_corner_diagonals(level, diagonal_data, "face")
    boundary_const = _glue_rhs12_from_corner_diagonals(level, diagonal_data, "const")
    boundary_difference = _fraction_polynomial_add(
        boundary_face,
        {monomial: -coefficient for monomial, coefficient in boundary_const.items()},
    )

    orientation_gap = _orientation_gap_polynomial(level)
    orientation_gap_real = {
        monomial: Fraction(coefficient[0])
        for monomial, coefficient in orientation_gap.items()
    }
    residual = _fraction_polynomial_add(
        boundary_difference,
        {monomial: -coefficient for monomial, coefficient in orientation_gap_real.items()},
    )
    normal = _circle_normal_form(residual)
    if any(coefficient.denominator != 1 for coefficient in normal.values()):
        raise ArithmeticError("the H12 level-five constant is not integral")
    return {monomial: coefficient.numerator for monomial, coefficient in normal.items()}


def p12_level5_affine_constant_matches_expected() -> bool:
    """Compare the exact graph computation with the fixed polynomial."""
    return p12_level5_affine_constant_circle_normal_form() == EXPECTED_C12_CIRCLE_NORMAL_FORM


def evaluate_p12_level5_affine_constant_at_rational_circle_point(
    c: int, s: int, denominator: int
) -> Fraction:
    """Evaluate C_12(c/d,s/d) exactly, requiring c^2+s^2=d^2."""
    if denominator <= 0 or c * c + s * s != denominator * denominator:
        raise ValueError("(c/d,s/d) must be a rational point on the unit circle")
    polynomial = p12_level5_affine_constant_circle_normal_form()
    return sum(
        (
            Fraction(coefficient)
            * Fraction(c, denominator) ** c_power
            * Fraction(s, denominator) ** s_power
            for (c_power, s_power), coefficient in polynomial.items()
        ),
        Fraction(0),
    )
