"""Exact all-angle p=12 finite-transition certificate.

The entries of the level-m operator are represented as sparse polynomials in
c = cos(theta/2), s = sin(theta/2), with Gaussian-integer coefficients.
This module computes Delta_m = Tr(H_noncommuting^12)-Tr(H_commuting^12)
for m=2,3,4 and reduces Delta_4 - 4 Delta_3 + 3 Delta_2 modulo
c^2+s^2=1. No floating-point arithmetic is used.

The result certifies only the finite m=3 -> 4 residual difference. It is not
an all-level recurrence proof.
"""
from __future__ import annotations

from functools import lru_cache
from math import comb
from typing import TypeAlias

from graph.sg_graph import sg_tree_graph_with_faces

Gaussian: TypeAlias = tuple[int, int]
Exponent: TypeAlias = tuple[int, int]
Polynomial: TypeAlias = dict[Exponent, Gaussian]
SparseMatrix: TypeAlias = list[dict[int, Polynomial]]
ZERO: Gaussian = (0, 0)
ONE: Gaussian = (1, 0)


def _gadd(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0] + b[0], a[1] + b[1])


def _gneg(a: Gaussian) -> Gaussian:
    return (-a[0], -a[1])


def _gmul(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0])


def _gconj(a: Gaussian) -> Gaussian:
    return (a[0], -a[1])


def _poly_add_scaled(
    target: Polynomial,
    source: Polynomial,
    scalar: Gaussian = ONE,
    shift: Exponent = (0, 0),
) -> None:
    """Add scalar*c^shift[0]*s^shift[1]*source into target in place."""
    di, dj = shift
    for (i, j), coefficient in source.items():
        key = (i + di, j + dj)
        value = _gadd(target.get(key, ZERO), _gmul(coefficient, scalar))
        if value == ZERO:
            target.pop(key, None)
        else:
            target[key] = value


def _edge_rotation(axis: int) -> list[list[Polynomial]]:
    """Return the exact 2x2 polynomial matrix for the selected SU(2) axis."""
    c = {(1, 0): ONE}
    s = {(0, 1): ONE}
    if axis == 0:
        minus_i_s = {(0, 1): (0, -1)}
        return [[c, minus_i_s], [minus_i_s, c]]
    if axis == 1:
        minus_s = {(0, 1): (-1, 0)}
        plus_s = {(0, 1): ONE}
        return [[c, minus_s], [plus_s, c]]
    if axis == 2:
        return [
            [{(1, 0): ONE, (0, 1): (0, -1)}, {}],
            [{}, {(1, 0): ONE, (0, 1): (0, 1)}],
        ]
    raise ValueError(f"unsupported axis: {axis}")


def _operator_polynomial(level: int, commuting: bool) -> SparseMatrix:
    vertices, edges, faces = sg_tree_graph_with_faces(level)
    vertex_count = len(vertices)
    size = 2 * vertex_count
    degree = [0] * vertex_count
    for u, v in edges:
        degree[u] += 1
        degree[v] += 1

    rows: SparseMatrix = [dict() for _ in range(size)]

    def put(row: int, column: int, terms: Polynomial) -> None:
        target = rows[row].setdefault(column, {})
        _poly_add_scaled(target, terms)
        if not target:
            rows[row].pop(column, None)

    for vertex, deg in enumerate(degree):
        if deg:
            diagonal = {(0, 0): (deg, 0)}
            put(2 * vertex, 2 * vertex, diagonal)
            put(2 * vertex + 1, 2 * vertex + 1, diagonal)

    identity = [[{(0, 0): ONE}, {}], [{}, {(0, 0): ONE}]]
    rotations = {tuple(sorted(edge)): identity for edge in edges}
    for face_index, (u, v, _third) in enumerate(faces):
        axis = 2 if commuting else face_index % 3
        rotations[tuple(sorted((u, v)))] = _edge_rotation(axis)

    for u, v in edges:
        u, v = sorted((u, v))
        rotation = rotations[(u, v)]
        for i in range(2):
            for j in range(2):
                _poly_add_scaled(rows[2 * u + i].setdefault(2 * v + j, {}),
                                 rotation[i][j], _gneg(ONE))
                # Reverse edge uses the negative conjugate transpose.
                reverse = {
                    exponent: _gneg(_gconj(coefficient))
                    for exponent, coefficient in rotation[j][i].items()
                }
                _poly_add_scaled(rows[2 * v + i].setdefault(2 * u + j, {}),
                                 reverse)

    for row in rows:
        for column in list(row):
            if not row[column]:
                del row[column]
    return rows


def _sparse_right_multiply(a: SparseMatrix, b: SparseMatrix) -> SparseMatrix:
    out: SparseMatrix = []
    for row in a:
        out_row: dict[int, Polynomial] = {}
        for middle, left_poly in row.items():
            for column, right_poly in b[middle].items():
                target = out_row.setdefault(column, {})
                for (di, dj), coefficient in right_poly.items():
                    _poly_add_scaled(target, left_poly, coefficient, (di, dj))
                if not target:
                    out_row.pop(column, None)
        out.append(out_row)
    return out


def _trace_polynomial_power(level: int, power: int, commuting: bool) -> Polynomial:
    matrix = _operator_polynomial(level, commuting)
    current = matrix
    for _ in range(1, power):
        current = _sparse_right_multiply(current, matrix)

    trace: Polynomial = {}
    for row_index, row in enumerate(current):
        diagonal = row.get(row_index)
        if diagonal:
            _poly_add_scaled(trace, diagonal)
    return trace


def _real_delta_polynomial(level: int) -> dict[Exponent, int]:
    noncommuting = _trace_polynomial_power(level, 12, False)
    commuting = _trace_polynomial_power(level, 12, True)
    result: dict[Exponent, int] = {}
    for exponent in set(noncommuting) | set(commuting):
        value = _gadd(noncommuting.get(exponent, ZERO),
                      _gneg(commuting.get(exponent, ZERO)))
        if value[1] != 0:
            raise ArithmeticError(
                f"non-real trace coefficient at level {level}, exponent {exponent}: {value}"
            )
        if value[0] != 0:
            result[exponent] = value[0]
    return result


def _add_into(target: dict[Exponent, int], key: Exponent, value: int) -> None:
    updated = target.get(key, 0) + value
    if updated:
        target[key] = updated
    else:
        target.pop(key, None)


def _linear_combination(
    polynomials: list[tuple[int, dict[Exponent, int]]]
) -> dict[Exponent, int]:
    result: dict[Exponent, int] = {}
    for scalar, polynomial in polynomials:
        for exponent, coefficient in polynomial.items():
            _add_into(result, exponent, scalar * coefficient)
    return result


def _circle_normal_form(polynomial: dict[Exponent, int]) -> dict[Exponent, int]:
    """Reduce s^2 to 1-c^2; output has only s-exponents 0 or 1."""
    result: dict[Exponent, int] = {}
    for (c_power, s_power), coefficient in polynomial.items():
        quotient, remainder = divmod(s_power, 2)
        for k in range(quotient + 1):
            value = coefficient * comb(quotient, k) * (-1 if k % 2 else 1)
            _add_into(result, (c_power + 2 * k, remainder), value)
    return result


def _expected_transition_polynomial() -> dict[Exponent, int]:
    """Expand 96*s^2*(24*c^3*s-59*c^2+48*c*s+492*c-480*s-43)."""
    return {
        (3, 3): 2304,
        (2, 2): -5664,
        (1, 3): 4608,
        (1, 2): 47232,
        (0, 3): -46080,
        (0, 2): -4128,
    }


@lru_cache(maxsize=1)
def p12_finite_transition_circle_normal_form() -> dict[Exponent, int]:
    """Return the exact circle-normal form of Delta_4-4*Delta_3+3*Delta_2.

    This is R_4-R_3 for R_m=Delta_m-3*Delta_(m-1), and uses exact
    sparse polynomial arithmetic over Gaussian integers.
    """
    delta2 = _real_delta_polynomial(2)
    delta3 = _real_delta_polynomial(3)
    delta4 = _real_delta_polynomial(4)
    transition = _linear_combination([(3, delta2), (-4, delta3), (1, delta4)])
    return _circle_normal_form(transition)


def p12_finite_transition_matches_expected() -> bool:
    """Check the exact finite transition against its factored expression."""
    return (
        p12_finite_transition_circle_normal_form()
        == _circle_normal_form(_expected_transition_polynomial())
    )


def evaluate_transition_at_rational_circle_point(c: int, s: int, denominator: int) -> int:
    """Return numerator of E(c/d,s/d) over denominator**12."""
    if c * c + s * s != denominator * denominator:
        raise ValueError("(c/d,s/d) must lie on the unit circle")
    polynomial = p12_finite_transition_circle_normal_form()
    return sum(
        coefficient * c**i * s**j * denominator ** (12 - i - j)
        for (i, j), coefficient in polynomial.items()
    )
