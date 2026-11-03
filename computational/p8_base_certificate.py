"""Exact symbolic finite-level certificate for the H8 base transition.

Write c = cos(theta/2), s = sin(theta/2). Matrix entries are polynomials
in c,s with Gaussian-integer coefficients. This module computes the exact
trace defects D_2, D_3, D_4 and verifies
    D_3 - 3 D_2 = D_4 - 3 D_3 = C_8(theta).
No floating-point arithmetic is used in the certificate.
"""
from __future__ import annotations

from functools import lru_cache
from typing import TypeAlias

from graph.sg_graph import sg_tree_graph_with_faces

Gaussian: TypeAlias = tuple[int, int]
Monomial: TypeAlias = tuple[int, int]
Polynomial: TypeAlias = dict[Monomial, Gaussian]
Block: TypeAlias = list[list[Polynomial]]

ZERO: Gaussian = (0, 0)


def _gadd(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0] + b[0], a[1] + b[1])


def _gmul(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0])


def _pconst(z: Gaussian) -> Polynomial:
    return {} if z == ZERO else {(0, 0): z}


def _padd(a: Polynomial, b: Polynomial) -> Polynomial:
    out = dict(a)
    for mon, z in b.items():
        value = _gadd(out.get(mon, ZERO), z)
        if value == ZERO:
            out.pop(mon, None)
        else:
            out[mon] = value
    return out


def _pmul(a: Polynomial, b: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for (ac, ass), za in a.items():
        for (bc, bs), zb in b.items():
            mon = (ac + bc, ass + bs)
            value = _gadd(out.get(mon, ZERO), _gmul(za, zb))
            if value == ZERO:
                out.pop(mon, None)
            else:
                out[mon] = value
    return out


def _block_zero() -> Block:
    return [[{}, {}], [{}, {}]]


def _block_add(a: Block, b: Block) -> Block:
    return [[_padd(a[i][j], b[i][j]) for j in range(2)]
            for i in range(2)]


def _block_mul(a: Block, b: Block) -> Block:
    return [
        [_padd(_pmul(a[i][0], b[0][j]), _pmul(a[i][1], b[1][j]))
         for j in range(2)]
        for i in range(2)
    ]


def _block_dagger(a: Block) -> Block:
    return [
        [{mon: (z[0], -z[1]) for mon, z in a[j][i].items()}
         for j in range(2)]
        for i in range(2)
    ]


def _axis_edge_block(axis: int) -> Block:
    """Forward operator block -U, with U = c I - i s sigma_axis."""
    neg_c: Polynomial = {(1, 0): (-1, 0)}
    if axis == 0:
        off: Polynomial = {(0, 1): (0, 1)}
        return [[neg_c, off], [off, neg_c]]
    if axis == 1:
        return [[neg_c, {(0, 1): (1, 0)}],
                [{(0, 1): (-1, 0)}, neg_c]]
    return [[_padd(neg_c, {(0, 1): (0, 1)}), {}],
            [{}, _padd(neg_c, {(0, 1): (0, -1)})]]


def trace_polynomial(level: int, commuting: bool,
                     power: int = 8) -> Polynomial:
    """Return exact Tr(H^power); orientation is the vertex-index ordering."""
    if level < 1:
        raise ValueError("level must be at least one")
    if power < 1:
        raise ValueError("power must be positive")

    vertices, edges, faces = sg_tree_graph_with_faces(level)
    n = len(vertices)
    degree = [0] * n
    for a, b in edges:
        degree[a] += 1
        degree[b] += 1
    flux_axes = {
        tuple(sorted((a, b))): (2 if commuting else i % 3)
        for i, (a, b, _c) in enumerate(faces)
    }

    rows: list[dict[int, Block]] = [dict() for _ in range(n)]
    for v, d in enumerate(degree):
        rows[v][v] = [[_pconst((d, 0)), {}],
                      [{}, _pconst((d, 0))]]
    for edge in edges:
        a, b = sorted(edge)
        key = (a, b)
        if key in flux_axes:
            forward = _axis_edge_block(flux_axes[key])
            reverse = _block_dagger(forward)
        else:
            forward = [[_pconst((-1, 0)), {}],
                       [{}, _pconst((-1, 0))]]
            reverse = forward
        rows[a][b] = forward
        rows[b][a] = reverse

    power_rows = rows
    for _ in range(power - 1):
        product: list[dict[int, Block]] = [dict() for _ in range(n)]
        for i, row in enumerate(power_rows):
            accum: dict[int, Block] = {}
            for k, left in row.items():
                for j, right in rows[k].items():
                    term = _block_mul(left, right)
                    accum[j] = (_block_add(accum[j], term)
                                if j in accum else term)
            product[i] = {
                j: block for j, block in accum.items()
                if any(block[r][c] for r in range(2) for c in range(2))
            }
        power_rows = product

    trace: Polynomial = {}
    for i, row in enumerate(power_rows):
        diagonal = row.get(i, _block_zero())
        trace = _padd(trace, diagonal[0][0])
        trace = _padd(trace, diagonal[1][1])
    if any(z[1] for z in trace.values()):
        raise ArithmeticError("the symbolic trace has a nonzero imaginary part")
    return {mon: z for mon, z in trace.items() if z[0]}


def _combine_polynomials(terms: list[tuple[int, Polynomial]]) -> Polynomial:
    result: Polynomial = {}
    for sign, polynomial in terms:
        for monomial, coefficient in polynomial.items():
            old = result.get(monomial, ZERO)
            value = (old[0] + sign * coefficient[0],
                     old[1] + sign * coefficient[1])
            if value == ZERO:
                result.pop(monomial, None)
            else:
                result[monomial] = value
    return result


def trace_defect_polynomial(level: int, power: int = 8) -> Polynomial:
    return _combine_polynomials([
        (1, trace_polynomial(level, commuting=False, power=power)),
        (-1, trace_polynomial(level, commuting=True, power=power)),
    ])


def reduce_unit_circle(polynomial: Polynomial) -> Polynomial:
    """Canonicalize c^2 = 1 - s^2 using exact integer arithmetic."""
    result = dict(polynomial)
    while any(pc >= 2 for pc, _ps in result):
        pc, ps = next((pc, ps) for pc, ps in result if pc >= 2)
        coefficient = result.pop((pc, ps))
        for target, sign in (((pc - 2, ps), 1),
                             ((pc - 2, ps + 2), -1)):
            old = result.get(target, ZERO)
            value = (old[0] + sign * coefficient[0],
                     old[1] + sign * coefficient[1])
            if value == ZERO:
                result.pop(target, None)
            else:
                result[target] = value
    return result


def evaluate_polynomial(polynomial: Polynomial, c: int, s: int) -> int:
    value = 0
    for (pc, ps), coefficient in polynomial.items():
        if coefficient[1]:
            raise ValueError("expected a real polynomial")
        value += coefficient[0] * c**pc * s**ps
    return value


@lru_cache(maxsize=1)
def exact_base_transition_certificate() -> dict[str, Polynomial]:
    """Exact D2,D3,D4 and C8 = D3-3D2 = D4-3D3."""
    d2 = trace_defect_polynomial(2, 8)
    d3 = trace_defect_polynomial(3, 8)
    d4 = trace_defect_polynomial(4, 8)
    residual2 = _combine_polynomials([(1, d3), (-3, d2)])
    residual3 = _combine_polynomials([(1, d4), (-3, d3)])
    if residual2 != residual3:
        raise ArithmeticError("the exact H8 base residuals do not agree")
    return {
        "D2": d2,
        "D3": d3,
        "D4": d4,
        "C8": residual2,
        "R2": residual2,
        "R3": residual3,
        "D2_reduced": reduce_unit_circle(d2),
        "D3_reduced": reduce_unit_circle(d3),
        "D4_reduced": reduce_unit_circle(d4),
        "C8_reduced": reduce_unit_circle(residual2),
    }
