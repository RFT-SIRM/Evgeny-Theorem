"""Exact symbolic certificate for the level-three p=6 orientation gap.

The vertex/face order comes from the repository's shared SG graph builder.
Write c = cos(theta/2), s = sin(theta/2). Every matrix entry is represented
as a polynomial in c,s with Gaussian-integer coefficients, so no floating
point arithmetic is used.

For F(3) = D_num(3) - D_til(3), the raw polynomial is
    -6192*s^2 - 144*c^2*s^2 - 144*s^4 - 864*s^3.
Using c^2+s^2=1, this is -6336*s^2 - 864*s^3.
This is an exact finite-level calculation, not a Lean proof of the general
all-level theorem.
"""
from __future__ import annotations

from graph.sg_graph import sg_tree_graph_with_faces

Gaussian = tuple[int, int]
Monomial = tuple[int, int]  # powers of c and s
Polynomial = dict[Monomial, Gaussian]
Block = list[list[Polynomial]]
ZERO: Gaussian = (0, 0)
PZERO: Polynomial = {}


def _gadd(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0] + b[0], a[1] + b[1])


def _gneg(a: Gaussian) -> Gaussian:
    return (-a[0], -a[1])


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


def _pneg(a: Polynomial) -> Polynomial:
    return {mon: _gneg(z) for mon, z in a.items()}


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
    return [[_padd(a[i][j], b[i][j]) for j in range(2)] for i in range(2)]


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
    """The forward operator block -U, with U = c I - i s sigma_axis."""
    neg_c: Polynomial = {(1, 0): (-1, 0)}
    if axis == 0:  # sigma_x
        off: Polynomial = {(0, 1): (0, 1)}
        return [[neg_c, off], [off, neg_c]]
    if axis == 1:  # sigma_y
        return [[neg_c, {(0, 1): (1, 0)}],
                [{(0, 1): (-1, 0)}, neg_c]]
    return [[_padd(neg_c, {(0, 1): (0, 1)}), {}],
            [{}, _padd(neg_c, {(0, 1): (0, -1)})]]


def trace_polynomial(level: int, commuting: bool,
                     flip_corner: bool = False) -> Polynomial:
    """Exact polynomial for Tr(H^6) at the requested orientation.

    commuting=False cycles x/y/z over the face list; True uses z.
    flip_corner reverses the flux edge ((2**level-1, 0), (2**level, 0)),
    exactly the exceptional edge in oTil after scaling the unit triangle.
    """
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
    corner_points = {
        (round((2**level - 1) / (2**level), 10), 0.0),
        (1.0, 0.0),
    }
    corner = tuple(sorted(vertices.index(p) for p in corner_points))
    if corner not in flux_axes:
        raise ValueError("The exceptional corner edge is not a flux edge")

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
            if flip_corner and key == corner:
                forward, reverse = reverse, forward
        else:
            forward = [[_pconst((-1, 0)), {}],
                       [{}, _pconst((-1, 0))]]
            reverse = forward
        rows[a][b] = forward
        rows[b][a] = reverse

    # Multiply sparse vertex-block rows by the base matrix five times.
    power = rows
    for _ in range(5):
        product: list[dict[int, Block]] = [dict() for _ in range(n)]
        for i, row in enumerate(power):
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
        power = product

    trace: Polynomial = {}
    for i, row in enumerate(power):
        diagonal = row.get(i, _block_zero())
        trace = _padd(trace, diagonal[0][0])
        trace = _padd(trace, diagonal[1][1])
    if any(z[1] for z in trace.values()):
        raise ArithmeticError("The symbolic trace has a nonzero imaginary part")
    return {mon: z for mon, z in trace.items() if z[0]}


def orientation_gap_polynomial(level: int = 3) -> Polynomial:
    """Return F(level) = D_num(level) - D_til(level) as an exact polynomial."""
    terms = [
        (1, trace_polynomial(level, False, False)),
        (-1, trace_polynomial(level, False, True)),
        (-1, trace_polynomial(level, True, False)),
        (1, trace_polynomial(level, True, True)),
    ]
    result: Polynomial = {}
    for sign, polynomial in terms:
        for mon, z in polynomial.items():
            signed = z if sign == 1 else _gneg(z)
            result = _padd(result, {mon: signed})
    return {mon: z for mon, z in result.items() if z != ZERO}


def evaluate_polynomial(poly: Polynomial, c: int, s: int) -> int:
    """Evaluate at exact integer c,s values (e.g. theta=0 or theta=pi)."""
    value = 0
    for (pc, ps), coefficient in poly.items():
        if coefficient[1]:
            raise ValueError("Expected real coefficients")
        value += coefficient[0] * c**pc * s**ps
    return value


if __name__ == "__main__":
    gap = orientation_gap_polynomial(3)
    print("Raw F(3) polynomial:", gap)
    print("F(3) at theta=pi:", evaluate_polynomial(gap, c=0, s=1))
