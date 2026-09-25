"""
The sibling-vertex value, reproduced exactly from a BOUNDED (6-vertex)
local formula -- no automaton, no unbounded prefix scan.

docs/SPLIT_AUTOMATON.md sections 2-6 found and verified an exact 3-state
automaton for whether a sibling vertex's contribution is the generic
`-8 sin^2(theta/2)` or exactly `0`, but could not explain, from the
operator algebra, why the answer needed to depend on an unboundedly long
prefix. This file resolves that: it re-derives `(H^2)` on `v`'s closed
neighborhood directly from T1, T2 and the third sibling triangle T3
(section 5), *correctly handling the min/max edge-storage direction*
(operators.py stores each edge's SU(2) matrix once, for the
(min(x,y), max(x,y)) direction, and takes the Hermitian conjugate for the
reverse direction) -- and checks that this bounded, 6-vertex-local formula
exactly reproduces the true value for every sibling vertex.

Verified exactly (symbolic, zero exceptions) for every sibling vertex at
m = 2, 3, 4 (117 instances total) against the automaton's own prediction,
which was itself verified against the ground truth in
test_split_automaton.py.

What this shows: the apparent need to scan an unboundedly long prefix was
an artifact of an incompletely-specified formula, not a real feature of
the underlying operator algebra. The true dependence is entirely local
(T1, T2, T3 -- six vertices) *once edge directions are handled correctly*.
What is not yet reduced to a simple closed rule: stating, from the
recursive graph construction alone (without querying actual integer
vertex labels), which of each pair {v,a}, {v,b}, {v,d}, {b,d}, etc. gets
the smaller label -- i.e. an explicit combinatorial description of
sg_tree_graph_with_faces's own labeling order. `b < d` and `v < c` held in
every one of the 81 level-4 instances checked; the other three comparisons
varied. This is now a finite fact about a labeling algorithm, not an open
question about the operator identity.
"""
import sympy as sp
import pytest

from graph.sg_graph import sg_tree_graph_with_faces

c, s = sp.symbols("c s", real=True)
_I2 = sp.eye(2)
_SX = sp.Matrix([[0, 1], [1, 0]])
_SY = sp.Matrix([[0, -sp.I], [sp.I, 0]])
_SZ = sp.Matrix([[1, 0], [0, -1]])
_PAULI = [_SX, _SY, _SZ]


def _rot(axis: int) -> sp.Matrix:
    return c * _I2 - sp.I * s * _PAULI[axis]


def _dag(M: sp.Matrix) -> sp.Matrix:
    return M.conjugate().T


def _reduce_mod_pyth(expr: sp.Expr) -> sp.Expr:
    expr = sp.expand(expr)
    for _ in range(12):
        reduced = sp.expand(expr.subs(s**2, 1 - c**2))
        if reduced == expr:
            break
        expr = reduced
    return sp.simplify(expr)


def _U_xy(faces, faceidx: int, x: int, y: int, commuting: bool) -> sp.Matrix:
    """The matrix U such that H_{x,y} = -U, respecting operators.py's
    min/max edge-storage convention (a single SU(2) matrix is stored per
    edge, for the (min, max) direction; H_{max,min} uses its dagger)."""
    fa, fb, fc = faces[faceidx]
    flux = tuple(sorted((fa, fb)))
    axis = 2 if commuting else (faceidx % 3)
    base = _rot(axis) if tuple(sorted((x, y))) == flux else _I2
    return base if x < y else _dag(base)


def _sibling_vertices_with_locals(level: int):
    """Yield (v, a, b, c, d, e, f1, f2, f3) for every sibling vertex: T1 =
    {v,a,b}, T2 = {v,c,d}, T3 = {b,d,e} is the third sibling triangle
    (SPLIT_AUTOMATON.md section 5)."""
    _, E, faces = sg_tree_graph_with_faces(level)
    n = max(max(f) for f in faces) + 1
    adj = {i: set() for i in range(n)}
    for x, y in E:
        adj[x].add(y)
        adj[y].add(x)
    incident = {i: [] for i in range(n)}
    for idx, (x, y, z) in enumerate(faces):
        incident[x].append(idx)
        incident[y].append(idx)
        incident[z].append(idx)

    def digits(idx, m):
        d = []
        for _ in range(m):
            d.append(idx % 3)
            idx //= 3
        return tuple(reversed(d))

    for v in range(n):
        fidx = incident[v]
        if len(fidx) != 2:
            continue
        f1, f2 = fidx
        d1, d2 = digits(f1, level), digits(f2, level)
        lcp = 0
        for x, y in zip(d1, d2):
            if x == y:
                lcp += 1
            else:
                break
        if lcp != level - 1:
            continue
        others1 = [x for x in faces[f1] if x != v]
        others2 = [x for x in faces[f2] if x != v]
        cross = None
        for p in others1:
            for q in others2:
                if q in adj[p]:
                    cross = (p, q)
        a = [x for x in others1 if x != cross[0]][0]
        b = cross[0]
        cc = [x for x in others2 if x != cross[1]][0]
        d = cross[1]
        f3 = next(idx for idx in incident[b] if idx in incident[d])
        e = [x for x in faces[f3] if x not in (b, d)][0]
        yield v, a, b, cc, d, e, f1, f2, f3, adj


def _bounded_prediction(level: int, v: int, commuting: bool) -> sp.Expr:
    """(H^4)_{vv}, computed using ONLY T1={v,a,b}, T2={v,c,d} and the
    third sibling triangle T3={b,d,e} -- six vertices total, no reference
    to anything else in the graph except their real degrees."""
    _, E, faces = sg_tree_graph_with_faces(level)
    n = max(max(f) for f in faces) + 1
    deg = {i: 0 for i in range(n)}
    for x, y in E:
        deg[x] += 1
        deg[y] += 1

    v_, a, b, cc, d, e, f1, f2, f3, _adj = next(
        item for item in _sibling_vertices_with_locals(level) if item[0] == v
    )

    dv, da, db, dc, dd = deg[v], deg[a], deg[b], deg[cc], deg[d]
    Uva = _U_xy(faces, f1, v, a, commuting)
    Uvb = _U_xy(faces, f1, v, b, commuting)
    Uab = _U_xy(faces, f1, a, b, commuting)
    Uvc = _U_xy(faces, f2, v, cc, commuting)
    Uvd = _U_xy(faces, f2, v, d, commuting)
    Ucd = _U_xy(faces, f2, cc, d, commuting)
    Ubd = _U_xy(faces, f3, b, d, commuting)
    Ube = _U_xy(faces, f3, b, e, commuting)
    Ude = _U_xy(faces, f3, d, e, commuting)

    H2 = {
        ("v", "v"): (dv**2 + dv) * _I2,
        ("a", "a"): (da**2 + da) * _I2,
        ("b", "b"): (db**2 + db) * _I2,
        ("c", "c"): (dc**2 + dc) * _I2,
        ("d", "d"): (dd**2 + dd) * _I2,
        ("v", "a"): -dv * Uva - da * Uva + Uvb * _dag(Uab),
        ("v", "b"): -dv * Uvb - db * Uvb + Uva * Uab,
        ("v", "c"): -dv * Uvc - dc * Uvc + Uvd * _dag(Ucd),
        ("v", "d"): -dv * Uvd - dd * Uvd + Uvc * Ucd,
        ("a", "b"): _dag(Uva) * Uvb - (da + db) * Uab,
        ("c", "d"): _dag(Uvc) * Uvd - (dc + dd) * Ucd,
        ("a", "c"): _dag(Uva) * Uvc,
        ("a", "d"): _dag(Uva) * Uvd + Uab * Ubd,
        ("b", "c"): _dag(Uvb) * Uvc + Ubd * _dag(Ucd),
        ("b", "d"): _dag(Uvb) * Uvd + Ube * Ude - (db + dd) * Ubd,
    }
    for (x, y) in list(H2.keys()):
        if x != y:
            H2[(y, x)] = _dag(H2[(x, y)])

    labels = ["v", "a", "b", "c", "d"]
    Hv = {"v": dv * _I2, "a": -Uva, "b": -Uvb, "c": -Uvc, "d": -Uvd}
    total = sp.zeros(2, 2)
    for x1 in labels:
        for x3 in labels:
            total += Hv[x1] * H2[(x1, x3)] * _dag(Hv[x3])
    return sp.trace(total)


def _build_H_full(level: int, commuting: bool):
    _, E, faces = sg_tree_graph_with_faces(level)
    n = max(max(f) for f in faces) + 1
    deg = {i: 0 for i in range(n)}
    for x, y in E:
        deg[x] += 1
        deg[y] += 1
    U_of = {}
    for x, y in E:
        e = (x, y) if x < y else (y, x)
        U_of[e] = _I2
    for idx, (x, y, _z) in enumerate(faces):
        axis = 2 if commuting else (idx % 3)
        e = (x, y) if x < y else (y, x)
        U_of[e] = _rot(axis)
    dim = 2 * n
    H = sp.zeros(dim, dim)
    for x in range(n):
        H[2 * x : 2 * x + 2, 2 * x : 2 * x + 2] = deg[x] * _I2
    for (x, y), U in U_of.items():
        H[2 * x : 2 * x + 2, 2 * y : 2 * y + 2] += -U
        H[2 * y : 2 * y + 2, 2 * x : 2 * x + 2] += -_dag(U)
    return H, n


@pytest.mark.parametrize("level", [2, 3])
def test_bounded_formula_matches_ground_truth_fast(level):
    H_C, n = _build_H_full(level, commuting=False)
    H_Cp, _ = _build_H_full(level, commuting=True)
    H_C4 = sp.expand(sp.expand(H_C * H_C) * sp.expand(H_C * H_C))
    H_Cp4 = sp.expand(sp.expand(H_Cp * H_Cp) * sp.expand(H_Cp * H_Cp))

    checked = 0
    for v, *_ in _sibling_vertices_with_locals(level):
        truth = _reduce_mod_pyth(
            sp.trace(H_C4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2])
            - sp.trace(H_Cp4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2])
        )
        bounded = _reduce_mod_pyth(
            _bounded_prediction(level, v, False) - _bounded_prediction(level, v, True)
        )
        assert bounded == truth, (level, v, bounded, truth)
        checked += 1
    assert checked == 3 * 3 ** (level - 1)


@pytest.mark.slow
def test_bounded_formula_matches_ground_truth_level4():
    level = 4
    H_C, n = _build_H_full(level, commuting=False)
    H_Cp, _ = _build_H_full(level, commuting=True)
    H_C4 = sp.expand(sp.expand(H_C * H_C) * sp.expand(H_C * H_C))
    H_Cp4 = sp.expand(sp.expand(H_Cp * H_Cp) * sp.expand(H_Cp * H_Cp))

    checked = 0
    for v, *_ in _sibling_vertices_with_locals(level):
        truth = _reduce_mod_pyth(
            sp.trace(H_C4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2])
            - sp.trace(H_Cp4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2])
        )
        bounded = _reduce_mod_pyth(
            _bounded_prediction(level, v, False) - _bounded_prediction(level, v, True)
        )
        assert bounded == truth, (level, v, bounded, truth)
        checked += 1
    assert checked == 3 * 3 ** (level - 1)
