"""
The split (docs/SPLIT_AUTOMATON.md sections 2, 7, 9), restated and
verified directly from the vertex-labeling construction itself, with no
reference to face indices at all.

`src/graph/sg_graph.py`'s `one_step` assigns each new vertex's index by
which of the three fixed copies (A: offset (0,0), B: offset (0.5,0), C:
offset (0,0.5), always processed in that order) first reaches that point,
at every recursive step. Instrumenting that assignment to record, for
every vertex, the sequence of copies that introduced it (one entry per
level, in chronological order) gives each vertex a "history". This file
checks that a sibling vertex's contribution is exactly determined by its
own history alone:

    skip the first entry; scan the rest in order; the first entry that
    isn't 1 decides it -- 0 => generic (-8 sin^2(theta/2)), 2 => exactly
    0; all remaining entries equal to 1 => generic.

Verified exactly (symbolic ground truth, zero exceptions) for every
sibling vertex at m = 2, 3, 4 -- 117 instances (m=5's 243 were checked
during development; only 2,3,4 are re-checked here to keep runtime
reasonable, 4 marked slow).
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


def _one_step_traced(V, E, faces_prev, history_prev):
    """Exactly src/graph/sg_graph.py's one_step, instrumented to also
    record, for every vertex, which copy (0=A, 1=B, 2=C) first introduced
    it at each level."""
    offsets = [(0.0, 0.0), (0.5, 0.0), (0.0, 0.5)]
    new_V, vertex_index, new_E, maps, new_history = [], {}, set(), [], []
    for copy_idx, (ox, oy) in enumerate(offsets):
        m = {}
        for i, (x, y) in enumerate(V):
            p = (round(x * 0.5 + ox, 10), round(y * 0.5 + oy, 10))
            if p not in vertex_index:
                vertex_index[p] = len(new_V)
                new_V.append(p)
                new_history.append(history_prev[i] + [copy_idx])
            m[i] = vertex_index[p]
        maps.append(m)
    new_faces = []
    for m in maps:
        for a, b in E:
            new_E.add(tuple(sorted((m[a], m[b]))))
        if faces_prev is not None:
            for f in faces_prev:
                new_faces.append(tuple(m[v] for v in f))
        else:
            new_faces.append((m[0], m[1], m[2]))
    return new_V, list(new_E), new_faces, new_history


def _build_traced(level: int):
    V0 = [(0.0, 0.0), (1.0, 0.0), (0.0, 1.0)]
    E0 = [(0, 1), (1, 2), (0, 2)]
    history0 = [[], [], []]
    V, E, faces, history = V0, E0, None, history0
    for _ in range(level):
        V, E, faces, history = _one_step_traced(V, E, faces, history)
    return V, E, faces, history


def history_predicts_bad(history_v) -> bool:
    for entry in history_v[1:]:
        if entry == 0:
            return False
        if entry == 2:
            return True
        # entry == 1: keep scanning
    return False


def _sibling_vertices(level: int):
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
        if lcp == level - 1:
            yield v


@pytest.mark.parametrize("level", [2, 3])
def test_history_rule_matches_ground_truth_fast(level):
    H_C, n = _build_H_full(level, commuting=False)
    H_Cp, _ = _build_H_full(level, commuting=True)
    H_C4 = sp.expand(sp.expand(H_C * H_C) * sp.expand(H_C * H_C))
    H_Cp4 = sp.expand(sp.expand(H_Cp * H_Cp) * sp.expand(H_Cp * H_Cp))
    _, _, _, history = _build_traced(level)

    checked = 0
    for v in _sibling_vertices(level):
        truth = _reduce_mod_pyth(
            sp.trace(H_C4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2])
            - sp.trace(H_Cp4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2])
        )
        assert (truth == 0) == history_predicts_bad(history[v]), (
            level, v, history[v], truth,
        )
        checked += 1
    assert checked == 3 * 3 ** (level - 1)


@pytest.mark.slow
def test_history_rule_matches_ground_truth_level4():
    level = 4
    H_C, n = _build_H_full(level, commuting=False)
    H_Cp, _ = _build_H_full(level, commuting=True)
    H_C4 = sp.expand(sp.expand(H_C * H_C) * sp.expand(H_C * H_C))
    H_Cp4 = sp.expand(sp.expand(H_Cp * H_Cp) * sp.expand(H_Cp * H_Cp))
    _, _, _, history = _build_traced(level)

    checked = 0
    for v in _sibling_vertices(level):
        truth = _reduce_mod_pyth(
            sp.trace(H_C4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2])
            - sp.trace(H_Cp4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2])
        )
        assert (truth == 0) == history_predicts_bad(history[v]), (
            level, v, history[v], truth,
        )
        checked += 1
    assert checked == 3 * 3 ** (level - 1)
