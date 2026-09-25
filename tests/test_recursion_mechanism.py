"""
The m-to-(m-1) recursion Δ_m = 3·Δ_{m-1} + 32·sin²(θ/2)
(docs/SPLIT_AUTOMATON.md section 10), explained via section 9's history
rule: the additive constant is fixed because the number of "still
inconclusive" sibling vertices (history = [x, 1, 1, ..., 1] for some x,
then all 1s) is exactly 3 at every level -- not merely at the level where
the recursion was first spotted.

This is a pure graph-construction fact (no SU(2) matrices needed): it
instruments src/graph/sg_graph.py's one_step exactly as
tests/test_history_automaton.py does, and just counts. Cheap enough to
check well beyond the levels used in the symbolic tests elsewhere in this
suite.
"""
from graph.sg_graph import sg_tree_graph_with_faces


def _one_step_traced(V, E, faces_prev, history_prev):
    """Exactly src/graph/sg_graph.py's one_step, instrumented to record
    which copy (0=A, 1=B, 2=C) introduced each vertex, per level."""
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


def _count_inconclusive_siblings(level: int) -> int:
    V, E, faces, history = _build_traced(level)
    n = len(V)
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

    count = 0
    for v in range(n):
        fidx = incident[v]
        if len(fidx) != 2:
            continue  # corners have only one incident face
        f1, f2 = fidx
        d1, d2 = digits(f1, level), digits(f2, level)
        lcp = 0
        for x, y in zip(d1, d2):
            if x == y:
                lcp += 1
            else:
                break
        if lcp != level - 1:
            continue  # only true sibling (FF/OF0/OF1) vertices
        if all(d == 1 for d in history[v][1:]):
            count += 1
    return count


def test_inconclusive_sibling_count_is_always_three():
    for level in [2, 3, 4, 5, 6, 7, 8, 9, 10]:
        assert _count_inconclusive_siblings(level) == 3, level
