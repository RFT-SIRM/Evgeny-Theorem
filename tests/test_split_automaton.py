"""
Exact characterization of the FF / OF0 / OF1 "split" flagged as an open
gap in docs/EXACT_VERIFICATION.md.

Three of the five interior vertex types (FF, OF0, OF1 in that note's
naming) do not have a single fixed local contribution: some instances
give exactly -8*sin(theta/2)**2 (the "generic" value), others give
exactly 0. This file defines the exact rule that determines which,
and checks it -- exactly, symbolically, no floating point -- against
every single relevant vertex at m = 2, 3, 4, 5 (360 instances total,
zero exceptions found during development).

The rule (see docs/SPLIT_AUTOMATON.md for the derivation and the
counting argument that turns this into a full re-derivation of the
closed form for general m):

A vertex of one of these three types is either a "sibling" vertex
(shared between two of the three finest sibling triangles under some
shared (m-1)-digit prefix of their face indices, in base 3) or a
"deep" vertex (its two triangles diverge earlier than the last digit).
Deep vertices always take the generic value. Sibling vertices are
governed by a 3-state automaton reading the shared prefix from its
LAST digit (finest / oldest recursive choice) to its FIRST (coarsest
/ newest): start in state Neutral; on reading a 0, move to (absorbing)
Good; on reading a 2, move to (absorbing) Bad; on reading a 1, stay in
the current state. A prefix of all 1s ends in Neutral, treated as
Good. The vertex's value is generic (-8 sin^2(theta/2)) unless the
final state is Bad, in which case it is exactly 0.

This is presented as an exactly-verified rule, not (yet) as an
induction proof of the rule itself -- see the note for exactly what
that would still require.
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


def _su2_rotation_cs(axis: int) -> sp.Matrix:
    return c * _I2 - sp.I * s * _PAULI[axis]


def _build_H_symbolic(level: int, commuting: bool):
    V, E, faces = sg_tree_graph_with_faces(level)
    n = len(V)
    deg = [0] * n
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    U_of = {}
    for a, b in E:
        e = (a, b) if a < b else (b, a)
        U_of[e] = _I2
    for idx, (a, b, _c) in enumerate(faces):
        axis = 2 if commuting else (idx % 3)
        e = (a, b) if a < b else (b, a)
        U_of[e] = _su2_rotation_cs(axis)
    dim = 2 * n
    H = sp.zeros(dim, dim)
    for x in range(n):
        H[2 * x : 2 * x + 2, 2 * x : 2 * x + 2] = deg[x] * _I2
    for (a, b), U in U_of.items():
        H[2 * a : 2 * a + 2, 2 * b : 2 * b + 2] += -U
        H[2 * b : 2 * b + 2, 2 * a : 2 * a + 2] += -U.conjugate().T
    return H, n, faces


def _reduce_mod_pyth(expr: sp.Expr) -> sp.Expr:
    expr = sp.expand(expr)
    for _ in range(12):
        reduced = sp.expand(expr.subs(s**2, 1 - c**2))
        if reduced == expr:
            break
        expr = reduced
    return sp.simplify(expr)


def _digits(idx: int, m: int) -> tuple[int, ...]:
    d = []
    for _ in range(m):
        d.append(idx % 3)
        idx //= 3
    return tuple(reversed(d))


def automaton_predict(prefix: tuple[int, ...]) -> str:
    """The rule described in the module docstring. Returns 'generic'
    or 'bad' (bad => contribution is exactly 0)."""
    state = "N"
    for d in reversed(prefix):
        if state != "N":
            break
        if d == 0:
            state = "G"
        elif d == 2:
            state = "B"
    return "bad" if state == "B" else "generic"


def _sibling_vertices_with_prefix(level: int):
    """Yield (vertex, shared_prefix) for every non-corner vertex whose
    two incident faces share every digit except the last (i.e. are two
    of the three finest sibling triangles under that prefix)."""
    _, _, faces = sg_tree_graph_with_faces(level)
    n = max(max(f) for f in faces) + 1
    incident = {i: [] for i in range(n)}
    for idx, (a, b, cc) in enumerate(faces):
        incident[a].append(idx)
        incident[b].append(idx)
        incident[cc].append(idx)
    for v in range(n):
        fidx = incident[v]
        if len(fidx) != 2:
            continue
        d1, d2 = _digits(fidx[0], level), _digits(fidx[1], level)
        lcp = 0
        for x, y in zip(d1, d2):
            if x == y:
                lcp += 1
            else:
                break
        if lcp == level - 1:
            yield v, d1[:lcp]


@pytest.mark.parametrize("level", [2, 3])
def test_automaton_matches_exact_trace_fast(level):
    H_C, n, faces = _build_H_symbolic(level, commuting=False)
    H_Cp, _, _ = _build_H_symbolic(level, commuting=True)
    H_C4 = sp.expand(sp.expand(H_C * H_C) * sp.expand(H_C * H_C))
    H_Cp4 = sp.expand(sp.expand(H_Cp * H_Cp) * sp.expand(H_Cp * H_Cp))

    checked = 0
    for v, prefix in _sibling_vertices_with_prefix(level):
        block_C = H_C4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2]
        block_Cp = H_Cp4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2]
        diff = _reduce_mod_pyth(sp.trace(block_C) - sp.trace(block_Cp))
        predicted_bad = automaton_predict(prefix) == "bad"
        assert (diff == 0) == predicted_bad, (level, v, prefix, diff)
        checked += 1
    assert checked == 3 * 3 ** (level - 1)  # one FF + one OF0 + one OF1 per prefix


@pytest.mark.slow
@pytest.mark.parametrize("level", [4, 5])
def test_automaton_matches_exact_trace_slow(level):
    H_C, n, faces = _build_H_symbolic(level, commuting=False)
    H_Cp, _, _ = _build_H_symbolic(level, commuting=True)
    H_C4 = sp.expand(sp.expand(H_C * H_C) * sp.expand(H_C * H_C))
    H_Cp4 = sp.expand(sp.expand(H_Cp * H_Cp) * sp.expand(H_Cp * H_Cp))

    checked = 0
    for v, prefix in _sibling_vertices_with_prefix(level):
        block_C = H_C4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2]
        block_Cp = H_Cp4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2]
        diff = _reduce_mod_pyth(sp.trace(block_C) - sp.trace(block_Cp))
        predicted_bad = automaton_predict(prefix) == "bad"
        assert (diff == 0) == predicted_bad, (level, v, prefix, diff)
        checked += 1
    assert checked == 3 * 3 ** (level - 1)


def test_bad_prefix_count_matches_closed_form():
    """Exact count of 'bad' (m-1)-digit prefixes is (3**(m-1)-1)//2 --
    a direct consequence of the automaton (a string is bad iff it is
    1^k 2 (anything)^{L-k-1} for some k), checked here by brute force
    for small L rather than assumed."""
    for L in range(0, 8):
        import itertools

        bad = sum(
            1
            for p in itertools.product([0, 1, 2], repeat=L)
            if automaton_predict(p) == "bad"
        )
        assert bad == (3**L - 1) // 2, L
