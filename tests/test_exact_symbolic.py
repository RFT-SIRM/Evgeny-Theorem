"""
Exact (symbolic) verification of the H^4 trace-defect identity.

Every other test in this suite compares floating-point matrices to the
closed form and accepts agreement to some numerical tolerance (1e-9 to
1e-11; see VERIFICATION.md). This file instead builds H_C and H_C' with
symbolic entries in c = cos(theta/2), s = sin(theta/2) (related by
c**2 + s**2 = 1) and checks that

    Tr(H_C^4) - Tr(H_C'^4) - (-16*(3**(m-1)+1) * s**2)

reduces to *exactly* zero as a polynomial identity in c, after
substituting s**2 -> 1 - c**2. There is no floating point anywhere in
this file and no tolerance parameter: the check is either exactly zero
or the test fails.

This is a strictly stronger statement than "agrees to 1e-9" -- it is an
exact computer-algebra proof of the closed form *for each specific m
tested here*. It is still not a proof for all m (that requires either
an inductive argument or a machine-checked general proof; see
docs/EXACT_VERIFICATION.md for what is and is not established) and it
is not a Lean-checked proof.

Runtime: m=1..4 are fast (well under a second each). m=5,6,7 are marked
slow (roughly 2s, 20s, 70s respectively on the machine this was
written on) and mirror the levels already covered numerically in
VERIFICATION.md.
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
    """exp(-i*theta/2*sigma_axis) with c=cos(theta/2), s=sin(theta/2) as
    free symbols (the relation c**2+s**2=1 is applied later, once, when
    reducing the final scalar expression -- not during matrix building)."""
    return c * _I2 - sp.I * s * _PAULI[axis]


def _build_H_symbolic(level: int, commuting: bool) -> tuple[sp.Matrix, int]:
    """Same construction as operators.build_su2_bundle, but with exact
    symbolic (c, s) rotation matrices instead of floating-point theta."""
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
    return H, n


def _reduce_mod_pyth(expr: sp.Expr) -> sp.Expr:
    """Reduce a polynomial in c, s to a polynomial in c alone, using
    s**2 = 1 - c**2 repeatedly, then simplify. Exact (rational
    arithmetic + sympy simplification); no floating point."""
    expr = sp.expand(expr)
    for _ in range(12):
        reduced = sp.expand(expr.subs(s**2, 1 - c**2))
        if reduced == expr:
            break
        expr = reduced
    return sp.simplify(expr)


def _exact_trace_defect(level: int) -> sp.Expr:
    """Tr(H_C^4) - Tr(H_C'^4), exact, as a reduced polynomial in c."""
    H_C, n = _build_H_symbolic(level, commuting=False)
    H_Cp, _ = _build_H_symbolic(level, commuting=True)
    H_C4 = sp.expand(sp.expand(H_C * H_C) * sp.expand(H_C * H_C))
    H_Cp4 = sp.expand(sp.expand(H_Cp * H_Cp) * sp.expand(H_Cp * H_Cp))
    tr_C = sum(sp.trace(H_C4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2]) for v in range(n))
    tr_Cp = sum(sp.trace(H_Cp4[2 * v : 2 * v + 2, 2 * v : 2 * v + 2]) for v in range(n))
    return _reduce_mod_pyth(tr_C - tr_Cp)


def _closed_form_cs(m: int) -> sp.Expr:
    """-16*(3**(m-1)+1)*sin(theta/2)**2, rewritten in terms of c via
    s**2 = 1 - c**2, and expanded (so it is directly comparable to the
    output of _exact_trace_defect)."""
    return sp.expand((-16 * (sp.Integer(3) ** (m - 1) + 1)) * (1 - c**2))


@pytest.mark.parametrize("m", [1, 2, 3, 4])
def test_trace_defect_exact_fast(m):
    lhs = _exact_trace_defect(m)
    rhs = _closed_form_cs(m)
    assert sp.simplify(lhs - rhs) == 0, f"m={m}: {lhs} != {rhs}"


@pytest.mark.slow
@pytest.mark.parametrize("m", [5, 6, 7])
def test_trace_defect_exact_slow(m):
    lhs = _exact_trace_defect(m)
    rhs = _closed_form_cs(m)
    assert sp.simplify(lhs - rhs) == 0, f"m={m}: {lhs} != {rhs}"


def test_graph_has_exactly_three_degree_two_vertices():
    """Structural fact used throughout docs/EXACT_VERIFICATION.md: SG(m)
    has exactly 3 degree-2 (corner) vertices for every m >= 1; every
    other vertex has degree exactly 4."""
    for level in range(1, 7):
        V, E, _ = sg_tree_graph_with_faces(level)
        deg = [0] * len(V)
        for a, b in E:
            deg[a] += 1
            deg[b] += 1
        from collections import Counter

        counts = Counter(deg)
        assert counts[2] == 3, (level, counts)
        assert counts[4] == len(V) - 3, (level, counts)
        assert set(counts) == {2, 4}, (level, counts)
