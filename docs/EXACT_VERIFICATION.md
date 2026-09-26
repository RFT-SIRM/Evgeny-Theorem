# Exact (symbolic) verification and the structure behind the closed form

## Status

**Established in this note, exactly (computer algebra, not floating point):**
the H⁴ trace-defect closed form in [THEOREM.md](THEOREM.md) holds *exactly*
for `m = 1..7`, and a specific local mechanism that explains *why* the
identity holds is derived and confirmed.

**Now established (see [`PROOF.md`](PROOF.md)):** a complete hand proof for
general `m`. §4 below identifies the gap this note originally left open;
[`SPLIT_AUTOMATON.md`](SPLIT_AUTOMATON.md) resolves it completely (§7–§9),
and [`PROOF.md`](PROOF.md) assembles everything into one induction on `m`.
No Lean proof of the operator-level identity exists yet (see
`formalization/README.md`) — that remains the only missing piece.

This note does not change the status of anything in `THEOREM.md`.

---

## 1. Exact symbolic verification, m = 1..7

`VERIFICATION.md` checks the closed form against direct floating-point
computation, to tolerances between `1e-6` and `1e-11`. That leaves open,
in principle, a systematic error too small to see at double precision.

[`tests/test_exact_symbolic.py`](../tests/test_exact_symbolic.py) removes
floating point entirely: `H_C` and `H_C'` are built with symbolic entries in
`c = cos(θ/2)`, `s = sin(θ/2)`, and

```
Tr(H_C^4) - Tr(H_C'^4)  -  ( -16·(3^(m-1)+1)·s² )
```

is reduced, using only `s² = 1 - c²` and exact rational simplification, to
the literal expression `0`. This is checked for `m = 1, 2, 3, 4` (fast,
seconds) and `m = 5, 6, 7` (`-m slow`, ~2 min total) — the same range as
`VERIFICATION.md`'s refinement-sequence table. There is no tolerance
parameter anywhere in this test: it is either exactly zero or the test
fails.

Reproduce: `pytest tests/test_exact_symbolic.py -v` (add `-m slow` for
`m=5,6,7`).

## 2. A structural fact: exactly 3 corners, everything else degree 4

`SG(m)` has exactly 3 vertices of degree 2 (the outer corners of the whole
figure) and every other vertex has degree exactly 4. Checked directly for
`m = 1..6` in `test_graph_has_exactly_three_degree_two_vertices`. This
follows from the recursive construction (each recursive step turns exactly
3 pairs of degree-2 corners into degree-4 joints, and only the 3 outermost
corners of the whole figure are never glued) but is stated here as a
computationally-checked fact, not (yet) as a Lean-style induction.

## 3. Why locality holds: a linear-algebra derivation

`SG(m)`'s elementary (leaf) triangles share only vertices, never edges
(`src/graph/sg_graph.py`'s own docstring). So every non-corner vertex `v`
belongs to *exactly two* elementary triangles `T1 = {v,a,b}`, `T2 = {v,c,d}`,
and removing `v` disconnects `T1` from `T2`.

Writing `(H^4)_{vv} = [H·(H^2)·H]_{vv}`, the only entries of `H^2` that are
needed are `(H^2)_{x,y}` for `x, y` ranging over `v` and its (≤4) neighbors.
Expanding `(H^2)_{x,y} = Σ_z H_{x,z} H_{z,y}` and using that every edge
matrix `U` is unitary (`U U^† = I`) gives, for a *generic* joint vertex
(all of `a,b,c,d` themselves degree 4, no coincidental extra adjacency):

```
(H^2)_{v,v}   = deg(v)^2 + deg(v)                      (scalar × I, always)
(H^2)_{v,a}   = -deg(v)·U(v,a) - deg(a)·U(v,a) + U(v,b)·U(b,a)     (a in T1)
(H^2)_{a,b}   =  U(a,v)·U(v,b) - (deg(a)+deg(b))·U(a,b)            (a,b in T1)
(H^2)_{a,c}   =  U(a,v)·U(v,c)                          (a in T1, c in T2)
```

Every term on the right involves only the six edges of `T1 ∪ T2` and the
degrees of `v, a, b, c, d` — nothing about what lies beyond `a, b, c, d`.
So `(H^4)_{vv}` is a finite, computable function of `T1`'s and `T2`'s own
SU(2) matrices alone. This is the rigorous version of the "locality"
observed only numerically in an earlier pass (see the git history around
the recursion-in-`m` investigation) — it is a direct consequence of `U`
being unitary and the triangles sharing only a vertex, not a numerical
coincidence, and it holds for *any* θ, not only θ = π/2.

## 4. Vertex types, and the open gap

Every non-corner vertex's two triangles `T1, T2` assign it a role in each
(`flux`: on the triangle's designated rotated edge; `opp`: the vertex
opposite it) and an axis (`i mod 3`, `i` = that triangle's index in the
fixed face-traversal order — 0 under the commuting control `C'` always,
since `C'` fixes every triangle's axis to `z`). Classifying all non-corner
vertices of `SG(1..5)` by the unordered pair `{(role₁,axis₁), (role₂,axis₂)}`
finds exactly **5** interior types, with counts matching simple closed
forms in `m` (verified `m=1..5`; not proved by induction here):

| type | pattern | count |
|---|---|---|
| FF | `{(flux,0),(flux,1)}` | `(3^m − 1)/2` |
| FO₀ | `{(flux,0),(opp,2)}` | `(3^(m−1) − 1)/2` |
| FO₁ | `{(flux,1),(opp,2)}` | `(3^(m−1) − 1)/2` |
| OF₀ | `{(flux,2),(opp,0)}` | `3^(m−1)` |
| OF₁ | `{(flux,2),(opp,1)}` | `3^(m−1)` |

(plus the 3 corners, one of each of `(flux,0)`, `(flux,1)`, `(opp,2)`).
These counts, plus the 3 corners, sum to `n(m)` exactly, as a check.

Using the exact §1/§3 machinery, each type's *local* contribution to
`Tr(H_C^4) − Tr(H_C'^4)` was computed directly at `m=2,3` (small enough to
enumerate every instance):

| type | local Δ | corner Δ |
|---|---|---|
| FO₀ | `−4 sin²(θ/2)` (every instance checked) | `(flux,0)` / `(flux,1)`: `−4 sin²(θ/2)` |
| FO₁ | `+4 sin²(θ/2)` (every instance checked) | `(opp,2)`: `0` |
| FF, OF₀, OF₁ | `−8 sin²(θ/2)` **or exactly `0`**, depending on the instance | |

FO₀, FO₁ and the 3 corner types are fully explained by the §3 mechanism
alone — every instance checked gives the same value. **FF, OF₀ and OF₁ are
not**: at `m = 2` already, some instances give `−8 sin²(θ/2)` and others
give exactly `0`, and the split is not explained by role+axis alone — it
depends on something at least one recursion level deeper (confirmed: a
finer signature built from the roles/axes of each triangle's *other two*
vertices' own second triangle still does not cleanly separate the two
cases; see the investigation referenced from the commit that adds this
file). All totals still check out exactly (§1) because the split's two
values happen to sum correctly, but the *rule* for which instances get
which value — as a function of `m` and position, for all `m` — is not
yet identified.

**Update:** the exact rule behind this split has since been found and
verified exhaustively (360 instances, `m` up to 5, zero exceptions) — see
[`SPLIT_AUTOMATON.md`](SPLIT_AUTOMATON.md), which also shows it
algebraically reproduces `Δ_m(θ)` for general `m`. What's left is an
induction proof of that rule itself (not yet done) and, after that, the
Lean translation for `TraceDefectIdentity`
(`formalization/EvgenyTheorem.lean`).

## Reproduce

```bash
pytest tests/test_exact_symbolic.py -v            # m=1..4, seconds
pytest tests/test_exact_symbolic.py -v -m slow     # m=5,6,7, ~2 min
```
