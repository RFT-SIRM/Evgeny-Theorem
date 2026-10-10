# Plan for the general-`m` proof (replaces the Lean-related part of `PROOF.md` §3–§5)

Status of the facts below: every numbered claim is checked numerically by
`tests/general_m_structure_check.py` (levels as stated); **none is proved yet**.
`traceDefect_one` (m = 1) is the only Lean-proved case so far.

Notation: `H = D − A`, `D = diag(deg)⊗1`, `A` = connection adjacency (2×2 blocks, unitary on
edges, zero diagonal). `s = sin(θ/2)`, `c = cos(θ/2)`. `H'`, `A'`: all flux axes equal to `z`.

## Reduction (valid for any flux-edge orientation)

1. **`Δ = Tr A⁴ − Tr A'⁴`.** The `D`-terms and the 3-cycle terms (`Tr D A³`) are axis-independent
   (a rotation about any axis has trace `2c`; each 3-cycle contains at most one flux edge).
   Checked m = 1..3.
2. **`Tr A⁴ = Σ_{v,w} ‖(A²)_{vw}‖²_F`**, `(A²)_{vv} = deg(v)·1` (unitarity — already in Lean:
   `axisRotation_unitary`, `Locality.lean`). For `v ≠ w`, `(A²)_{vw}` is a sum over common
   neighbours of unitaries. Any two distinct vertices of `SG(m)` have **at most 2 common
   neighbours** (checked m ≤ 3). With one common neighbour the norm is `2` for every connection;
   with two (rhombus diagonals) it is `4 + 2 Re tr(hol of the rhombus)`.
3. Hence `Δ = 8 Σ_{rhombi R} (Re tr hol_R − Re tr hol'_R)`. Each 6-vertex cell contains 3
   rhombi; exactly 2 carry flux edges: `X–Z` and `Y–Z` (checked: 6·3^(m−1) diagonal pairs).
   For `HC` the loop trace is `2c²`; for `HC'` it is `2` if the two `z` flux edges are traversed in
   opposite directions and `2c²−2s²` if in the same direction. Contribution per flux rhombus:
   `−16 s²` (opposite) or `+16 s²` (same).

## Orientation

4. **Geometric orientation** (every flux edge directed `+x`): all flux rhombi are "opposite", so
   `Δ_m = −32·3^(m−1) s²` (checked m ≤ 4 in `tests/orientation_check.py`).
5. **Index orientation** (as `sg_graph.py` / `operators.py`): the flux edge of face `k` is flipped
   iff `index(face[0]) > index(face[1])`. Checked m ≤ 7: the flipped faces are exactly `F_m =
   (3^(m−1)−1)/2` faces, all with `k ≡ 1 (mod 3)` (the `Y`-face of a cell, which lies in exactly one
   flux rhombus). Each flip turns `−16 s²` into `+16 s²`, so
   `Δ_m = −32 s² (3^(m−1) − F_m) = −16 (3^(m−1)+1) s²`, and `F_{m+1} = 3F_m + 1` is exactly
   `Δ_{m+1} = 3Δ_m + 32 s²` of `PROOF.md`.

## L5: DONE in Lean (`FlipCount.lean`: `flipCount_succ`, `flipCount_closed`)

Proof (as formalized; files `VertexOrder`, `VertexIndex`, `ListOrder`, `FlipB`, `FlipC`, `FlipFaces`, `FlipCount`):

`vertexOrder (m+1) = eraseDups (P ++ shiftB P ++ shiftC P)`, `P = vertexOrder m`. Consequences:

* **Copy A**: its vertices are the prefix of the list, in the old order, so a face of copy A is
  flipped iff it is flipped at level `m`. Contribution `F_m`.
* **Copy B**: the only removed duplicate is the local corner `(0,0)` (local index 0, smallest),
  so the relative order of any two B-vertices is the old one. Contribution `F_m`.
* **Copy C**: two removed duplicates, local corners `(0,0)` (lies in part A) and `(2^m,0)` (lies in
  part B). Both precede all new C-vertices. Relative order changes only for an edge with an endpoint at
  the local corner `(2^m,0)`; the corner roles say that this corner is the *second* endpoint `f1` of
  its flux edge, whose first endpoint is a new C-vertex, so exactly one face becomes flipped.
  Contribution `F_m + 1`.

Hence `F_{m+1} = 3F_m + 1`, `F_1 = 0`, so `F_m = (3^(m−1)−1)/2`. Checked: flips split as
`(F_{m−1}, F_{m−1}, F_{m−1}+1)` over the three copies for `m = 2..7`; the corner roles are
`(0,0)=f0`, `(2^m,0)=f1`, `(0,2^m)` not a flux endpoint for `m = 1..5`
(`tests/general_m_structure_check.py`). Everything needed was proved directly (no separate corner-role lemma): endpoints of faces lie in `vertexOrder`, the bottom-row order `bottom_lt`, and `corner_count` (exactly one face ends at `(2^m,0)`).

## Refined route (recursion over the three copies; supersedes L1–L4, L6 below)

Reasoning (not yet formalized, except where marked **done**):

* **R1. Additivity.** The edge set of `SG(m+1)` is the disjoint union of the three copies' edge sets
  (`EdgeB` is a disjunction of three exclusive cases; **done**: `EdgeB_sound`, `EdgeB_irrefl`,
  `mem_vertexOrder_iff` in `SGStruct.lean`). Degrees add, so
  `H_{m+1} = Σ_X ι_X H_X ι_X†` exactly, where `H_X` is the level-`m` operator with the orientation
  induced from level `m+1`. Orientation transport is **done**: copies A, B keep the level-`m`
  orientation (`flipped_A`, `flipped_B`), copy C differs only at the face ending in the corner
  `(2^m, 0)` (`flipped_C`, `bottom_lt`, `corner_count`). The axes agree for `m ≥ 1` since face
  indices shift by `3^m ≡ 0 (mod 3)`.
* **R2. Cross words.** Expand `Tr H_{m+1}⁴` over words in `{A,B,C}⁴`. The copies pairwise share
  exactly one corner, and for `m ≥ 1` the corners of a copy are pairwise non-adjacent
  (**done**: `corners_not_adj`, `EdgeB_step` in `EdgeStep.lean`). Every non-constant cyclic word then
  either contains a length-1 run between two different corners (contributes 0) or consists of
  corner-to-same-corner runs, i.e. only the numbers `(H_X²)(v,v) = (d²+d)·1` and
  `tr (H_X³)(v,v)` at corners `v` (degree `d = 2`). The latter involves a single 3-cycle (the
  corner triangle, one flux edge), so its trace is `2c`-type, **independent of the axes**.
  Hence cross words cancel in `Tr H⁴ − Tr H'⁴`: `Δ_{m+1} = Δ(H_A) + Δ(H_B) + Δ(H_C)` (`m ≥ 1`).
* **R3. One flip.** `Δ(H_C) = Δ(H_m) + 32 s²`: flipping the flux edge `e = ((2^m−1,0),(2^m,0))`
  (axis `Y`, the corner vertex has degree 2) changes `Tr A⁴` only through closed 4-walks using `e`
  exactly once, i.e. the rhombus `p, c, q, z` with `p=(s−1,0)`, `c=(s,0)`, `q=(s−1,1)`, `z=(s−2,1)`
  (`Z`-flux edge `q–z`). With `A'` (all `z`) the loop trace changes from `2(c²−s²)` to `2`, and
  `8·(2 − 2c² + 2s²) = 32 s²`; for `A` (axes `Y`,`Z`) both traces equal `2c²`.
* **R4. Induction.** `Δ_1 = −32 s²` (**done**: `traceDefect_one`), then
  `Δ_{m+1} = 3Δ_m + 32 s²` gives `Δ_m = −16(3^(m−1)+1) s²`.

Remaining Lean work for this route: the matrix identity R1 (embeddings `Vertex m → Vertex (m+1)`),
the word expansion R2, corner facts (degree 2, one flux edge on the corner triangle, shape of the
corner cell), and R3.

## Final route (supersedes R3): coupled recursion, no local flip lemma

`Δ̃_m` = trace defect of the level-`m` operator whose index orientation is reversed on the single
flux edge `((2^m−1,0),(2^m,0))` (the face ending at the corner `(2^m,0)`). Numerically
(`m ≤ 4`, verified): `Δ̃_m = −16(3^(m−1)−1) s²` and

* `Δ_{m+1} = 2Δ_m + Δ̃_m`  (copies: A keeps σ_m, B keeps σ_m, C gets σ_m with the corner edge flipped),
* `Δ̃_{m+1} = Δ_m + 2Δ̃_m`  (the level-`(m+1)` corner edge lies in copy B, so B and C both get the flip).

Together with `Δ_1 = −32 s²` (done) and `Δ̃_1 = 0` (new finite computation, like `traceDefect_one`)
this gives `Δ_m = −16(3^(m−1)+1) s²` by induction, **without** analysing the rhombus at the corner.

What it needs (everything orientation-generic, orientations antisymmetric):
1. `pHe_succ` for an arbitrary orientation (the proof of `pHe_succ` already carries the orientation
   through unchanged), plus orientation transport on flux edges (`flipped_A/B/C`, done) for both
   `σ_m` and `σ_m ⊕ flip`.
2. **Gluing algebra** (abstract, `GlueAlg.lean`): for block-diagonal `K` and the gluing matrix `N`,
   `Tr((K+KN)⁴) = Tr K⁴ + 4 S₃ + 2 S₂ + S₁`, where `S₃, S₂, S₁` only involve the diagonal entries of
   `K, K², K³` at glued points.
3. Corner facts for the three corners of `SG(m)`, `m ≥ 1`: degree 2, neighbours adjacent, the corner
   triangle has exactly one flux edge (so `tr (K³)_{cc}` and `(K²)_{cc}` do not depend on the axes).
4. The base cases and the induction.

## Lean targets (original plan; see the refined route above) (in this order)

| # | Statement | Where | Difficulty |
|---|---|---|---|
| L1a | `Tr((D−A)⁴) = Tr D⁴ − 4Tr D³A + 4Tr D²A² + 2Tr DADA − 4Tr DA³ + Tr A⁴` (noncommutative expansion + cyclicity of trace) | `Reduction.lean` | easy |
| L1b | `Tr D³A = 0`, `Tr D²A²`, `Tr DADA` coincide for `H`, `H'`: needs `(A²)_{vv} = deg(v)·1` for general `m` (unitarity + `Adj_symm`) | `Reduction.lean` | medium |
| L1c | `Tr DA³` coincides for `H`, `H'`: every 3-cycle of `SG(m)` has at most one flux edge, so its holonomy trace is `2c`. **Depends on L2.** | `Rhombi.lean` | hard |
| L2 | Combinatorics of `SG(m)`: ≤ 2 common neighbours; rhombus ⇔ pair with 2; the flux-carrying rhombi are exactly `X–Z`, `Y–Z` per cell | new `Rhombi.lean`, induction on `EdgeB` | **hard** |
| L3 | Holonomy traces of the two flux rhombus types (finite computation, like `Algebra.lean`) | extend `Algebra.lean` | easy |
| L4 | Geometric version: `Δ_m = −32·3^(m−1) s²` from L1–L3 | new `Geometric.lean` | medium |
| L5 | `#{faces with index(f.2.1) < index(f.1)} = (3^(m−1)−1)/2` via `vertexOrder` | `FlipCount.lean` | **done** (`2·flipCount (m+1) + 1 = 3^m`; only standard axioms) |
| L6 | Assemble L4 + L5 into `traceDefect m θ = −16(3^(m−1)+1) s²` | new `Main.lean` | easy |

L1a–c, L3, L4 give a complete Lean proof of the geometric closed form; L5 is what the
index-orientation formula additionally needs.
