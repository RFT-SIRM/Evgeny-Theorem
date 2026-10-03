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

## Proof idea for L5 (derived from `vertexOrder`; numbers checked, **not yet in Lean**)

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
(`tests/general_m_structure_check.py`). The corner roles themselves (PROOF.md §4.1) still need a
proof by induction on `EdgeB`/`facesExact`; this is the first sub-lemma of L5.

## Lean targets (in this order)

| # | Statement | Where | Difficulty |
|---|---|---|---|
| L1a | `Tr((D−A)⁴) = Tr D⁴ − 4Tr D³A + 4Tr D²A² + 2Tr DADA − 4Tr DA³ + Tr A⁴` (noncommutative expansion + cyclicity of trace) | `Reduction.lean` | easy |
| L1b | `Tr D³A = 0`, `Tr D²A²`, `Tr DADA` coincide for `H`, `H'`: needs `(A²)_{vv} = deg(v)·1` for general `m` (unitarity + `Adj_symm`) | `Reduction.lean` | medium |
| L1c | `Tr DA³` coincides for `H`, `H'`: every 3-cycle of `SG(m)` has at most one flux edge, so its holonomy trace is `2c`. **Depends on L2.** | `Rhombi.lean` | hard |
| L2 | Combinatorics of `SG(m)`: ≤ 2 common neighbours; rhombus ⇔ pair with 2; the flux-carrying rhombi are exactly `X–Z`, `Y–Z` per cell | new `Rhombi.lean`, induction on `EdgeB` | **hard** |
| L3 | Holonomy traces of the two flux rhombus types (finite computation, like `Algebra.lean`) | extend `Algebra.lean` | easy |
| L4 | Geometric version: `Δ_m = −32·3^(m−1) s²` from L1–L3 | new `Geometric.lean` | medium |
| L5 | `#{k : index(face[0]) > index(face[1])} = (3^(m−1)−1)/2`, all `k ≡ 1 mod 3`, using `vertexOrder` (`Orientation.lean`) | new `FlipCount.lean`, induction with `eraseDups` | **hard** (new combinatorics) |
| L6 | Assemble L4 + L5 into `traceDefect m θ = −16(3^(m−1)+1) s²` | new `Main.lean` | easy |

L1a–c, L3, L4 give a complete Lean proof of the geometric closed form; L5 is what the
index-orientation formula additionally needs.
