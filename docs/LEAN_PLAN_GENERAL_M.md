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

## Lean targets (in this order)

| # | Statement | Where | Difficulty |
|---|---|---|---|
| L1 | Algebraic reduction 1–3 for a finite graph with unitary edge blocks (abstract, no `SG`) | new `Reduction.lean` | medium |
| L2 | Combinatorics of `SG(m)`: ≤ 2 common neighbours; rhombus ⇔ pair with 2; the flux-carrying rhombi are exactly `X–Z`, `Y–Z` per cell | new `Rhombi.lean`, induction on `EdgeB` | **hard** |
| L3 | Holonomy traces of the two flux rhombus types (finite computation, like `Algebra.lean`) | extend `Algebra.lean` | easy |
| L4 | Geometric version: `Δ_m = −32·3^(m−1) s²` from L1–L3 | new `Geometric.lean` | medium |
| L5 | `#{k : index(face[0]) > index(face[1])} = (3^(m−1)−1)/2`, all `k ≡ 1 mod 3`, using `vertexOrder` (`Orientation.lean`) | new `FlipCount.lean`, induction with `eraseDups` | **hard** (new combinatorics) |
| L6 | Assemble L4 + L5 into `traceDefect m θ = −16(3^(m−1)+1) s²` | new `Main.lean` | easy |

L1, L3, L4 give a complete Lean proof of the geometric closed form; L5 is what the
index-orientation formula additionally needs.
