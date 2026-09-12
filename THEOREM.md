# Theorem statement

## Object

Let `SG(m)` be the standard Sierpiński-gasket approximation graph at refinement level `m`, built by recursive triangle subdivision (`src/graph/sg_graph.py`). Vertex count `n(m) = (3^(m+1)+3)/2`, edge count `3^(m+1)`, elementary-triangle (face) count `3^m` — all closed-form and checked in `tests/test_levels.py`.

The Hilbert space is `C^n ⊗ C²`. Every graph edge `(a,b)` carries a unitary `U(a,b) ∈ SU(2)`, with `U(b,a) = U(a,b)†`. Flux is injected through exactly one designated edge per elementary triangle. Two configurations are compared at the same local rotation angle `θ`:

- **C (non-commuting):** rotation axis on the flux edge cycles x/y/z by triangle index mod 3. Verified to produce genuinely non-commuting holonomy between triangles sharing a vertex (‖[U_i, U_j]‖ = 1.0, the maximal value for unitary 2×2 matrices).
- **C′ (commuting control):** identical, but the axis is fixed to z for every triangle. All edge matrices commute; this is exactly equivalent to two decoupled U(1) magnetic SG Laplacians at flux ±θ/2.

At θ = 0, both reduce exactly to two decoupled copies of the plain SG Laplacian (`tests/test_levels.py::test_su2_bundle_reduces_to_two_plain_sg_copies_at_theta_zero`).

## Statement

Let `Δ_m(H⁴, θ) = Tr(H_C⁴) − Tr(H_C'⁴)`.

```
Δ_m(H⁴, θ) = −16 · (3^(m−1) + 1) · sin²(θ/2)
```

exactly, for every tested `(m, θ)` pair, to numerical precision better than `1e-9` (small `m`) down to `1e-6` (`m=7`, dim 6564). See `VERIFICATION.md`.

Normalizing by `dim(H) = 2n(m) = 3^(m+1) + 3` gives the intensive invariant:

```
I_m(θ) = Δ_m(H⁴, θ) / dim(H) = −8 · (3^(m−1) + 1) · sin²(θ/2) / (3^(m+1) + 3)
```

At `θ = π/2`:

```
lim_{m→∞} I_m(π/2) = −8/9
```

## Acceptance protocol

The quantity `I_m` was accepted as a genuine structural invariant only after checking all six of the following, not fewer:

| # | Criterion | Status |
|---|---|---|
| i | stable limit as `m → ∞` | geometric convergence to `−8/9`, confirmed to `m=7` |
| ii | differs from plain SG (A) and U(1)-magnetic SG (B) | the quantity does not exist in A or B by construction |
| iii | survives normalization | computed as a per-state quantity throughout |
| iv | gauge-invariant | verified to `8e-15` under a random SU(2) gauge transformation |
| v | not merely a function of dim / edges / faces / flux-density | C and C′ are identical in all of these; only axis choice differs |
| vi | vanishes in the commuting limit | by construction (`I_m = M₄(C) − M₄(C′)`); zero exactly at moments p=1,2,3, first nonzero at p=4 |

## Computational scope of the closed form

The closed form permits evaluating `Δ_m(H⁴, θ)` for any `m` and `θ` in O(1) arithmetic operations, without constructing the underlying `2n(m)`-dimensional operator. This applies strictly to the single quantity defined above. It is not a statement about the computational complexity of the operator's full spectrum, its spectral gap, or any moment other than the fourth — those still require constructing and diagonalizing (or multiplying out) the operator directly, as done throughout `tests/` and `reproducibility/`.
