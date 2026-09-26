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

This has also been checked as an *exact* computer-algebra identity (no floating point, no tolerance) for `m = 1..7`, with the local mechanism behind it derived in [docs/EXACT_VERIFICATION.md](docs/EXACT_VERIFICATION.md) and [docs/SPLIT_AUTOMATON.md](docs/SPLIT_AUTOMATON.md). [docs/PROOF.md](docs/PROOF.md) assembles these into a complete hand proof of this identity for every `m`, not only the tested range — still short of a Lean-checked proof (`formalization/README.md`).

Normalizing by `dim(H) = 2n(m) = 3^(m+1) + 3` gives the intensive invariant:

```
I_m(θ) = Δ_m(H⁴,θ) / dim(H) = −16 · (3^(m−1)+1) · sin²(θ/2) / (3^(m+1) + 3)
```

At `θ = π/2`:

```
lim_{m→∞} I_m(π/2) = −8/9
```

## Higher-moment numerical verification

The fourth-moment identity above is the repository's analytic closed-form result. Higher moments have also been computed directly under the same non-commuting configuration `C` and commuting control `C′`.

For `Δ_m(H^p, θ) = Tr(H_C^p) − Tr(H_C′^p)`, the following reference values are reproduced at `θ = π/2`:

| m | Δ_m(H⁶, π/2) | Δ_m(H⁸, π/2) | Δ_m(H¹⁰, π/2) |
|---:|---:|---:|---:|
| 1 | −3180.000000000000 | −246909.026268397924 | −14013358.982483163476 |
| 2 | −6956.588745030516 | −595053.284942481667 | −37686518.369789719582 |
| 3 | −18274.354980121832 | −1632052.331668503582 | −107772338.487565994263 |
| 4 | −52227.653685396537 | −4743049.471846580505 | −318029798.840893745422 |

These are **numerical regression references**, not claimed closed-form formulas or machine-checked theorems for H⁶, H⁸, or H¹⁰. They are locked into [`tests/test_higher_moments.py`](tests/test_higher_moments.py).

Higher moments are evaluated by constructing the finite-dimensional operators and multiplying the matrices directly. No O(1) analytic formula is claimed for H⁶, H⁸, or H¹⁰.

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

The closed form permits evaluating `Δ_m(H⁴, θ)` for any `m` and `θ` in O(1) arithmetic operations, without constructing the underlying `2n(m)`-dimensional operator. This closed-form statement applies strictly to the fourth-moment invariant defined above.

Higher moments have also been evaluated directly. In particular, `Δ_m(H⁶, θ)`, `Δ_m(H⁸, θ)`, and `Δ_m(H¹⁰, θ)` are covered by reproducible numerical regression tests for `m = 1, 2, 3, 4` at `θ = π/2` (`tests/test_higher_moments.py`). These are numerical reference results, not claimed closed-form theorems. No analytic formula for H⁶, H⁸, or H¹⁰ is asserted here.
