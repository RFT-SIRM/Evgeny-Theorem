# Higher Spectral Moments: H⁶, H⁸, H¹⁰

## Status

**H⁴** has an exact closed form. See [THEOREM.md](../THEOREM.md).

**H⁶** now has a Lean-proved all-angle affine growth law for levels `m ≥ 3`;
the finite-level coefficient is not yet simplified, and the level-2-to-3 base
transition remains open. **H⁸ and H¹⁰** remain an open research program.
This document records the proven H⁶ result, its limitations, and the remaining
higher-moment steps.

---

## H⁶: Structural results

### 1. All-angle recurrence and affine growth (Lean-proved for m ≥ 3)

Writing
`D_m(θ) = defectO6 m θ faceAxis (fun _ => 2) (oNum m)`, the current
Lean proof establishes

$$
D_{m+1}(\theta)=3D_m(\theta)+C_6(\theta),\qquad m\ge 3,
$$

and equivalently

$$
D_m(\theta)=3^{m-3}A_6(\theta)+B_6(\theta),\qquad m\ge 3.
$$

The functions `C₆`, `A₆`, and `B₆` are defined exactly in
`formalization/EvgenyTheorem/FinalTilde.lean` from the level-three defect,
the level-three orientation gap, and the level-three high-power boundary
residual. They are independent of m; no vanishing of the gap or residual is
assumed. Both full Lean CI builds passed on commit
`7ce1e9d687ce8b20d61bb6c5da39b0975f41519c`.

### 2. Remaining base-transition and coefficient questions

The transition from level 2 to level 3 (`D_3 - 3D_2 = C₆(θ)`) is not yet
formally proved for all angles, and the finite level-three expression for
`C₆(θ)` has not been simplified to an elementary trigonometric expression.

### 3. Exact finite certificate at θ = π

The sparse Gaussian-integer certificate gives the exact residual value 5280
for tested transitions from levels 3 through 6 at `θ = π`. This is a finite
arithmetic calculation; the Lean theorem does not yet separately normalize
its general coefficient `C₆(π)` to 5280.

### 4. Path-class zero pattern on SG(1) (finite-level result)

On `SG(1)` (6 vertices, 9 edges, 3 triangles), closed walks of length 6 were classified computationally by which triangles they visit. Their contribution to
`Δ(H⁶) = Tr(H_C⁶) − Tr(H_C′⁶)` is reported as follows:

| Path class (triangles visited) | Count | Δ contribution |
|---|---:|---:|
| Single triangle `{0}`, `{1}`, or `{2}` | 66 each | **0** (exact) |
| Two triangles `{0,1}`, `{0,2}`, or `{1,2}` | 168 each | **0** (exact) |
| All three triangles `{0,1,2}` | 486 | **nonzero** |

In these finite-level calculations, only paths sampling all three rotation axes (x, y, z) contribute. The isolated triangle calculations agree to `10⁻¹²`; this is not an all-level theorem.

The physical reason: for two axes, `Tr([R_a, R_b] · M) = 0` — the
pairwise commutator leaves no trace. All three axes are required.

### 5. Why H⁶ has no closed form of the H⁴ type

H⁴ has an exact closed form because every contributing walk performs
exactly one triangular traversal, producing the same function `−4·sin²(θ/2)`.

H⁶ has a single contributing path class `{0,1,2}`, but that class
contains 486 distinct walks with different sequences of rotation axes
whose SU(2) holonomies do not collapse to a finite trigonometric polynomial.

### 6. What remains open

- Prove the finite base transition `D_3 - 3D_2 = C₆(θ)` for every angle.
- Simplify the exact level-three definition of `C₆(θ)` to an elementary expression, if possible.
- Derive the corresponding all-angle recurrence and affine growth law for H⁸ and H¹⁰.

The path-class inventory and exact sparse certificate remain useful for
simplifying the finite coefficient; they are not needed to claim the all-level
affine law for H⁶ when `m ≥ 3`.---

## H⁸ and H¹⁰: Numerical results

The same structural pattern holds:

- Growth law `α(θ)·3^m + β(θ)` verified to machine precision.
- No quadratic `3^(2m)` terms (coefficient ratio `< 10⁻¹⁵`).
- No closed form is claimed.

### Reference values at θ = π/2

| m | Δ(H⁶) | Δ(H⁸) | Δ(H¹⁰) |
|---:|---:|---:|---:|
| 1 | −3180.000000000000 | −246909.026268397924 | −14013358.982483163476 |
| 2 | −6956.588745030516 | −595053.284942481667 | −37686518.369789719582 |
| 3 | −18274.354980121832 | −1632052.331668503582 | −107772338.487565994263 |
| 4 | −52227.653685396537 | −4743049.471846580505 | −318029798.840893745422 |

Locked by `tests/test_higher_moments.py` and `tests/test_path_class_h6.py`.

---

## Contributing

If you can derive a closed form for `C(θ)` or `Δ_m(H⁶, θ)`, establish
the recurrence analytically, or extend the path-class theorem to H⁸ or H¹⁰,
please open an issue or pull request with the derivation and reproducible
numerical checks.
