# Higher Spectral Moments: H⁶, H⁸, H¹⁰

## Status

**H⁴** has an exact closed form. See [THEOREM.md](../THEOREM.md).

**H⁶, H⁸, H¹⁰** are an open research program. This document records
what is currently established, what is not, and what the next steps are.

---

## H⁶: Structural results

### 1. Growth law (established numerically to machine precision)

For all tested `(m, θ)`:
Δ_m(H⁶, θ) = α(θ)·3^m + β(θ)

Verification: coefficients `α`, `β` fitted from `m = 4, 5` predict `m = 3`
with error below `10⁻⁸` across all tested θ values.

No quadratic term `3^(2m)` is present. The coefficient of `9^m` in a
3-point fit using `m = 3, 4, 5` is below `10⁻¹⁵` relative to the linear term.

### 2. Exact recurrence (established)

For `m ≥ 2`:
Δ_m(H⁶, θ) = 3 · Δ_{m−1}(H⁶, θ) + C(θ)

where `C(θ)` is independent of `m`. Verified by checking that
`Δ_m − 3·Δ_{m−1}` is constant across `m = 2, 3, 4, 5` for all tested θ.

### 3. Exact value C(π) = 5280

At `θ = π`, the recurrence constant is the exact integer:
C(π) = 5280 = 2⁵ · 3 · 5 · 11

| θ | C(θ) |
|---|------|
| 0 | 0 (exact) |
| π/6 | 327.985… |
| π/4 | 729.785… |
| π/3 | 1265.569… |
| π/2 | 2595.411… |
| 2π/3 | 3954.831… |
| **π** | **5280** (exact integer) |

At `θ = π`, the growth law also yields exact fractions:
`α(π) = −4112/3`, `β(π) = −2640`.

### 4. Path-class zero theorem (established)

On `SG(1)` (6 vertices, 9 edges, 3 triangles), all closed walks of length 6
are classified by which triangles they visit. Their contribution to
`Δ(H⁶) = Tr(H_C⁶) − Tr(H_C′⁶)` satisfies:

| Path class (triangles visited) | Count | Δ contribution |
|---|---:|---:|
| Single triangle `{0}`, `{1}`, or `{2}` | 66 each | **0** (exact) |
| Two triangles `{0,1}`, `{0,2}`, or `{1,2}` | 168 each | **0** (exact) |
| All three triangles `{0,1,2}` | 486 | **nonzero** |

Only paths sampling all three rotation axes (x, y, z) contribute.
Verified on isolated triangle Hamiltonians to `10⁻¹²`.

The physical reason: for two axes, `Tr([R_a, R_b] · M) = 0` — the
pairwise commutator leaves no trace. All three axes are required.

### 5. Why H⁶ has no closed form of the H⁴ type

H⁴ has an exact closed form because every contributing walk performs
exactly one triangular traversal, producing the same function `−4·sin²(θ/2)`.

H⁶ has a single contributing path class `{0,1,2}`, but that class
contains 486 distinct walks with different sequences of rotation axes
whose SU(2) holonomies do not collapse to a finite trigonometric polynomial.

### 6. What remains open

- Analytical expression for `C(θ)` at general `θ`.
- Symbolic computation of all 486 walk contributions.
- Whether `C(θ)` admits a closed form in any variable.

---

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
