# Higher Spectral Moments: H⁶, H⁸, H¹⁰

## Status

**H⁴** has an exact closed form. See [THEOREM.md](../THEOREM.md).

**H⁶** has an explicit all-angle recurrence and closed form for every level
`m ≥ 2`. The recurrence for `m ≥ 3` is Lean-proved; the finite transition
`m = 2 → 3` and coefficient formula are certified by exact symbolic
polynomial arithmetic in the Python regression suite. That base transition is
not yet a Lean-kernel theorem. **H⁸ and H¹⁰** remain an open research program.

---

## H⁶: Structural results

### 1. All-angle recurrence and explicit closed form (combined Lean + exact certificate)

Write
\`D_m(θ) = defectO6 m θ faceAxis (fun _ => 2) (oNum m)\`,
\`c = cos(θ/2)\`, and \`s = sin(θ/2)\`.

The Lean proof establishes the recurrence for every angle and \`m ≥ 3\`.
The exact Gaussian-integer polynomial certificate in
\`tests/test_higher_moments.py\` checks the finite \`m = 2 → 3\` transition
by expanding the exact level-2 and level-3 trace polynomials and reducing only
with \`c² + s² = 1\`. Together these results give, for every angle and \`m ≥ 2\`,

$$
D_{m+1}(\theta)=3D_m(\theta)+C_6(\theta),
$$

with the explicit coefficient

$$
C_6(\theta)=4512s^2+192cs^2+768s^3.
$$

The level-two value is

$$
D_2(\theta)=-14592s^2+1344cs^2-384s^3.
$$

Thus the all-level closed form is

$$
D_m(\theta)=3^{m-2}D_2(\theta)
+\frac{3^{m-2}-1}{2}C_6(\theta),
\qquad m\ge2,
$$

or, fully expanded,

$$
D_m(\theta)=-(12336\cdot3^{m-2}+2256)s^2
+(1440\cdot3^{m-2}-96)cs^2-384s^3.
$$

At \`θ = π\`, this gives \`C₆(π) = 5280\`, agreeing with the exact sparse
Gaussian-integer certificates.

**Proof boundary:** \`defectO6_num_growth_recurrence\` in
\`formalization/EvgenyTheorem/FinalTilde.lean\` is Lean-proved for \`m ≥ 3\`.
The exceptional finite base transition is established by exact symbolic Python
polynomial arithmetic and regression tests, not currently by Lean's kernel.
No floating-point sampling is used for that polynomial identity.

### 2. Exact symbolic base-transition certificate

The certificate pins the raw level-two defect polynomial, verifies
\`D₃ - 3D₂ = C₆(θ)\`, and checks that the adjusted residual
\`D_{m+1} - 3D_m + F₃\` has the same exact polynomial at \`m = 2\` and \`m = 3\`.
This is the one finite bridge needed to extend the Lean recurrence to \`m ≥ 2\`.

### 3. Path-class zero pattern on SG(1) (finite-level result)

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

### 5. Why H⁶ differs from the simpler H⁴ formula

H⁴ has the particularly simple factor `−4·sin²(θ/2)` per contributing
triangular traversal. H⁶ still has an explicit level-growth closed form, but
its coefficient contains several trigonometric monomials. The contributing
three-triangle class `{0,1,2}` contains 486 walks with different sequences of
rotation axes; the exact level-growth formula above comes from the recurrence
and finite symbolic base certificate, not from identifying those walks with
one common H⁴ contribution.

### 6. What remains open

- Formalize the exact finite level-2-to-3 base transition in Lean, so the combined H⁶ result is kernel-checked end to end.
- Derive the corresponding all-angle recurrence and closed forms for H⁸ and H¹⁰.

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
