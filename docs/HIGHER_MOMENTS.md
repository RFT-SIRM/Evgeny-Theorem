# Higher Spectral Moments: H⁶, H⁸, H¹⁰

## Status

**H⁴** has an exact closed form. See [THEOREM.md](../THEOREM.md).

**H⁶** has an explicit all-angle recurrence and closed form for every level
`m ≥ 2`. The recurrence for `m ≥ 3` is Lean-proved; the finite transition
`m = 2 → 3` and coefficient formula are certified by exact symbolic
polynomial arithmetic in the Python regression suite. That base transition is
not yet a Lean-kernel theorem. **H⁸** has an all-angle affine recurrence for every level \(m\ge3\), plus an
exact symbolic finite transition \(m=2\to3\); together these give the explicit
closed form for every \(m\ge2\). The finite transition is an exact Python
polynomial certificate, not yet a Lean-kernel theorem. **H¹⁰** remains open.

---

## H⁶: Structural results

### 1. All-angle recurrence and explicit closed form (combined Lean + exact certificate)

Write
`D_m(θ) = defectO6 m θ faceAxis (fun _ => 2) (oNum m)`,
`c = cos(θ/2)`, and `s = sin(θ/2)`.

The Lean proof establishes the recurrence for every angle and `m ≥ 3`.
The exact Gaussian-integer polynomial certificate in
`tests/test_higher_moments.py` checks the finite `m = 2 → 3` transition
by expanding the exact level-2 and level-3 trace polynomials and reducing only
with `c² + s² = 1`. Together these results give, for every angle and `m ≥ 2`,

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

At `θ = π`, this gives `C₆(π) = 5280`, agreeing with the exact sparse
Gaussian-integer certificates.

**Proof boundary:** `defectO6_num_growth_recurrence` in
`formalization/EvgenyTheorem/FinalTilde.lean` is Lean-proved for `m ≥ 3`.
The exceptional finite base transition is established by exact symbolic Python
polynomial arithmetic and regression tests, not currently by Lean's kernel.
No floating-point sampling is used for that polynomial identity.

### 2. Exact symbolic base-transition certificate

The certificate pins the raw level-two defect polynomial, verifies
`D₃ - 3D₂ = C₆(θ)`, and checks that the adjusted residual
`D_{m+1} - 3D_m + F₃` has the same exact polynomial at `m = 2` and `m = 3`.
This is the one finite bridge needed to extend the Lean recurrence to `m ≥ 2`.

### 3. Path-class zero pattern on SG(1) (finite-level result)

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

### 4. Why H⁶ differs from the simpler H⁴ formula

H⁴ has the particularly simple factor `−4·sin²(θ/2)` per contributing
triangular traversal. H⁶ still has an explicit level-growth closed form, but
its coefficient contains several trigonometric monomials. The contributing
three-triangle class `{0,1,2}` contains 486 walks with different sequences of
rotation axes; the exact level-growth formula above comes from the recurrence
and finite symbolic base certificate, not from identifying those walks with
one common H⁴ contribution.

### 5. What remains open

- Formalize the exact finite level-2-to-3 base transition in Lean, so the combined H⁶ result is kernel-checked end to end.
- H⁸ is now covered by the combined Lean recurrence plus exact finite base-transition certificate described below.
- Derive the corresponding all-angle recurrence and closed form for H¹⁰.

The path-class inventory and exact sparse certificate remain useful for
simplifying the finite coefficient; they are not needed to claim the all-level
affine law for H⁶ when `m ≥ 3`.## H⁸: all-angle affine law from level two

Let
\[
D_m(\theta)=\operatorname{defectO8}(m,\theta,\mathrm{faceAxis},2,\mathrm{oNum}),
\quad c=\cos(\theta/2),\quad s=\sin(\theta/2).
\]
The Lean proof establishes the exact recurrence
\[
D_{m+1}(\theta)=3D_m(\theta)+C_8(\theta),\qquad m\ge3.
\]
An exact sparse-polynomial certificate computes the finite traces at levels
2, 3, and 4 and proves coefficient-by-coefficient that
\[
D_3-3D_2=D_4-3D_3=C_8(\theta).
\]
The resulting explicit coefficient and level-two value are
\[
\begin{aligned}
D_2(\theta)={}&-1335552s^2+244352cs^2-40064s^3+64cs^3+1920s^4,\\
C_8(\theta)={}&193600s^2+75776cs^2+83712s^3-512cs^3+192s^4.
\end{aligned}
\]
Therefore, for every \(m\ge2\),
\[
D_m(\theta)=3^{m-2}D_2(\theta)
+\frac{3^{m-2}-1}{2}C_8(\theta).
\]
At \(\theta=\pi\), this gives \(C_8(\pi)=277504\), agreeing with the
independent exact Gaussian-integer trace certificate.

**Proof boundary.** The all-level structural recurrence and the arithmetic
closed-form step are Lean-formalized. The exceptional \(m=2\to3\) transition
is verified by exact polynomial arithmetic over Gaussian integers in
computational/p8_base_certificate.py; its values at \(\theta=\pi\) are
cross-checked against computational/higher_moment_pi_certificate.py.
The finite transition is an exact reproducible certificate, not yet a
Lean-kernel theorem. No sampled-angle fit is used.

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
