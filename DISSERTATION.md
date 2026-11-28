# Evgeny's Theorem: Spectral Trace Defects of Noncommutative SU(2) Connections on Sierpiński-Gasket Graphs

## Research dissertation

**Author:** Evgeny Zaprudnov  
**Research group:** RFT-SIRM  
**Version:** 2.0 (version 1.0: 8 November 2026; version 2.0 adds the twelfth moment)  
**Date:** 28 November 2026  
**Project:** [RFT-SIRM/Evgeny-Theorem](https://github.com/RFT-SIRM/Evgeny-Theorem)

---

## Abstract

This dissertation studies trace defects of recursively defined graph operators on finite Sierpiński-gasket approximations. Each vertex carries a two-component complex state, and the edges carry an SU(2)-valued connection. Two configurations are compared on the same graph: a non-commuting connection whose flux-edge axes cycle through x, y, z, and a commuting control that uses the fixed z-axis.

The principal theorem, called Evgeny's Theorem, is the exact identity
```math
\boxed{
\Delta_m^{(4)}(\theta)
=
Tr\left(H_C(m,\theta)^4\right)
-
Tr\left(H_{C'}(m,\theta)^4\right)
=
-16\bigl(3^{m-1}+1\bigr)\sin^2\left(\frac{\theta}{2}\right)
}
```
for every integer m ≥ 1 and every real θ. The identity is proved for the concrete operators in Lean 4 by the declaration **traceDefect_closed**. Its proof uses recursive gluing and two coupled orientation recurrences. The final theorem contains no unproved placeholder and depends only on the standard Lean axioms **propext**, **Classical.choice**, and **Quot.sound**.

After normalization by the matrix dimension, the fourth-moment defect has the exact limit
```math
I_\infty(\theta)=-\frac{16}{9}\sin^2\left(\frac{\theta}{2}\right).
```
This is a statement about one normalized trace observable; it is not a theorem about the full spectrum, individual eigenvalues, the spectral gap, or computational complexity.

The dissertation also records the present higher-moment results. For H⁶ and H⁸, Lean proves the all-angle recurrences for m ≥ 3, while exact symbolic certificates close the exceptional transition m = 2 → 3. These combined formulae are exact, but the finite bridges are not yet Lean-kernel theorems. For H¹⁰, radius-four diagonal transport through degree nine is proved in Lean for both configurations at all m ≥ 4. Consequently, the H¹⁰ affine recurrence for m ≥ 4 and affine closed form for m ≥ 5 are unconditional Lean theorems. Their level-five correction is an exact finite trace expression that has not yet been expanded into a trigonometric polynomial.

For H¹², Lean proves, for every real θ and every level m ≥ 3, the affine recurrence, the finite initial bridge D₄ = 3D₃ + C₁₂, and the affine closed form. The explicit trigonometric-polynomial form of its two finite trace quantities, D₃ = 32s²Q₃ and C₁₂ = −64s²Q₁₂ (with s = sin(θ/2) and explicit integer polynomials Q₃, Q₁₂), is supported by exact integer-arithmetic certificates; these two finite identities are not yet Lean-kernel theorems.

The purpose of this document is to preserve these distinctions. A Lean theorem, an exact finite symbolic certificate, and a numerical regression are different forms of evidence. Every claim below is restricted to the graph, edge orientation, and operator definitions actually maintained in this repository.

**Keywords:** Sierpiński-gasket graphs; trace defect; spectral moments; SU(2) connection; non-commuting holonomy; recursive gluing; exact symbolic computation; Lean 4.

---

## 1. Scope and status of the results

The central result is a universal fourth-moment identity: it holds for every refinement level m ≥ 1 and every real angle θ. It is machine-checked for the concrete matrices defined by the repository, not inferred from the finite numerical tables.

The repository also contains separate results for higher even moments. Their status is summarized below.

| Moment | Established statement | Proof boundary |
|---|---|---|
| H⁴ | Exact closed form for all m ≥ 1, all θ ∈ ℝ. | Unconditional Lean-kernel theorem. |
| H⁶ | All-angle recurrence for m ≥ 3; combined formula for m ≥ 2. | Lean recurrence plus an exact Gaussian-integer polynomial certificate for the 2 → 3 transition. |
| H⁸ | All-angle recurrence for m ≥ 3; combined formula for m ≥ 2. | Lean recurrence plus an exact sparse-polynomial certificate for the 2 → 3 transition. |
| H¹⁰ | Unconditional affine recurrence for m ≥ 4; unconditional affine form for m ≥ 5. | Both are Lean-kernel theorems; the correction coefficient remains an exact finite trace expression. |
| H¹² | Unconditional affine recurrence, finite bridge D₄ = 3D₃ + C₁₂, and affine form for every m ≥ 3. | Lean-kernel theorems with D₃ and C₁₂ kept as exact finite trace expressions; their explicit polynomial form is an exact external certificate, not yet a Lean-kernel theorem. |

The H⁶ and H⁸ finite bridges are exact and reproducible but are not yet formalized inside the Lean kernel. By contrast, the H¹⁰ recurrence does not retain an unproved transport hypothesis: the required transport statement is itself proved in Lean. Simplifying its correction coefficient would improve its presentation, but is not required for the unconditional theorem.

The H¹² recurrence, finite bridge and affine form are likewise Lean-kernel theorems. What is not yet in the kernel is the evaluation of the two finite trace quantities D₃ and C₁₂ as explicit polynomials; that evaluation is carried out by exact integer arithmetic and is reproducible with the tests listed in Section 8.

This work does not claim a formula for all eigenvalues, the spectral gap, a computational-complexity classification, or a physical law.

### 1.1 Summary for non-specialists

*The setting.* Take a Sierpiński gasket: a triangle made of three smaller triangles, each of which is again made of three smaller ones, and so on, m times. Place a particle with an internal two-state "spin" on the corners of the smallest triangles; it can hop along the edges. On one edge of every smallest triangle, the hop also rotates the spin by an angle θ about one of three perpendicular axes. In the non-commuting configuration the three axes alternate from triangle to triangle, so successive rotations do not commute (the order matters). In the commuting control every rotation uses the same axis. Each configuration gives a finite matrix H (a graph Laplacian) whose eigenvalues play the role of energy levels.

*What is measured.* The trace of H⁴ is the sum of the fourth powers of all energy levels, the fourth spectral moment. The theorem compares this single number for the two configurations.

*What the theorem says.* For every refinement level m ≥ 1 and every angle θ, the difference between the two sums is exactly −16(3^(m−1) + 1) sin²(θ/2). The angle enters only through sin²(θ/2), and the level enters as a tripling plus a constant, mirroring the way each gasket is assembled from three copies of the previous one. The difference is never positive: the non-commuting configuration never has a larger fourth moment than its control, and the two agree only when the rotation is trivial.

*Why the proof matters.* The identity is a statement about infinitely many graphs and a continuum of angles, and it has been checked by the Lean 4 proof assistant rather than by sampling. Sections 6 and 8 state precisely which higher-moment parts are checked by the Lean kernel and which by exact arithmetic outside it.

*What it does not say.* It concerns this specific family of operators and one trace observable. It does not give the full spectrum, says nothing about a spectral gap, and is a mathematical identity, not a claim about a physical system.

## 2. Graph and connection operators

### 2.1 The recursive graph

Let SG(m) be the finite Sierpiński-gasket approximation graph at refinement level m, built by recursively assembling three copies of the preceding level and identifying their corner vertices. Its exact combinatorial counts are
```math
|V_m|=\frac{3^{m+1}+3}{2},
\qquad
|E_m|=3^{m+1},
\qquad
|F_m|=3^m.
```
Each vertex carries two complex state components. Therefore
```math
\mathcal H_m=\mathbb C^{|V_m|}\otimes\mathbb C^2,
\qquad
N_m=\dim\mathcal H_m=3^{m+1}+3.
```

### 2.2 The SU(2) edge data

Let σₓ, σᵧ, σ_z be the Pauli matrices. A flux edge with rotation axis a ∈ {x, y, z} carries
```math
U_a(\theta)
=
\cos\left(\frac{\theta}{2}\right)I_2
-i\sin\left(\frac{\theta}{2}\right)\sigma_a.
```
The reverse orientation carries the adjoint:
```math
U(b,a)=U(a,b)^\ast.
```
Exactly one designated edge of each elementary triangle carries this rotation; the other edges carry the identity.

Configuration C assigns the axes x, y, z cyclically by triangle index modulo three. Configuration C′ keeps the graph and flux-edge locations fixed but assigns the z-axis to every triangle. Its edge rotations commute and split into two decoupled U(1)-magnetic Sierpiński-gasket operators with fluxes +θ/2 and −θ/2.

The operator has graph-Laplacian form
```math
H=D-A,
```
where D is the degree matrix tensored with I₂, and A is the connection adjacency matrix. At θ = 0, both configurations reduce to two copies of the ordinary Sierpiński-gasket Laplacian.

### 2.3 Orientation convention

The theorem uses the vertex-index orientation of the repository: Lean uses **vIdx**, and Python orders edge endpoints by their vertex indices. This is part of the operator definition.

The orientation audit records that a different, geometrically uniform direction convention gives, for the tested levels m = 1, …, 4,
```math
-32\cdot3^{m-1}\sin^2\left(\frac{\theta}{2}\right).
```
That alternative is a finite-level comparison in **docs/ORIENTATION_NOTE.md**, not the all-level theorem proved here. Graph indexing, face order, flux-edge choice, and edge orientation must be preserved when reproducing the result.

## 3. Trace-defect notation

For an even moment p, define
```math
\Delta_m^{(p)}(\theta)
=
Tr\left(H_C(m,\theta)^p\right)
-
Tr\left(H_{C'}(m,\theta)^p\right).
```
For the higher-moment Lean statements, Dₘ⁽ᵖ⁾(θ) denotes the corresponding numbering-orientation quantity defined by **defectO6**, **defectO8**, **defectO10**, and **defectO12**.

For the polynomial formulae below, write
```math
\phi=\frac{\theta}{2},\qquad
c=\cos\phi,\qquad s=\sin\phi,\qquad c^2+s^2=1.
```

## 4. Main theorem: the fourth spectral moment

### Theorem 4.1 (Evgeny's Theorem) — exact fourth-moment trace defect

For every integer m ≥ 1 and every real θ,
```math
\boxed{
\Delta_m^{(4)}(\theta)
=
-16\left(3^{m-1}+1\right)
\sin^2\left(\frac{\theta}{2}\right).
}
```
The concrete Lean declaration is **traceDefect_closed** in **formalization/EvgenyTheorem/TildeEntries.lean**.

The identity implies Δₘ⁽⁴⁾(θ) ≤ 0, and the defect vanishes exactly when θ ∈ 2πℤ.

### 4.1 Normalization and limit

Normalize by the matrix dimension:
```math
I_m(\theta)
=
\frac{\Delta_m^{(4)}(\theta)}{3^{m+1}+3}
=
-16\frac{3^{m-1}+1}{3^{m+1}+3}
\sin^2\left(\frac{\theta}{2}\right).
```
Since
```math
\frac{3^{m-1}+1}{3^{m+1}+3}
=
\frac{1}{9}\frac{3^m+3}{3^m+1},
```
we obtain
```math
I_m(\theta)
=
-\frac{16}{9}\sin^2\left(\frac{\theta}{2}\right)
-\frac{32}{9(3^m+1)}\sin^2\left(\frac{\theta}{2}\right).
```
Consequently,
```math
\boxed{
I_\infty(\theta)
=
\lim_{m\to\infty}I_m(\theta)
=
-\frac{16}{9}\sin^2\left(\frac{\theta}{2}\right)
}
```
and the exact finite-level remainder is
```math
\boxed{
I_m(\theta)-I_\infty(\theta)
=
-\frac{32}{9(3^m+1)}
\sin^2\left(\frac{\theta}{2}\right).
}
```
In particular, I∞(π/2) = −8/9. For θ ∉ 2πℤ, the ratio of successive absolute remainders is
```math
\frac{|I_{m+1}(\theta)-I_\infty(\theta)|}
{|I_m(\theta)-I_\infty(\theta)|}
=
\frac{3^m+1}{3^{m+1}+1}
\longrightarrow\frac13.
```
For θ ∈ 2πℤ, both remainders vanish identically, so this ratio is undefined. This is a limit of the normalized fourth-moment trace defect, not a statement about eigenvalue convergence or the spectral gap.

## 5. Lean proof architecture

The general-level proof uses the recursive gluing structure and two orientation states. Let Dₘ be the numbering-orientation defect and D̃ₘ the defect with the designated corner orientation flipped. Put s = sin(θ/2). Lean proves
```math
D_1=-32s^2,\qquad \widetilde D_1=0,
```
and
```math
\begin{aligned}
D_{m+1}&=2D_m+\widetilde D_m,\\
\widetilde D_{m+1}&=D_m+2\widetilde D_m,
\end{aligned}
\qquad m\geq1.
```

Set Sₘ = Dₘ + D̃ₘ and Eₘ = Dₘ − D̃ₘ. Then
```math
S_{m+1}=3S_m,\qquad E_{m+1}=E_m,
```
with S₁ = E₁ = −32s². Hence
```math
S_m=-32\cdot3^{m-1}s^2,\qquad E_m=-32s^2.
```
Recovering Dₘ = (Sₘ + Eₘ)/2 yields the main theorem. The proof uses recursive gluing, block-matrix trace identities, corner data, and orientation transport. Its principal modules include **GlueAlg**, **GlueBridge**, **GlueSG**, **GlueK**, **GlueCorner**, **FinalOrient**, **FinalTilde**, **FinalArith**, and **TildeEntries**.

The formalization README records that **traceDefect_closed** has no unproved placeholder and depends only on the standard Lean axioms **propext**, **Classical.choice**, and **Quot.sound**; this was re-checked with `#print axioms` on 27 November 2026.
The earlier hand-oriented manuscript **docs/PROOF.md** is not the machine-checked proof. The universal theorem should be cited through its Lean declaration and coupled-recursion route.

At the repository snapshot of 27 November 2026 (commit 46dcd2b53a8e232877f3082700e97d0571bf455a), the Lean sources comprise 78 modules with about 43,600 lines and about 1,370 theorems and lemmas. Two modules, **SanityChecks** and **H12OrbitInventory**, use `native_decide`; neither is among the transitive imports of the theorems named in this dissertation, so those theorems do not depend on the additional axiom that `native_decide` introduces.

## 6. Higher-moment results

### 6.1 Sixth moment

For the numbering-orientation quantity Dₘ⁽⁶⁾(θ), Lean proves
```math
D_{m+1}^{(6)}(\theta)
=
3D_m^{(6)}(\theta)+C_6(\theta),
\qquad m\geq3.
```
The exact finite certificate gives the level-two value
```math
D_2^{(6)}(\theta)
=
-14592s^2+1344cs^2-384s^3.
```
and the recurrence coefficient
```math
C_6(\theta)=4512s^2+192cs^2+768s^3.
```
For every m ≥ 2,
```math
\boxed{
D_m^{(6)}(\theta)
=
3^{m-2}D_2^{(6)}(\theta)
+
\frac{3^{m-2}-1}{2}C_6(\theta).
}
```
Equivalently,
```math
\boxed{
\begin{aligned}
D_m^{(6)}(\theta)
={}&-\bigl(12336\cdot3^{m-2}+2256\bigr)s^2\\
&+\bigl(1440\cdot3^{m-2}-96\bigr)cs^2
-384s^3.
\end{aligned}
}
```
At θ = π, C₆(π) = 5280.

**Proof boundary.** The recurrence for m ≥ 3 is proved in Lean. The exceptional m = 2 → 3 transition is certified by exact Gaussian-integer polynomial arithmetic in **computational/p6_level3_orientation_certificate.py** and tested in **tests/test_higher_moments.py**. This is exact symbolic evidence, but not yet a Lean-kernel theorem.

### 6.2 Eighth moment

For Dₘ⁽⁸⁾(θ), Lean proves
```math
D_{m+1}^{(8)}(\theta)
=
3D_m^{(8)}(\theta)+C_8(\theta),
\qquad m\geq3.
```
The exact certificate gives
```math
\begin{aligned}
D_2^{(8)}(\theta)
={}&-1335552s^2+244352cs^2-40064s^3\\
&+64cs^3+1920s^4,
\end{aligned}
```
and
```math
\begin{aligned}
C_8(\theta)
={}&193600s^2+75776cs^2+83712s^3\\
&-512cs^3+192s^4.
\end{aligned}
```
Thus, for every m ≥ 2,
```math
\boxed{
D_m^{(8)}(\theta)
=
3^{m-2}D_2^{(8)}(\theta)
+
\frac{3^{m-2}-1}{2}C_8(\theta).
}
```
At θ = π, C₈(π) = 277504.

**Proof boundary.** The structural recurrence is Lean-formalized for m ≥ 3. The exceptional m = 2 → 3 identity is computed coefficient-by-coefficient over Gaussian integers in **computational/p8_base_certificate.py**. It is exact and reproducible, but not yet a Lean-kernel theorem.

### 6.3 Tenth moment

The tenth-moment development contains an ordered p = 10 trace expansion, exact word-stratum reductions, gluing assembly, orientation recurrences, and transport of the required corner rows through degree nine.

The proposition **H10TransportAll** is proved by **H10TransportAll_proved** for both the face-axis and fixed-z configurations at every m ≥ 4. Lean proves unconditionally
```math
\boxed{
D_{m+1}^{(10)}(\theta)
=
3D_m^{(10)}(\theta)+C_{10}^{(5)}(\theta),
\qquad m\geq4,
}
```
and
```math
\boxed{
D_m^{(10)}(\theta)
=
3^{m-5}
\left(
D_5^{(10)}(\theta)+\frac{C_{10}^{(5)}(\theta)}{2}
\right)
-\frac{C_{10}^{(5)}(\theta)}{2},
\qquad m\geq5.
}
```
The exact correction C₁₀⁽⁵⁾(θ) is the finite trace expression **defectO10_num_residual_constant**. It has not yet been expanded as a trigonometric polynomial. This is a presentation task, not a missing hypothesis in the theorem.

### 6.4 Twelfth moment

Write D_m^(12)(θ) for the numbering-orientation quantity **defectO12** and C₁₂(θ) for the exact finite residual **defectO12_num_residual_constant**. For every real θ, Lean proves:

- **defectO12_succ_num_level3_constant_boundary**: the affine recurrence for every m ≥ 3,
```math
\boxed{
D_{m+1}^{(12)}(\theta)=3D_m^{(12)}(\theta)+C_{12}(\theta),\qquad m\geq3;
}
```
- **defectO12_num_finite_base_bridge_level3**: the finite bridge
```math
D_4^{(12)}(\theta)=3D_3^{(12)}(\theta)+C_{12}(\theta);
```
- **defectO12_num_affine_closed_form_from_level3_unconditional**: the affine closed form
```math
\boxed{
D_m^{(12)}(\theta)=3^{m-3}\left(D_3^{(12)}(\theta)+\frac{C_{12}(\theta)}2\right)-\frac{C_{12}(\theta)}2,\qquad m\geq3.
}
```

Here D₃⁽¹²⁾ and C₁₂ remain exact finite trace expressions in the Lean statements. A `#print axioms` check on 27 November 2026 reports only **propext**, **Classical.choice**, and **Quot.sound** for the recurrence and affine-closed-form theorems.

The development contains the ordered p = 12 trace expansion (**GlueTrace12**), the glued-row and orientation transport (**GlueRows12**, **GlueRows12Orientation**, **FinalOrient12**), and the final recurrence and closed form (**FinalClosed12**).

**Explicit polynomial form.** With c = cos(θ/2) and s = sin(θ/2), define
```math
\begin{aligned}
Q_3={}&-12c^6+24c^5s+1032c^5-2040c^4s-80120c^4\\
&+42894c^3s+2400282c^3-67494c^2s-30361019c^2\\
&-2479593cs+275590614c+3481440s-566815997,
\end{aligned}
```
```math
\begin{aligned}
Q_{12}={}&6c^6+6c^5s+240c^5-456c^4s-8858c^4\\
&+2466c^3s-33138c^3+618c^2s+1612501c^2\\
&+571254cs-18512844c-3259668s+13167067.
\end{aligned}
```
The exact finite identities are
```math
D_3^{(12)}(\theta)=32s^2Q_3(c,s),\qquad C_{12}(\theta)=-64s^2Q_{12}(c,s),
```
and therefore, for every m ≥ 3,
```math
\boxed{
D_m^{(12)}(\theta)=32s^2\Big[3^{m-3}\big(Q_3(c,s)-Q_{12}(c,s)\big)+Q_{12}(c,s)\Big].
}
```
The polynomial identity Q₃ − Q₁₂ = A and the affine polynomial rearrangement are checked coefficientwise in Lean (**H12PolynomialTargets**: **h12Q3_sub_Q12**, **h12_affine_polynomial_form**, **h12_scaled_affine_polynomial_form**).

At θ = π (c = 0, s = 1) the formula reads D_m^(12)(π) = −18,343,742,592 · 3^(m−3) + 317,036,768. For the first levels:

| m | D_m^(12)(π) |
|---:|---:|
| 3 | −18,026,705,824 |
| 4 | −54,714,191,008 |
| 5 | −164,776,646,560 |
| 6 | −494,964,013,216 |

Each of these four values agrees with an independent full-matrix Gaussian-integer calculation at θ = π (**tests/test_p12_explicit_closed_form.py**).

**Proof boundary.**

- *Lean-kernel theorems:* the recurrence for m ≥ 3, the finite bridge, and the affine closed form, with D₃ and C₁₂ as exact finite trace expressions.
- *Exact external certificates:* the identities D₃⁽¹²⁾ = 32s²Q₃ and C₁₂ = −64s²Q₁₂. They are verified in exact integer arithmetic, with no floating point, from the full finite operators at levels three and four, and the closed formula is checked at exact rational circle points and at θ = π. These two finite identities are not yet Lean-kernel theorems.
- The Lean modules **H12PolynomialTrace**, **H12PolynomialBridge**, **H12PolynomialGaussianCoefficientRecurrence** and **H12PolynomialGaussianExecutableRecurrence** contain infrastructure towards their Lean evaluation; that evaluation is not complete.

Stage notes: [Stage 6](formalization/H12_STAGE6_HANDOFF_2026-11-25.md) and [Stage 7](formalization/H12_STAGE7_POLYNOMIAL_REDUCTION_2026-11-26.md).

### 6.5 Finite H⁶ path classes

On SG(1), the exact length-six walk classification finds 66 walks in each one-triangle class, 168 in each two-triangle class, and 486 walks visiting all three elementary triangles. The first two groups contribute zero; the all-three-triangle group contributes nonzero. This is a finite-level result, not an all-level path-class theorem.

## 7. Numerical and exact-computation records

At θ = π/2, direct fourth-moment matrix calculations give:

| m | dim Hₘ | Iₘ(π/2) |
|---:|---:|---:|
| 1 | 12 | −1.333333 |
| 2 | 30 | −1.066667 |
| 3 | 84 | −0.952381 |
| 4 | 246 | −0.910569 |
| 5 | 732 | −0.896175 |
| 6 | 2190 | −0.891324 |
| 7 | 6564 | −0.889701 |

The held-out H⁴ matrix-power comparisons recorded in **VERIFICATION.md** have maximum listed absolute discrepancy 2.54 × 10⁻¹¹. The higher-moment regression table at θ = π/2 covers m = 1, …, 4 and is recorded in **docs/HIGHER_MOMENTS.md**. These finite tables are numerical checks, not the universal proof.

The Python tests also check selected vertex-wise gauge transformations. At level three, the recorded maximum spectral discrepancy is 7.99 × 10⁻¹⁵; the fourth-moment difference is zero at displayed precision. These checks are not assumptions in the Lean theorem.

For H¹², the exact record consists of three regression files: **tests/test_p12_level4_base_bridge.py** (the finite bridge D₄ − 3D₃ in circle-normal form), **tests/test_p12_level5_affine_constant.py** (the level-five constant), and **tests/test_p12_explicit_closed_form.py** (D₃ = 32s²Q₃, C₁₂ = −64s²Q₁₂, the closed formula at six exact rational circle points for m = 3, 4, and at θ = π for m = 3, …, 6). All use exact integer or rational arithmetic.

## 8. Reproducibility and proof artifacts

| Artifact | Role |
|---|---|
| **src/graph/sg_graph.py** | Recursive graph construction and counts. |
| **src/operators/operators.py** | Python graph operators and SU(2) connection. |
| **formalization/EvgenyTheorem/Operator.lean** | Concrete Lean operators and trace-defect definition. |
| **formalization/EvgenyTheorem/TildeEntries.lean** | Theorem **traceDefect_closed**. |
| **formalization/EvgenyTheorem/FinalTilde.lean** | Coupled H⁴ recurrences and H⁶ results. |
| **formalization/EvgenyTheorem/FinalClosed10.lean** | Unconditional H¹⁰ transport and affine theorem. |
| **formalization/EvgenyTheorem/FinalClosed12.lean** | H¹² recurrence, finite bridge and affine closed form for m ≥ 3. |
| **formalization/EvgenyTheorem/H12PolynomialTargets.lean** | Polynomials Q₃, Q₁₂ and their algebraic relations. |
| **computational/p6_level3_orientation_certificate.py** | Exact H⁶ transition certificate. |
| **computational/p8_base_certificate.py** | Exact H⁸ transition certificate. |
| **computational/higher_moment_p12_symbolic.py** | Exact H¹² trace-defect polynomials at levels three and four. |
| **computational/higher_moment_p12_level5_constant.py** | Exact H¹² level-five constant. |
| **tests/test_p12_explicit_closed_form.py**, **tests/test_p12_level4_base_bridge.py**, **tests/test_p12_level5_affine_constant.py** | Exact H¹² regression and consistency tests. |
| **docs/HIGHER_MOMENTS.md** | Higher-moment formulae and proof boundaries. |
| **docs/ORIENTATION_NOTE.md** | Orientation convention audit. |
| **VERIFICATION.md** | Numerical and held-out checks. |

From a clean checkout, run:
~~~bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r reproducibility/requirements.txt
pytest tests/ -m "not slow" -v
pytest tests/ -m slow -v
lake build
~~~
The Python suite checks numerical regressions and exact finite certificates. The Lean build checks formal proofs. A successful run certifies only the assertions actually executed by that run. The root **lakefile.toml** and **lean-toolchain** pin the Mathlib revision and Lean toolchain.

## 9. Limitations and non-claims

1. **No full-spectrum formula.** The fourth-moment trace identity does not determine all eigenvalues or the complete spectral distribution.
2. **No spectral-gap theorem.** No conclusion about the smallest positive eigenvalue follows from this identity alone.
3. **No complexity-theory result.** The closed form evaluates the scalar trace defect without constructing the full matrix. This is not a complexity-class separation, lower bound, or bit-complexity theorem.
4. **No silent change of orientation.** A different edge orientation defines a different operator family.
5. **No automatic extension to higher moments.** Each higher moment requires its own recurrence and boundary argument.
6. **No conflation of evidence.** Lean theorems, exact external certificates, and floating-point regressions are distinct. In particular, the two finite H¹² identities D₃ = 32s²Q₃ and C₁₂ = −64s²Q₁₂ are exact external certificates, not Lean-kernel theorems.
7. **No cross-project identification.** This work does not identify the SU(2) operators with signed Z₂-flux or spectral-decimation models.
8. **No physical-law claim.** All statements concern the graph operators defined in this repository.

The site's six-criterion protocol is a project-defined diagnostic for the normalized H⁴ invariant. It is not an external peer-review verdict and does not replace the theorem or its proof.

## 10. Conclusion

For the specified Sierpiński-gasket graph and vertex-index-oriented SU(2) connection, the fourth-moment trace defect has the exact all-level, all-angle formula
```math
\Delta_m^{(4)}(\theta)
=
-16(3^{m-1}+1)\sin^2\left(\frac{\theta}{2}\right).
```
The result is machine-checked in Lean 4. Its normalized form has an exact limit and a fully explicit finite-level remainder. The H⁶ and H⁸ developments combine Lean recurrences with exact finite transition certificates; the H¹⁰ recurrence and affine form are unconditional Lean theorems; the H¹² recurrence, finite bridge and affine form hold for every m ≥ 3 as Lean theorems, with an explicit polynomial form supported by exact certificates.

This dissertation consolidates a proved fourth-moment theorem and specific higher-moment advances. It does not claim that every related spectral question is closed. The full spectrum, spectral gap, Lean formalization of the H⁶/H⁸ finite bridges and of the two finite H¹² identities, and explicit trigonometric simplification of the H¹⁰ correction remain outside the principal H⁴ theorem.

## References and primary research artifacts

1. [Evgeny-Theorem repository](https://github.com/RFT-SIRM/Evgeny-Theorem) — source, formalization, certificates, tests, and research records.
2. [THEOREM.md](THEOREM.md) — statement of the fourth-moment identity.
3. [Lean formalization guide](formalization/README.md) — theorem declaration, proof architecture, axioms, and build instructions.
4. [Higher-moment results](docs/HIGHER_MOMENTS.md) — detailed H⁶, H⁸, H¹⁰, and H¹² formulae.
5. [Orientation note](docs/ORIENTATION_NOTE.md) — edge-orientation convention.
6. [Verification record](VERIFICATION.md) — finite numerical and held-out checks.
7. [Lean proof-work log](formalization/PROOF_WORK_LOG.md) and [higher-moment research log](formalization/HIGHER_MOMENT_RESEARCH_LOG.md) — chronological research records.
8. [H¹² Stage 6 handoff](formalization/H12_STAGE6_HANDOFF_2026-11-25.md) and [Stage 7 polynomial reduction](formalization/H12_STAGE7_POLYNOMIAL_REDUCTION_2026-11-26.md) — the H¹² Lean recurrence and its polynomial reduction.
9. Preprint of an earlier version (moments up to the tenth): [aiXiv:2611.01439](https://aixiv.online/abs/2611.01439), 14 November 2026.

## Use of AI tools

The research was carried out within the author's RFT–SIRM framework, where SIRM denotes the project's Synthetic Intelligence Reasoning Model, its invariant-driven reasoning and systems-engineering model, in which the initial conception of the project was formulated. In addition, general-purpose large language model assistants were used during development as aids for writing code, for proof engineering in Lean, and for drafting and editing text. The validity of every Lean proof is checked by the Lean kernel, and the exact certificates are reproducible with the code in this repository; the author reviewed the results and takes full responsibility for the content of this document.

---

*This document is a research dissertation/monograph about the mathematics maintained in this repository. It is not a claim of an academic degree and contains no material from the separate “Theory of Everything” project.*
