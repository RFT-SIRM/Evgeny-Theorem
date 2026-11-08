# Spectral Trace Defects of Noncommutative SU(2) Connections on Sierpiński-Gasket Graphs

## Research dissertation

**Author:** Evgeny Zaprudnov  
**Research group:** RFT-SIRM  
**Version:** 1.0  
**Date:** 8 November 2026  
**Project:** [RFT-SIRM/Evgeny-Theorem](https://github.com/RFT-SIRM/Evgeny-Theorem)

---

## Abstract

This dissertation studies trace defects of recursively defined graph operators on finite Sierpiński-gasket approximations. Each vertex carries a two-component complex state, and the edges carry an SU(2)-valued connection. Two configurations are compared on the same graph: a non-commuting connection whose flux-edge axes cycle through x, y, z, and a commuting control that uses the fixed z-axis.

The principal theorem is the exact identity
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

The H⁶ and H⁸ finite bridges are exact and reproducible but are not yet formalized inside the Lean kernel. By contrast, the H¹⁰ recurrence does not retain an unproved transport hypothesis: the required transport statement is itself proved in Lean. Simplifying its correction coefficient would improve its presentation, but is not required for the unconditional theorem.

This work does not claim a formula for all eigenvalues, the spectral gap, a computational-complexity classification, or a physical law.

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
For the higher-moment Lean statements, Dₘ⁽ᵖ⁾(θ) denotes the corresponding numbering-orientation quantity defined by **defectO6**, **defectO8**, and **defectO10**.

For the polynomial formulae below, write
```math
\phi=\frac{\theta}{2},\qquad
c=\cos\phi,\qquad s=\sin\phi,\qquad c^2+s^2=1.
```

## 4. Main theorem: the fourth spectral moment

### Theorem 4.1 — exact fourth-moment trace defect

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
In particular, I∞(π/2) = −8/9, and the ratio of successive absolute remainders tends to 1/3. This is a limit of the normalized fourth-moment trace defect, not a statement about eigenvalue convergence or the spectral gap.

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

The formalization README records that **traceDefect_closed** has no unproved placeholder and depends only on the standard Lean axioms
The theorem depends on the standard Lean axioms **propext**, **Classical.choice**, and **Quot.sound**.
The earlier hand-oriented manuscript **docs/PROOF.md** is not the machine-checked proof. The universal theorem should be cited through its Lean declaration and coupled-recursion route.

## 6. Higher-moment results

### 6.1 Sixth moment

For the numbering-orientation quantity Dₘ⁽⁶⁾(θ), Lean proves
```math
D_{m+1}^{(6)}(\theta)
=
3D_m^{(6)}(\theta)+C_6(\theta),
\qquad m\geq3.
```
The exact finite certificate gives
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

### 6.4 Finite H⁶ path classes

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

## 8. Reproducibility and proof artifacts

| Artifact | Role |
|---|---|
| **src/graph/sg_graph.py** | Recursive graph construction and counts. |
| **src/operators/operators.py** | Python graph operators and SU(2) connection. |
| **formalization/EvgenyTheorem/Operator.lean** | Concrete Lean operators and trace-defect definition. |
| **formalization/EvgenyTheorem/TildeEntries.lean** | Theorem **traceDefect_closed**. |
| **formalization/EvgenyTheorem/FinalTilde.lean** | Coupled H⁴ recurrences and H⁶ results. |
| **formalization/EvgenyTheorem/FinalClosed10.lean** | Unconditional H¹⁰ transport and affine theorem. |
| **computational/p6_level3_orientation_certificate.py** | Exact H⁶ transition certificate. |
| **computational/p8_base_certificate.py** | Exact H⁸ transition certificate. |
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
6. **No conflation of evidence.** Lean theorems, exact external certificates, and floating-point regressions are distinct.
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
The result is machine-checked in Lean 4. Its normalized form has an exact limit and a fully explicit finite-level remainder. The H⁶ and H⁸ developments combine Lean recurrences with exact finite transition certificates; the H¹⁰ recurrence and affine form are unconditional Lean theorems.

This dissertation consolidates a proved fourth-moment theorem and specific higher-moment advances. It does not claim that every related spectral question is closed. The full spectrum, spectral gap, Lean formalization of the H⁶/H⁸ finite bridges, and explicit trigonometric simplification of the H¹⁰ correction remain outside the principal H⁴ theorem.

## References and primary research artifacts

1. [Evgeny-Theorem repository](https://github.com/RFT-SIRM/Evgeny-Theorem) — source, formalization, certificates, tests, and research records.
2. [THEOREM.md](../THEOREM.md) — statement of the fourth-moment identity.
3. [Lean formalization guide](../formalization/README.md) — theorem declaration, proof architecture, axioms, and build instructions.
4. [Higher-moment results](HIGHER_MOMENTS.md) — detailed H⁶, H⁸, and H¹⁰ formulae.
5. [Orientation note](ORIENTATION_NOTE.md) — edge-orientation convention.
6. [Verification record](../VERIFICATION.md) — finite numerical and held-out checks.
7. [Lean proof-work log](../formalization/PROOF_WORK_LOG.md) and [higher-moment research log](../formalization/HIGHER_MOMENT_RESEARCH_LOG.md) — chronological research records.

---

*This document is a research dissertation/monograph about the mathematics maintained in this repository. It is not a claim of an academic degree and contains no material from the separate “Theory of Everything” project.*
