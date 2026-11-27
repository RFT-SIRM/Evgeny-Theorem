# Higher spectral moments: H⁶, H⁸, H¹⁰, and H¹²

This note records the current mathematical and formal status of the higher spectral moments for the SU(2)-valued operators defined in this repository. It separates all-level recurrence proofs from finite exact certificates and numerical reference data.

## Status at a glance

| Moment | Established result | Remaining proof boundary |
|---|---|---|
| **H⁴** | Unconditional all-angle closed form, Lean-checked for every $m\ge1$. | None for the stated theorem. |
| **H⁶** | Lean recurrence for $m\ge3$, plus an exact finite symbolic bridge for $m=2\to3$. Combined all-angle formula for $m\ge2$. | The finite bridge is not yet a Lean-kernel theorem. |
| **H⁸** | Lean recurrence for $m\ge3$, plus an exact sparse-polynomial bridge for $m=2\to3$. Combined all-angle formula for $m\ge2$. | The finite bridge is not yet a Lean-kernel theorem. |
| **H¹⁰** | Unconditional Lean-checked affine recurrence for m ≥ 4 and affine form for m ≥ 5. | Radius-four transport is proved through degree nine for both axes; the level-five constant remains an exact trace expression. |
| **H¹²** | Lean-checked affine recurrence for $m\ge3$ and affine closed form for $m\ge3$, with the explicit all-angle polynomial $D_m=32s^2\big(3^{m-3}(Q_3-Q_{12})+Q_{12}\big)$. | The two finite identities $D_3=32s^2Q_3$ and $C_{12}=-64s^2Q_{12}$ are exact symbolic certificates, not yet Lean-kernel theorems. |

H⁴ is stated in [THEOREM.md](../THEOREM.md). The detailed tenth-moment Lean layer is in `formalization/EvgenyTheorem/GlueTrace10.lean`, `GlueRows10.lean`, `FinalOrient10.lean`, and `FinalClosed10.lean`.

---

## Notation

For $p\in\{6,8,10,12\}$, let $\Delta_m^{(p)}(\theta)$ be the difference between the p-th traces of the non-commuting SU(2) configuration and the commuting control. For the level-dependent recurrences below, $D_m^{(p)}(\theta)$ denotes the orientation-specific defect used in the corresponding Lean declarations.

Throughout this note,

$$
c=\cos(\theta/2),\quad s=\sin(\theta/2).
$$

The names `defectO6`, `defectO8`, `defectO10`, and `defectO12` refer to the concrete Lean definitions. The superscripts in $D_m^{(p)}$ label the moment order; they are not powers of $D_m$.

---

## H⁶ — all-angle recurrence and explicit formula

Write $D_m^{(6)}(\theta)$ for the level-$m$ numbering-orientation quantity defined by `defectO6`.

The Lean proof establishes

$$
D_{m+1}^{(6)}(\theta)=3D_m^{(6)}(\theta)+C_6(\theta),\quad m\ge3.
$$

The exact finite polynomial certificate establishes the exceptional level-two transition. The level-two value and recurrence coefficient are

$$
D_2^{(6)}(\theta)=-14592s^2+1344cs^2-384s^3.
$$

$$
C_6(\theta)=4512s^2+192cs^2+768s^3.
$$

Combining the Lean recurrence with the exact finite transition gives, for every $m\ge2$,

$$
D_m^{(6)}(\theta)=3^{m-2}D_2^{(6)}(\theta)+\frac{3^{m-2}-1}{2}C_6(\theta).
$$

Equivalently,

$$
D_m^{(6)}(\theta)=-(12336\cdot3^{m-2}+2256)s^2+(1440\cdot3^{m-2}-96)cs^2-384s^3.
$$

At $\theta=\pi$, the coefficient is exactly $C_6(\pi)=5280$.

**Proof boundary.** The recurrence theorem `defectO6_num_growth_recurrence` is in `formalization/EvgenyTheorem/FinalTilde.lean` and is Lean-proved for $m\ge3$. The exceptional finite transition is certified by exact Gaussian-integer polynomial arithmetic, with code in `computational/p6_level3_orientation_certificate.py` and regression checks in `tests/test_higher_moments.py`. No floating-point angle grid is used to establish the symbolic bridge. The finite transition is exact, but it is not yet a Lean-kernel theorem.

### H⁶ path-class result on the first gasket

On $SG(1)$, closed walks of length six can be classified by which elementary triangles they visit. The exact finite-level calculation gives:

| Triangles visited | Number of walks | Contribution to the H⁶ defect |
|---|---:|---:|
| One triangle | 66 in each class | Zero |
| Two triangles | 168 in each class | Zero |
| All three triangles | 486 | Nonzero |

At this finite level, only walks that sample all three rotation axes contribute. This statement concerns the first gasket and the enumerated length-six walks; it is not asserted as an all-level path-class theorem.

---

## H⁸ — all-angle affine law and explicit formula

Write $D_m^{(8)}(\theta)$ for the level-$m$ numbering-orientation quantity defined by `defectO8`.

The Lean development proves the all-angle recurrence

$$
D_{m+1}^{(8)}(\theta)=3D_m^{(8)}(\theta)+C_8(\theta),\quad m\ge3.
$$

The exact sparse-polynomial certificate gives

$$
D_2^{(8)}(\theta)=-1335552s^2+244352cs^2-40064s^3+64cs^3+1920s^4.
$$

$$
C_8(\theta)=193600s^2+75776cs^2+83712s^3-512cs^3+192s^4.
$$

It also verifies the finite transition identity

$$
D_3^{(8)}-3D_2^{(8)}=D_4^{(8)}-3D_3^{(8)}=C_8(\theta).
$$

Consequently, for every $m\ge2$,

$$
D_m^{(8)}(\theta)=3^{m-2}D_2^{(8)}(\theta)+\frac{3^{m-2}-1}{2}C_8(\theta).
$$

At $\theta=\pi$, the exact coefficient is $C_8(\pi)=277504$.

**Proof boundary.** The recurrence is Lean-formalized for $m\ge3$. The exceptional finite $m=2\to3$ identity is computed coefficient-by-coefficient over Gaussian integers in `computational/p8_base_certificate.py`. It is an exact reproducible certificate, not yet a Lean-kernel theorem. No sampled-angle fit is used.

---


## H¹⁰ — p=10 gluing and unconditional affine closed form

The tenth-moment proof layer goes beyond numerical trace tables. The current Lean source includes:

- the ordered p=10 gluing assembly, theorem `pOpO_trace10_glue_final`;
- the exact even-word-stratum aggregation and the zero-insertion term;
- recurrences for the numbering orientation and the flipped-corner orientation;
- transfer of the corner-flip rows through powers up to nine;
- the radius-four glued-state diagonal transport through degree nine, proved for both configurations at every level m ≥ 4.

Write $D_m^{(10)}(\theta)$ for the level-$m$ numbering-orientation quantity defined by `defectO10`. The level-five residual is named `defectO10_num_residual_constant` in Lean; denote it by $C_{10}^{(5)}(\theta)$. Its current definition is an exact finite trace expression.

The transport proposition is explicitly named `H10TransportAll`. It requires the glued-state diagonal powers through degree nine to agree between adjacent levels, for both the face-axis and fixed-axis configurations, at every level m ≥ 4. This radius-four corner-locality statement is now proved by `H10TransportAll_proved`, using the concrete degree-eight/nine partner bridges and the state-level transport theorem in `FinalTilde.lean`.

Lean therefore proves unconditionally

$$
D_{m+1}^{(10)}(\theta)=3D_m^{(10)}(\theta)+C_{10}^{(5)}(\theta),\quad m\ge4.
$$

The corresponding affine form is

$$
D_m^{(10)}(\theta)=3^{m-5}(D_5^{(10)}(\theta)+C_{10}^{(5)}(\theta)/2)-C_{10}^{(5)}(\theta)/2,\quad m\ge5.
$$

The recurrence and affine formula are machine-checked without an additional transport hypothesis. The exact level-five correction $C_{10}^{(5)}(\theta)$ has not yet been simplified to an explicit trigonometric polynomial; it remains a named exact trace expression. This concerns the presentation of the coefficient, not a remaining hypothesis in the Lean theorem.

### H¹⁰ source map

| Component | Lean module | Role |
|---|---|---|
| Tenth-power trace expansion and word strata | `GlueTrace.lean` and `TraceExpand.lean` | Exact ordered-word expansion and stratum reductions. |
| p=10 gluing assembly | `GlueTrace10.lean` | Connects the ordered expansion to the tenth-moment boundary expression. |
| Glued-row transport | `GlueRows10.lean` | Establishes corner-flip row identities through degree nine and transports the boundary correction. |
| Radius-four corner transport | `FinalTilde.lean` and `FinalClosed10.lean` | Proves degree-eight/nine partner transport, combines degrees one through nine, and establishes `H10TransportAll_proved`. |
| Unconditional affine recurrence and form | `FinalClosed10.lean` | Proves `defectO10_succ_num_level5_constant_boundary_unconditional` and `defectO10_num_affine_closed_form_from_level5_unconditional`. |


---

## H¹² — p=12 affine recurrence and explicit all-angle polynomial

Write $D_m^{(12)}(\theta)$ for the level-$m$ numbering-orientation defect `defectO12`, and $C_{12}(\theta)$ for the exact finite residual `defectO12_num_residual_constant`. For every real $\theta$, Lean proves:

- `defectO12_succ_num_level3_constant_boundary`: $D_{m+1}^{(12)}(\theta)=3D_m^{(12)}(\theta)+C_{12}(\theta)$ for every $m\ge3$;
- `defectO12_num_finite_base_bridge_level3`: the finite bridge $D_4^{(12)}=3D_3^{(12)}+C_{12}$, derived from the level-three boundary and orientation-invariance theorems;
- `defectO12_num_affine_closed_form_from_level3_unconditional`: for every $n\ge0$,

$$
D_{n+3}^{(12)}(\theta)=3^n\left(D_3^{(12)}(\theta)+\frac{C_{12}(\theta)}2\right)-\frac{C_{12}(\theta)}2 .
$$

In these Lean statements $D_3^{(12)}$ and $C_{12}$ are exact finite trace expressions.

### Explicit polynomial form

With $c=\cos(\theta/2)$, $s=\sin(\theta/2)$ and $c^2+s^2=1$, the finite quantities are

$$
D_3^{(12)}(\theta)=32s^2Q_3(c,s),\qquad C_{12}(\theta)=-64s^2Q_{12}(c,s),
$$

where

$$
\begin{aligned}
Q_3={}&-12c^6+24c^5s+1032c^5-2040c^4s-80120c^4\\
&+42894c^3s+2400282c^3-67494c^2s-30361019c^2\\
&-2479593cs+275590614c+3481440s-566815997,
\end{aligned}
$$

$$
\begin{aligned}
Q_{12}={}&6c^6+6c^5s+240c^5-456c^4s-8858c^4\\
&+2466c^3s-33138c^3+618c^2s+1612501c^2\\
&+571254cs-18512844c-3259668s+13167067.
\end{aligned}
$$

Consequently, for every $m\ge3$,

$$
D_m^{(12)}(\theta)=32s^2\Big(3^{m-3}\big(Q_3(c,s)-Q_{12}(c,s)\big)+Q_{12}(c,s)\Big).
$$

At $\theta=\pi$ ($c=0$, $s=1$) this reads $D_m^{(12)}(\pi)=-18{,}343{,}742{,}592\cdot3^{m-3}+317{,}036{,}768$.

The algebraic part of this presentation is machine-checked: `h12Q3_sub_Q12`, `h12_affine_polynomial_form` and `h12_scaled_affine_polynomial_form` in `H12PolynomialTargets.lean` prove $Q_3-Q_{12}=A$ and the equivalent forms of the affine polynomial identity for every natural exponent.

### H¹² proof boundary

- **Lean-kernel theorem:** the recurrence for $m\ge3$, the finite bridge $D_4=3D_3+C_{12}$, and the affine closed form with $D_3$ and $C_{12}$ kept as exact finite trace expressions.
- **Exact symbolic certificate:** the identities $D_3^{(12)}=32s^2Q_3$ and $C_{12}=-64s^2Q_{12}$. They are verified in exact integer arithmetic, with no floating point, from the full finite operators at levels three and four, by `tests/test_p12_explicit_closed_form.py` (which also checks the closed formula at exact rational circle points and, by an independent Gaussian-integer calculation at $\theta=\pi$, for levels three to six), `tests/test_p12_level4_base_bridge.py` and `tests/test_p12_level5_affine_constant.py`. These two finite identities are **not yet Lean-kernel theorems**.
- The Lean modules `H12PolynomialTrace`, `H12PolynomialBridge`, `H12PolynomialGaussianCoefficientRecurrence` and `H12PolynomialGaussianExecutableRecurrence` contain infrastructure towards the Lean evaluation of the two finite identities. That evaluation is not complete.

### H¹² source map

| Component | Lean module | Role |
|---|---|---|
| Twelfth-power trace expansion and word strata | `GlueTrace12.lean` | Exact ordered-word expansion for $p=12$. |
| Glued-row and orientation transport | `GlueRows12.lean`, `GlueRows12Orientation.lean`, `FinalOrient12.lean` | Corner-flip rows, positive even-stratum transport, orientation invariance. |
| Affine recurrence and closed form | `FinalClosed12.lean` | Proves the recurrence for $m\ge3$, the finite bridge, and the affine closed form. |
| Polynomial presentation | `H12PolynomialTargets.lean`, `H12PolynomialClosedForm.lean` | Defines $Q_3$, $Q_{12}$, $A$ and proves their algebraic relations. |

Stage notes: [Stage 6](../formalization/H12_STAGE6_HANDOFF_2026-11-25.md) and [Stage 7](../formalization/H12_STAGE7_POLYNOMIAL_REDUCTION_2026-11-26.md).

---

## Numerical reference values

The following table records direct numerical regression values at $\theta=\pi/2$. These finite values are regression anchors, not proofs of the all-angle H⁶/H⁸ identities or the H¹⁰ recurrence. The H¹⁰ transport and its unconditional affine recurrence/form are proved separately in Lean, as described above.

| $m$ | $\Delta_m(H^6,\pi/2)$ | $\Delta_m(H^8,\pi/2)$ | $\Delta_m(H^{10},\pi/2)$ |
|---:|---:|---:|---:|
| 1 | −3180.000000000000 | −246909.026268397924 | −14013358.982483163476 |
| 2 | −6956.588745030516 | −595053.284942481667 | −37686518.369789719582 |
| 3 | −18274.354980121832 | −1632052.331668503582 | −107772338.487565994263 |
| 4 | −52227.653685396537 | −4743049.471846580505 | −318029798.840893745422 |

These values are locked by `tests/test_higher_moments.py`. Additional exact angle-$\pi$ certificates are maintained in `computational/higher_moment_pi_certificate.py`.

---

## How to read the evidence

- **Lean-kernel theorem:** the proposition and proof are checked by Lean under the displayed hypotheses.
- **Exact symbolic certificate:** a finite algebraic identity is verified without floating-point sampling. It may still be outside the Lean kernel.
- **Numerical regression:** a reproducible finite computation checked against fixed reference values. It is not an all-level proof.
- **Conditional theorem:** Lean verifies the implication from an explicitly stated hypothesis; the hypothesis must still be proved before the result is unconditional.

The source journals preserve the chronology and details of the formalization:

- [Higher-moment research log](../formalization/HIGHER_MOMENT_RESEARCH_LOG.md)
- [Lean proof-work log](../formalization/PROOF_WORK_LOG.md)

These journals are intentionally retained as research records. This page is their organized mathematical summary, not a replacement for the underlying history.
