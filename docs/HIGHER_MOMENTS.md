# Higher spectral moments: H⁶, H⁸, and H¹⁰

This note records the current mathematical and formal status of the higher spectral moments for the SU(2)-valued operators defined in this repository. It separates all-level recurrence proofs from finite exact certificates and numerical reference data.

## Status at a glance

| Moment | Established result | Remaining proof boundary |
|---|---|---|
| **H⁴** | Unconditional all-angle closed form, Lean-checked for every $m\ge1$. | None for the stated theorem. |
| **H⁶** | Lean recurrence for $m\ge3$, plus an exact finite symbolic bridge for $m=2\to3$. Combined all-angle formula for $m\ge2$. | The finite bridge is not yet a Lean-kernel theorem. |
| **H⁸** | Lean recurrence for $m\ge3$, plus an exact sparse-polynomial bridge for $m=2\to3$. Combined all-angle formula for $m\ge2$. | The finite bridge is not yet a Lean-kernel theorem. |
| **H¹⁰** | Unconditional Lean-checked affine recurrence for m ≥ 4 and affine form for m ≥ 5. | Radius-four transport is proved through degree nine for both axes; the level-five constant remains an exact trace expression. |

H⁴ is stated in [THEOREM.md](../THEOREM.md). The detailed tenth-moment Lean layer is in `formalization/EvgenyTheorem/GlueTrace10.lean`, `GlueRows10.lean`, `FinalOrient10.lean`, and `FinalClosed10.lean`.

---

## Notation

For $p\in\{6,8,10\}$, let $\Delta_m^{(p)}(\theta)$ be the difference between the p-th traces of the non-commuting SU(2) configuration and the commuting control. For the level-dependent recurrences below, $D_m^{(p)}(\theta)$ denotes the orientation-specific defect used in the corresponding Lean declarations.

Throughout this note,

$$
c=\cos(\theta/2),\quad s=\sin(\theta/2).
$$

The names `defectO6`, `defectO8`, and `defectO10` refer to the concrete Lean definitions. The superscripts in $D_m^{(p)}$ label the moment order; they are not powers of $D_m$.

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

## Numerical reference values

The following table records direct numerical regression values at $\theta=\pi/2$. The table is a finite computational record; it is not the proof of the all-angle H⁶/H⁸ identities and does not discharge the H¹⁰ transport hypothesis.

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
