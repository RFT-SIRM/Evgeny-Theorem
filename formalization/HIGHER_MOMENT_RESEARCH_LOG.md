# Higher-Moment Formalization Research Log

**Status:** research notes; not a Lean proof or a theorem claim.  
**Scope:** extending the existing fourth-moment gluing argument to moments (p=6,8,10).  
**Policy:** keep proved statements, numerical evidence, and conjectures explicitly separate.

## 1. Current formalization baseline

The existing Lean development contains the fourth-moment gluing lemma `glue_trace4` in
`formalization/EvgenyTheorem/GlueAlg.lean`. Its hypotheses include block diagonality of
`K`, a vanishing condition for distinct glued vertices, and the corner condition
`GlueDiag G (K * K)`. The conclusion expresses the fourth-power trace after gluing as the
unglued trace plus explicit corner terms involving powers through (K^3).

This is the current reusable formal baseline. It does **not** itself prove the corresponding
formula for moments 6, 8, or 10.

## 2. Definitions for the higher-moment target

For a fixed angle θ and an even moment (p), let
[
\Delta_m^{(p)}(\theta)
 = \operatorname{Tr}(H_C(m,\theta)^p)
 - \operatorname{Tr}(H_{C'}(m,\theta)^p),
\qquad
R_m^{(p)}(\theta)
 = \Delta_m^{(p)}(\theta)-3\Delta_{m-1}^{(p)}(\theta).
]

For (p\in\{6,8,10\}), the working target is the eventual residual identity
[
R_m^{(p)}(\theta)=R_4^{(p)}(\theta),\qquad m\ge 3,
]
under the project's exact operator and gluing hypotheses. This remains a **conjectural target** until a complete proof and a successful Lean build establish it. No all-level higher-moment theorem is claimed here.

## 3. Exact combinatorial counts

Expanding ((K+KN)^p) gives (2^p) binary words of length (p), where each position chooses (K) or (KN). Excluding the all-(K) word leaves (2^p-1) words containing at least one (N).

The number of binary necklaces (cyclic-rotation classes) of length (p) over two symbols is
[
\frac{1}{p}\sum_{d\mid p}\varphi(d)2^{p/d}.
]
For the three target moments, this gives:

| (p) | All binary words (2^p) | Words containing (N) | Binary necklaces total | Nonempty-(N) necklace classes |
|---:|---:|---:|---:|---:|
| 6 | 64 | 63 | 14 | 13 |
| 8 | 256 | 255 | 36 | 35 |
| 10 | 1024 | 1023 | 108 | 107 |

These are **combinatorial counts only**. Necklace classes are not yet a trace identity: cyclic trace equivalence, matrix constraints, vanishing terms, and multiplicities must be handled explicitly. In particular, the class with exactly one (N) is represented by (\operatorname{Tr}(K^pN)) after cyclic rotation and vanishes if (K^p) is block diagonal across the paired copy classes, as in the existing `trace_BD_N` lemma.

A related but different enumeration describes cyclic compositions: for (r\) occurrences of (N), it groups positive gap lengths (a_1,\ldots,a_r) with sum (p), modulo cyclic rotation. These composition counts must not be conflated with binary-necklace counts, and neither count alone supplies the coefficients of the final trace formula.

## 4. Computational evidence (not formal proof)

Independent numerical work recorded during this research found, at (\theta=\pi), the following residual values:
- (p=6): (R_2=5256), (R_3=5280), and (R_m=5280) for the tested levels (4\le m\le10).
- (p=8): (R_2=268960), (R_3=277504), and (R_m=277504) for the tested levels (4\le m\le10).
- (p=10): (R_2=4006040), (R_3=4507520), and (R_m=4507520) for the tested levels (4\le m\le10).

Additional floating-point checks across angles and a modular/DFT check were reported to support the finite-level relation (R_3^{(p)}=R_4^{(p)}) for (p=6,8,10). However, the full independent calculation is not yet packaged in this repository as a reproducible, reviewed certificate. These observations must therefore be treated as **computational evidence**, not as a machine-checked theorem. They do not prove the all-level recurrence.

## 5. Proof obligations before claiming closure

1. Prove a general finite expansion of (\operatorname{Tr}((K+KN)^p)) that records multiplicities and cyclic classes without losing ordering information.
2. Prove, under explicit hypotheses, that terms with one (N) vanish by block diagonality; do not assume that all other terms vanish.
3. Derive the remaining boundary expression in terms of marked corner entries of (K^j), with (j\le p-1), and state every required corner-separation/vanishing hypothesis.
4. Prove that the relevant marked corner blocks are equivalent for the two orientations. Graph-neighborhood isomorphism alone is insufficient unless it preserves the operator labels or an explicit basis transformation is supplied.
5. Establish the finite base transition for (R_3=R_4) with an independently reproducible exact certificate or a direct formal proof.
6. Prove the level-to-level recurrence (or another valid induction step) that propagates the residual identity to every claimed level.
7. Compile the Lean project from a clean checkout and record the exact toolchain and successful build output before describing any result as machine-checked.

## 6. Intended Lean decomposition

A maintainable route is to separate the proof into:
- a generic algebraic expansion/collection lemma for arbitrary (p);
- a gluing-boundary formula expressed through corner matrix entries;
- geometric lemmas proving the required corner-block relations for the concrete graph operators;
- the finite base case and the induction/recurrence theorem.

The existing fourth-moment result should remain unchanged while these components are developed. Do not weaken hypotheses or introduce axioms, `sorry`, or an unverified all-level claim merely to make the higher-moment statement appear closed.

## 7. Status summary

- **Machine-checked:** the existing fourth-moment development, subject to the repository's actual current build status.
- **Combinatorially counted:** binary words and cyclic-rotation classes listed above.
- **Numerically supported:** finite-level higher-moment residual patterns described above; reproducible artifact still to be added.
- **Not yet proved/formalized here:** the all-level (p=6,8,10) residual identity and its propagation.
