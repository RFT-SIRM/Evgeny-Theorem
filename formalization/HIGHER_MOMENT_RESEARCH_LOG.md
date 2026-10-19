# Higher-Moment Formalization Research Log

**Status:** research notes; not a Lean proof or a theorem claim.  
**Scope:** extending the existing fourth-moment gluing argument to moments $p\in\{6,8,10\}$.   
**Policy:** keep proved statements, numerical evidence, and conjectures explicitly separate.

## 1. Current formalization baseline

The existing Lean development contains the fourth-moment gluing lemma `glue_trace4` in
`formalization/EvgenyTheorem/GlueAlg.lean`. Its hypotheses include block diagonality of
`K`, a vanishing condition for distinct glued vertices, and the corner condition
`GlueDiag G (K * K)`. The conclusion expresses the fourth-power trace after gluing as the
unglued trace plus explicit corner terms involving powers through $K^3$.

This is the current reusable formal baseline. It does **not** itself prove the corresponding
formula for moments 6, 8, or 10.

## 2. Definitions for the higher-moment target

For a fixed angle $\theta$ and an even moment $p$, define the trace defect and its residual by

$$
\Delta_m^{(p)}(\theta)
= \operatorname{Tr}\!\left(H_C(m,\theta)^p\right)
- \operatorname{Tr}\!\left(H_{C'}(m,\theta)^p\right),
\qquad
R_m^{(p)}(\theta)
= \Delta_m^{(p)}(\theta)-3\Delta_{m-1}^{(p)}(\theta).
$$

For $p\in\{6,8,10\}$, the working target is the eventual residual identity

$$
R_m^{(p)}(\theta)=R_4^{(p)}(\theta),
\qquad m\ge 3.
$$

This target is conditional on the project's exact operator and gluing hypotheses. It remains a **conjecture** until a complete proof is established; the current Lean formalization does not claim an all-level theorem for moments $p=6,8,10$.

## 3. Exact combinatorial counts

Expanding $(K+KN)^p$ gives $2^p$ binary words of length $p$, where each position chooses $K$ or $KN$. Excluding the all-$K$ word leaves $2^p-1$ words containing at least one $N$.

The number of binary necklaces (cyclic-rotation classes) of length $p$ over two symbols is
\[
\frac{1}{p}\sum_{d\mid p}\varphi(d)\,2^{p/d}.
\]
For the three target moments, this gives:

| $p$ | All binary words $2^p$ | Words containing $N$ | Binary necklaces total | Nonempty-$N$ necklace classes |
|---:|---:|---:|---:|---:|
| 6 | 64 | 63 | 14 | 13 |
| 8 | 256 | 255 | 36 | 35 |
| 10 | 1024 | 1023 | 108 | 107 |

These are **combinatorial counts only**. Necklace classes are not yet a trace identity: cyclic trace equivalence, matrix constraints, vanishing terms, and multiplicities must be handled explicitly. In particular, the class with exactly one $N$ is represented by $\operatorname{Tr}(K^pN)$ after cyclic rotation and vanishes if $K^p$ is block diagonal across the paired copy classes, as in the existing `trace_BD_N` lemma.

A related but different enumeration describes cyclic compositions: for $r$ occurrences of $N$, it groups positive gap lengths $(a_1,\ldots,a_r)$ with sum $p$, modulo cyclic rotation. These composition counts must not be conflated with binary-necklace counts, and neither count alone supplies the coefficients of the final trace formula.

## 4. Computational evidence (not formal proof)

Independent numerical work recorded during this research found, at $\theta=\pi$, the following residual values:
- $p=6$: $R_2=5256$, $R_3=5280$, and $R_m=5280$ for tested levels $4\le m\le10$.
- $p=8$: $R_2=268960$, $R_3=277504$, and $R_m=277504$ for tested levels $4\le m\le10$.
- $p=10$: $R_2=4006040$, $R_3=4507520$, and $R_m=4507520$ for tested levels $4\le m\le10$.

Additional floating-point checks across angles and a modular/DFT check were reported to support the finite-level relation $R_3^{(p)}=R_4^{(p)}$ for $p\in\{6,8,10\}$. However, the full independent calculation is not yet packaged in this repository as a reproducible, reviewed certificate. These observations must therefore be treated as **computational evidence**, not as a machine-checked theorem. They do not prove the all-level recurrence.

## 4a. Machine-checked reusable lemmas now in `main`

The Lean development contains the arbitrary-exponent block-diagonal lemmas
`blockK_pow` and `trace_blockK_pow` in `formalization/EvgenyTheorem/GlueTrace.lean`.
These remove the exponent-four restriction from the **block-diagonal step only**.

The ordered-word expansion for `$(K+KN)^p$` and its trace-level version are
also now in `formalization/EvgenyTheorem/TraceExpand.lean`. They preserve word
ordering and multiplicity. In `formalization/EvgenyTheorem/GlueAlg.lean`,
`trace_single_KN_word_zero` proves that a trace word with exactly one `K*N`
factor vanishes when the remaining factors are powers of a block-diagonal `K`,
using the existing `trace_pow_N_pow_zero` result.

These are reusable algebraic components, not a generalization of `glue_trace4`
to higher moments. The corner identities `GlueDiag G (K * K)`, controlled
boundary reductions, and the multi-pairing strata still need separate proofs.

## 4b. Reproducible combinatorial certificate

The generated inventory is committed at
`computational/trace_word_inventory_p6_p8_p10.json`. It records every canonical
cyclic representative for $p=6,8,10$, the number of occurrences of the
`K*N` factor in each representative, and the size of its rotation orbit.
The Python test suite now compares the committed JSON byte-independent data
structure against fresh output from `word_inventory`, so accidental drift in
the certificate is caught by CI.

This makes the **word enumeration** independently auditable and reproducible.
It does not establish equality of the matrix traces for different words, prove
that any term vanishes, or close the higher-moment theorem.

## 5. Proof obligations before claiming closure

1. Use the machine-checked ordered-word expansion to organize the $p=6,8,10$ terms with their exact ordering and multiplicities; do not collapse terms merely because they share a cyclic class.
2. Reduce the remaining multi-pairing terms under explicit hypotheses. The $r=1$ stratum now has a machine-checked vanishing lemma; $r=2$ still needs its corner-vanishing hypothesis, and $r\ge3$ is not covered by the current generic reductions.
3. Derive the remaining boundary expression in terms of marked corner entries of $K^j$, with $j\le p-1$, and state every required corner-separation/vanishing hypothesis.
4. Prove that the relevant marked corner blocks are equivalent for the two orientations. Graph-neighborhood isomorphism alone is insufficient unless it preserves the operator labels or an explicit basis transformation is supplied.
5. Establish the finite base transition for $R_3=R_4$ with an independently reproducible exact certificate or a direct formal proof.
6. Prove the level-to-level recurrence (or another valid induction step) that propagates the residual identity to every claimed level.
7. Compile the Lean project from a clean checkout and record the exact toolchain and successful build output before describing any result as machine-checked.

## 6. Intended Lean decomposition

A maintainable route is to separate the proof into:
- a generic algebraic expansion/collection lemma for arbitrary $p$;
- a gluing-boundary formula expressed through corner matrix entries;
- geometric lemmas proving the required corner-block relations for the concrete graph operators;
- the finite base case and the induction/recurrence theorem.

The existing fourth-moment result should remain unchanged while these components are developed. Do not weaken hypotheses or introduce axioms, `sorry`, or an unverified all-level claim merely to make the higher-moment statement appear closed.

## 7. Status summary

- **Machine-checked components in `main`:** the existing fourth-moment development and the components already merged there. The new three-pairing lemmas described in Sections 4e–4f are on PR #4's working branch, not `main`.
- **Current PR head `06b3a67` (checked 2026-10-19):** the Lean `Build formalization` job and Python tests (3.11 and 3.12) pass in GitHub Actions after retrying a transient TLS failure while downloading Lean 4.33.1. This is CI evidence for the current branch head, not proof of the full higher-moment conjecture.
- **Combinatorially counted and reproducibly certified:** binary words and cyclic-rotation classes for $p=6,8,10$; the committed JSON inventory is checked against the generator by tests.
- **Numerically supported:** finite-level higher-moment residual patterns described above; the full independent calculation is not yet packaged here as a reproducible, reviewed certificate.
- **Not yet proved/formalized here:** the complete higher-moment boundary formulas, the required corner equivalences, and the all-level $p=6,8,10$ residual identity and its propagation.


## 4c. Cyclic gap encoding by the number of pairing factors

The combinatorial inventory now records, for each binary necklace, the canonical
cyclic tuple of numbers of K factors between consecutive K*N factors. For a word
with r occurrences of K*N, this tuple has length r and its entries sum to p-r.
The all-K word is represented by the empty tuple. This encoding is rotation-invariant
and gives a one-to-one representation of binary necklace classes at each fixed r;
the generator and tests check uniqueness and counts for $p=6,8,10$.

This is an organizational result for the expansion: it groups cyclic words by
the gaps between pairing factors, which is the natural shape needed to apply
the two-N trace formula and identify which middle powers K^b arise. It remains
combinatorics only and does not assert that words with the same gap data have
equal trace contributions beyond cyclic rotation.


## 4d. Reduction ledger: what the current generic lemmas do and do not cover

A machine-readable ledger now partitions every word and cyclic class by the
number r of factors K*N. It explicitly separates the strata that have generic
reductions from those that do not: $r=0$ is the K^p term; $r=1$ is covered by the
one-N trace-vanishing lemma under block diagonality; $r=2$ is covered by the
two-N formula only when its corner-vanishing hypothesis is supplied. The strata
$r\ge3$ are marked as not covered by the current generic reductions. This is a
statement about the current proof infrastructure, not a claim that those terms
are nonzero or irreducible.

The class counts make the remaining gap concrete:

| p | total cyclic classes | $r=2$ classes | $r\ge3$ classes |
|---:|---:|---:|---:|
| 6 | 14 | 3 | 9 |
| 8 | 36 | 4 | 30 |
| 10 | 108 | 5 | 101 |

Thus the two-N lemma is a useful component but cannot by itself close the
$p=6,8,10$ expansion. The next mathematical target is a controlled reduction
for words with at least three $K N$ factors (or a proof that specific classes
vanish under additional explicit geometric hypotheses), while preserving their
ordering and multiplicities. The ledger is checked against the inventory in CI.

## 4e. Ordered three-pairing reduction (PR #4 working branch)

The working branch `work/three-pairing-word-reduction` now adds the Lean lemma
`trace_three_N_word_zero` in `formalization/EvgenyTheorem/GlueAlg.lean`.
It extends the three-pairing reduction from natural powers of one matrix to
ordered lists of potentially different block-diagonal matrices on the outside
of the three displayed pairing factors. The lemma preserves the order of those
factors and uses cyclicity only to rotate the exterior product.

Its key assumption is explicit: the middle matrix M must be block diagonal and
must satisfy the glued-corner off-diagonal vanishing condition, so that N*M*N
is diagonal by `Q_eq_diag`. This condition is not derived from block diagonality
alone. In applications with M = K^b, the proof must separately establish the
corner condition for that specific exponent b, including the cross-copy case
where required by `GlueDiag_pair_vanish`.

The resulting trace is zero because the diagonalized N*M*N factor, together
with the remaining block-diagonal factors, leaves one N in the cyclic trace.
This extends the reusable formal reduction pattern for the $r=3$ stratum, but
does not settle the $r\ge4$ strata, establish the needed hypotheses for all powers,
or prove the $p=6,8,10$ residual recurrence.

**CI status checked 2026-10-19:** the current PR head `06b3a67` passes the Lean `Build formalization` job and both Python jobs (Python 3.11 and 3.12) after the CI workflow was updated to retry transient toolchain-download failures; the first setup attempt succeeded on this run. All three checks completed successfully for this exact head. This verifies compilation and these test suites for the current head; it does not discharge the mathematical obligations listed below. PR #4 remains open and should not be merged solely on the strength of this conditional lemma.

## 4f. Exact $r=3$ gap split for $p=6,8,10$

The committed inventory and a dedicated regression test now split the
three-pairing classes according to whether any cyclic K-gap is zero. A zero
gap means two consecutive factors of the form K*N, so the power between the
corresponding N factors is exactly K^1. The ordered three-pairing lemma can
therefore use the already stated glued-corner condition for K, with all other
K powers kept as block-diagonal exterior factors.

| p | $r=3$ classes | Classes with a zero gap | Remaining classes (canonical gap tuples) |
|---:|---:|---:|---|
| 6 | 4 | 3 | (1,1,1) |
| 8 | 7 | 5 | (1,1,3), (1,2,2) |
| 10 | 12 | 7 | (1,1,5), (1,4,2), (1,2,4), (1,3,3), (2,2,3) |

This split is checked against the generator by
`test_three_pairing_classes_split_by_unit_cyclic_gap`. It certifies the
classification and exact cyclic representatives, not the matrix-trace theorem
itself. For each remaining tuple, every gap is positive, so the middle powers
between N factors are at least K^2. The existing hypothesis on K does not imply
the needed corner-vanishing condition for these powers. The next mathematical
obligation is to prove or refute those specific higher-power conditions from
the concrete graph/operator definitions, rather than assume them.

