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
- **Latest CI run checked 2026-10-19:** the Lean `Build formalization` job and Python tests (3.11 and 3.12) pass in GitHub Actions after retrying a transient TLS failure while downloading Lean 4.33.1. This is CI evidence for the current branch head, not proof of the full higher-moment conjecture.
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

**CI status checked 2026-10-19:** the current branch head passed the Lean `Build formalization` job and both Python jobs (Python 3.11 and 3.12) after the CI workflow was updated to retry transient toolchain-download failures; the first setup attempt succeeded on this run. All three checks completed successfully for this exact head. This verifies compilation and these test suites for the current head; it does not discharge the mathematical obligations listed below. PR #4 remains open and should not be merged solely on the strength of this conditional lemma.

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

## 4g. Support-by-distance reduction and the remaining spin obstruction

The concrete locality facts isolate a partial route for the unresolved positive
cyclic-gap classes. The operator entry vanishes when geometric coordinates
differ and the corresponding vertices are not joined by an `EdgeB` edge;
diagonal degree terms preserve the coordinate. The theorem `EdgeB_step`
bounds the change in each coordinate along one edge by one. Distinct geometric
corners of a level-`m` copy differ by `2^m` in at least one coordinate.
Consequently, any edge path between such corners has length at least `2^m`.

The intended matrix-power lemma is:

```
(K^b)_{u,v} = 0
for distinct geometric corner coordinates whenever b < 2^m.
```

Its Lean proof must expand the matrix product at the induction step and show
that every summand vanishes: either the last edge is unsupported, or the
preceding power is already zero by the induction hypothesis. This is a proof
target, not yet a theorem in the repository.

If established, this coordinate-support result covers exponents `b <= 9`
at levels `m >= 4`, since `2^m >= 16`. It does **not** cover the exceptional
level `m = 3` for exponents `b = 8, 9`, where the distance lower bound is
only eight. Those entries need a finite exact calculation or a separate graph
argument.

There is a second independent limitation: the hypothesis used by the generic
trace reduction quantifies over distinct glued *states*, not just distinct
geometric coordinates. When two states have the same coordinate but different
spin, the distance argument is inapplicable. The existing `Hc_sq_zero`
establishes a specific second-power cancellation only; it does not justify
vanishing for powers three and above. Any complete application must either
prove the needed spin-resolved corner entries for each relevant exponent or
retain their contributions in the boundary formula.

**Status:** no unconditional corner-power lemma has been added on the basis of
this argument. The positive-gap `r = 3` classes listed in Section 4f remain
unresolved, as do the full higher-moment boundary identity and the all-level
residual recurrence for `p in {6, 8, 10}`. This section records narrowed
proof obligations and must not be read as a Lean proof.

## 4h. Exact interface and current proof boundary

The locality-to-power-support argument is split into a one-step theorem and an
induction that remains open.

The one-step part is now machine-checked in
`formalization/EvgenyTheorem/GlueCorner.lean`:

- `sgK_entry_local`: a nonzero entry of `sgK` either preserves the geometric
  coordinate or follows an `EdgeB` edge.
- `sgK_entry_coord_dist`: each coordinate changes by at most one across a
  nonzero one-step entry.

The second lemma combines the first with `EdgeB_dist`. These results handle
the state/copy/spin projections at the one-step level; they do **not** prove
the analogous statement for `K^b`.

The remaining power-support target is that a nonzero entry of `K^b` implies
that each coordinate changes by at most `b`. Its induction step must expand
`Matrix.mul_apply`, retain the intermediate state (including spin), and use
the one-step bound for the final factor. Only after this induction is proved
can the coordinate-distance bound be used contrapositively to establish
corner-entry vanishing for exponents below the corner separation.

The compatible metric is the maximum of the absolute coordinate differences,
not Manhattan distance: the six directions in `Step6` include diagonal
moves, while each coordinate changes by at most one per edge. Distinct
geometric corners differ by `2^m` in at least one coordinate. Thus the
intended coordinate-only consequence is vanishing for distinct corner
coordinates when `b < 2^m`, if the power-support induction is completed.

## 4i. Verified one-step support for `sgK`

The concrete matrix is `sgK m θ ax o = blockK (Hc m θ ax o)`. The current
Lean source proves the exact one-step interface:

```lean
theorem sgK_entry_local (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] (w w' : WSG m)
    (h : sgK m θ ax o w w' ≠ 0) :
    w.2.1.1 = w'.2.1.1 ∨
      EdgeB m w.2.1.1.1 w.2.1.1.2 w'.2.1.1.1 w'.2.1.1.2 = true
```

It also proves the quantitative bound:

```lean
theorem sgK_entry_coord_dist (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] (w w' : WSG m)
    (h : sgK m θ ax o w w' ≠ 0) :
    w.2.1.1.1 ≤ w'.2.1.1.1 + 1 ∧ w'.2.1.1.1 ≤ w.2.1.1.1 + 1 ∧
    w.2.1.1.2 ≤ w'.2.1.1.2 + 1 ∧ w'.2.1.1.2 ≤ w.2.1.1.2 + 1
```

Both lemmas are present in the current branch, and the current branch head's
Lean formalization and test workflows passed. This upgrades the one-step
locality interface from a proposed sketch to a compiled result.

The next Lean theorem must lift this bound from entries of `K` to entries of
`K^b`. It must not discard spin indices in the intermediate-state sum. Even
if that coordinate-only power theorem is proved, same-coordinate/different-spin
corner entries remain a separate obligation: `Hc_sq_zero` covers the
second-power cancellation only and cannot be generalized to higher powers
without proof.

The coordinate argument would cover distinct-coordinate corner entries for
`b ≤ 9` at levels `m ≥ 4`, since `2^m ≥ 16`. It does not settle the
exceptional level `m = 3` for powers `8` and `9`, nor does it settle
same-coordinate/different-spin entries. Those entries must be computed or
proved separately, and any nonzero contributions must be retained in the
boundary formula.

**Status:** one-step support and coordinate displacement are proved and
compiled; arbitrary-power support, the exceptional level-3 entries, the
spin-resolved higher-power corner conditions, the full higher-moment boundary
identity, and the all-level residual recurrence for `p ∈ {6, 8, 10}` remain
open. The higher-moment target remains conjectural.

## 4j. Machine-checked arbitrary-power coordinate support

The induction gap described in Sections 4g–4i has now been closed at the
coordinate-support level in `GlueCorner.lean`. The generic theorem
`pow_entry_coord_dist` proves that if every nonzero one-step matrix entry
changes each coordinate by at most one, then every nonzero entry of `K^n`
changes each coordinate by at most `n`. Its induction step expands
`Matrix.mul_apply` and extracts an intermediate state with a nonzero product;
the intermediate state is not replaced by a coordinate-only or spin-free
surrogate.

The concrete specialization `sgK_pow_entry_coord_dist` applies that theorem
to the glued Sierpinski operator. The contraposition is formalized by
`pow_entry_zero_of_coord_gap`, with the concrete specialization
`sgK_pow_entry_zero_of_coord_gap`: if any coordinate gap exceeds the power
length, the corresponding matrix-power entry is zero.

**CI status checked 2026-10-20:** after correcting the concrete corollary's
state type to let Lean infer it from `sgK`, both the `Lean formalization`
workflow and the `Tests` workflow passed on commit
`9407a8ae47c7f2da1c7f0cffd09badefecb4702b`. This is the exact commit checked;
later commits require their own CI confirmation.

This result closes only the coordinate-distance induction. It does not by
itself prove the corner condition used by `trace_three_N_word_zero`: that
condition distinguishes glued states and can include states sharing geometric
coordinates but differing in spin/copy labels. The exceptional level-`3`
powers `8` and `9`, same-coordinate/different-spin entries, and the full
boundary identity remain open. Therefore the residual recurrence for
`p ∈ {6, 8, 10}` remains conjectural, not a proved theorem.

## 4k. Status reconciliation after Section 4j

Sections 4g and 4h were written before the generic induction was committed.
Their statements that the coordinate-only power-support induction is still open
are historical descriptions of the earlier state and are superseded by Section
4j. The current state is:

1. **Proved and compiled:** arbitrary-power coordinate displacement for any
   matrix satisfying the one-step coordinate bound.
2. **Proved and compiled:** the corresponding zero-entry consequence when a
   coordinate gap exceeds the power length, including the `sgK` specialization.
3. **Still open:** vanishing for distinct glued corner states whose geometric
   coordinates are equal but whose spin/copy labels differ; the exceptional
   level-`3` exponents `8` and `9`; the full boundary identity; and the
   all-level residual recurrence for `p ∈ {6, 8, 10}`.

**Documentation CI status checked 2026-10-20:** the research-log update in
commit `60b6c75e441731a1edbbfb1c3f11072b6e108b40` passed both `Lean
formalization` and `Tests`. This verifies the repository checks for that
documentation commit; it does not upgrade the remaining conjecture to a theorem.


## 4l. Local block identities checked against the concrete operator

A further source audit of `GlueCornerTri.lean`, `GlueCornerData.lean`, and `PairUnit.lean` identifies the exact local identities available for future path reductions:

- `Bk_diag`: the point-level diagonal block is the vertex degree times the 2×2 identity matrix.
- `Bk_swap`: for an antisymmetric orientation, reversing an edge gives the conjugate transpose of its block.
- `Bk_mul`: the two directed blocks of one edge multiply to the identity.
- `tri_add_conj`: for a triangle with exactly one flux edge, the oriented loop product plus its adjoint is a scalar multiple of the identity, with coefficient `-2 * cC θ` in the project's notation.
- `sgK_diag` and `sgK_sq_diag`: the diagonal entries of the first and second powers are respectively `d` and `d² + d`, independent of the axis function under the stated orientation hypotheses.

These identities are local: they control a single edge, a backtracking pair, a specified triangle, or diagonal entries. They do not give a general rule for products along length-8 or length-9 paths. In particular, replacing adjacent reverse-edge blocks by the identity inside a longer ordered product is valid only when the factors are adjacent in that product; it cannot be used to commute unrelated SU(2) blocks.

The next calculation should enumerate the actual supported walks for the unresolved level-3 corner entries and multiply their 2×2 blocks in path order, grouping a path with its reversed path only after taking the relevant adjoint/trace relation into account. Any cancellation must be derived from these concrete products or formalized as a separate lemma. No new all-level higher-moment claim follows from the local identities alone.

**Status:** this audit narrows the available reduction rules but does not close the exceptional level-3 entries or the higher-moment conjecture.


## 4m. Numerical pipeline audit: trace values are not corner certificates

The current Python implementation provides a concrete finite-level SU(2) operator in `src/operators/operators.py`, built from the graph in `src/graph/sg_graph.py`. The higher-moment tests evaluate full traces of powers for levels 1–4 at `θ = π/2`; these tests are useful regression checks for the implemented convention, but they do not expose the individual glued-corner entries `(K^8)_{w,w'}` and `(K^9)_{w,w'}` required by the conditional Lean reduction.

This distinction matters because a trace-difference match cannot certify that every boundary term vanishes: nonzero corner contributions could cancel in a total trace or be absorbed into a residual value. The next numerical artifact should therefore be a targeted corner-entry report at level 3, with the exact endpoint state labels and complex values for powers 1 through 9, computed from the same operator builder and the same `commuting`/axis convention as the existing tests. It should separately report (i) different geometric corner coordinates and (ii) same-coordinate states with different spin/copy labels. Such a report can identify a finite candidate identity, but the resulting equality still needs an exact symbolic or Lean proof before it can discharge the formal hypothesis.

**Audit result:** the existing numerical higher-moment tests are not a substitute for the exceptional-corner calculation. No conclusion about the level-3 entries of powers 8 or 9 is asserted here.


## 4n. First concrete level-3 numerical probe (diagnostic only)

A direct matrix-power probe was run from the repository's current Python builders (`src/graph/sg_graph.py` and `src/operators/operators.py`) at level 3, `theta = pi/2`, with `commuting=False`. The builder gives 42 graph vertices and an 84-dimensional spin operator. For the three geometric outer vertices `(0,0)`, `(1,0)`, and `(0,1)` in the Python graph's normalized coordinates, all computed off-diagonal 2×2 corner blocks of `H^n` were zero to numerical precision for `1 <= n <= 7`, but **not** for `n = 8` or `n = 9`. At `n = 8`, the largest absolute block entry was 1.0; at `n = 9`, it was approximately 23.6842.

This is an important warning against assuming the exceptional level-3 corner entries vanish automatically. It is not yet a counterexample to the Lean theorem: the Python builder uses its own graph construction, face traversal, edge-flux assignment, and state indexing, and those conventions have not been proven identical to the Lean `sgK`/`sgGlue` construction. In addition, this probe measures the Python operator's vertex-corner blocks, not the full Lean glued-state corner hypotheses. It is therefore diagnostic evidence only, not a formal disproof or a replacement for an exact calculation.

**Action implied:** before attempting to prove the level-3 corner hypothesis, align the Python and Lean graph/flux conventions and compare the level-1 and level-2 entries on shared labeled states. If the conventions agree, the nonzero level-3 blocks must be accounted for explicitly in any higher-moment formula rather than discarded by a distance argument.


## 4o. Cross-implementation convention comparison

The source comparison now confirms one important match: Lean's `facesExact` recursively appends the three translated face lists in the same order as the Python `sg_tree_graph_with_faces` construction, and Lean's `faceAxis(i) = i mod 3` matches Python's noncommuting axis assignment by face index. Both assign the flux to the first edge of each ordered face (the face's first and second vertices).

A remaining convention check is still required before treating the level-3 numerical probe as evidence about `HC`: Python canonicalizes undirected edges by vertex indices (`tuple(sorted((a,b)))`), while Lean canonicalizes by lexicographic point order (`if pu ≤ pv then (pu,pv) else (pv,pu)`) and defines the flux edge by point order. The Python vertex insertion order is generated by recursive copy traversal, not explicitly sorted by coordinates. Thus the two implementations may orient a shared geometric edge differently; because reversing an SU(2) edge replaces its unitary by its adjoint, this cannot be ignored without a labeled edge-by-edge comparison or a gauge-equivalence argument.

The newly added `computational/corner_power_report.py` commit `8988422838517259f7f44d26cb8ad56de8ff798c` has now passed both CI workflows: [Lean formalization](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39375729447) and [Tests](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39375729465). These checks validate the repository build/tests, not mathematical equivalence of the Python and Lean operators.

**Next comparison:** emit the ordered vertex coordinates and flux-edge orientation from both implementations at level 1, normalize each edge to a common geometric ordering, and compare its assigned axis and directed unitary. Only after this table agrees (or a precise gauge transform is proved) should level-3 corner values be used to adjust or prove the Lean boundary formula.


## 4p. Follow-up on vertex ordering: one suspected mismatch is resolved

Inspection of `Orientation.lean` resolves part of the convention concern raised in §4o. Lean's `vertexOrder` is explicitly defined as the deduplicated concatenation of the three recursive copies in `A ++ B ++ C` order, and `vIdx` is the index in that list. This mirrors the Python builder's `one_step`, which traverses offsets `(0,0)`, `(1/2,0)`, `(0,1/2)` and retains the first occurrence of each coordinate. `connectionOperatorWithAxis` deliberately uses `vIdx` to choose `U` versus `Uᴴ`, so the edge direction is intended to follow Python's vertex-index order, not lexicographic coordinate order.

This means the earlier concern should be narrowed, not repeated as an established mismatch: recursive vertex order and the direction-selection rule are designed to agree. The remaining verification is concrete and finite: compare, after scaling Python coordinates by `2^m`, the ordered vertex list, edge set, ordered face triples, and per-edge axis at levels 0, 1, and 2. In particular, confirm that the face's first-second edge in `facesExact` maps to the same sorted-index edge assigned the rotation in Python. A proof of this correspondence is not yet present in Lean, so the level-3 numerical report remains diagnostic until the comparison is completed.

**Correction to §4o:** vertex-index orientation is not an unexplained implementation discrepancy; `Orientation.lean` explicitly exists to reproduce Python's creation order. The open issue is a proved edge/face/axis correspondence, not evidence that the operators already differ.


## 4q. Orientation discrepancy is real at the coordinate level, but handled in the operator

A closer read of `Operator.lean` and `docs/LEAN_ROADMAP.md` sharpens §4p. The raw coordinate order `pu ≤ pv` and Python's vertex-index order are different for some edges when `m ≥ 2`; this is not merely a hypothetical concern. The repository already handles it correctly in `connectionOperatorWithAxis`: the canonical edge key is stored as a geometric ordered pair for flux lookup, but the choice between `-U` and `-Uᴴ` is made by `vIdx m pu ≤ vIdx m pv`. `Orientation.lean` defines `vertexOrder` as the recursive `A ++ B ++ C` first-occurrence order matching Python's `one_step` traversal. The roadmap explicitly records that coordinate orientation fails to reproduce the p=4 closed form at levels 2 and 3, while index orientation reproduces it at levels 1, 2, and 3.

Thus the correct conclusion is: **the operator's direction convention has already been deliberately corrected; the remaining cross-implementation audit is to verify the recursive vertex list, edge adjacency, face ordering, and flux-edge-to-face-index map—not to change the orientation rule again.** The p=4 closed form and its CI evidence should not be disturbed while investigating higher moments.

A useful independent check for the next pass is a small deterministic comparison of Python's scaled vertex list against Lean's `vertexOrder` at levels 0–2, then comparison of each face's first-second edge against the corresponding Python `faces[i]` edge and axis `i mod 3`. Until that table is produced, higher-moment corner entries remain diagnostic only. No claim is made here that the level-3 powers 8 or 9 vanish.


## 4r. Verification status and the next finite comparison

The CI status has been rechecked against GitHub Actions: both `Lean formalization` and `Tests` completed successfully for commit `9b4345872cb7b3bd5d6382b6a4bce287e6ae8191` (runs 39377867112 and 39377867121). The same two workflows also passed for `6c345e4` and `eaef375`. These are repository-level checks; they do not establish the conjectural higher-moment identity.

The next finite comparison is specified as a data table rather than another prose-only audit. For each level `m = 0, 1, 2`, it should list: (a) the ordered vertex coordinates in Python and Lean, after scaling by `2^m`; (b) the canonical undirected edge set; (c) each ordered face triple; (d) the face index and axis assigned to its first-second edge; and (e) any duplicate edge assignment with conflicting axes. The comparison must use the actual Python functions and Lean definitions, not a separately reconstructed graph. A mismatch should fail loudly and identify the first differing item.

Until that executable comparison exists and passes, the level-3 corner report remains diagnostic. Even a successful convention comparison would not prove the higher-moment theorem: the exceptional powers still need either an exact corner-entry identity or an explicit boundary correction. The established p=4 theorem is to remain unchanged.


## 4s. Convention regression test repaired and CI-confirmed

The first run of `tests/test_lean_python_graph_conventions.py` failed because the test treated the Python level-0 face list as explicit, although the builder intentionally returns `faces=None` at that base level. The test now checks vertex order at levels 0–2 and checks ordered faces/flux-edge assignments only at levels 1–2, where the Python builder materializes faces. This is a test-domain correction; it does not alter the operator or any Lean theorem.

The corrected commit `100524e334d3cc3787105c9c4ddc5417078eeeb1` has passed both workflows: [Tests run 39380417984](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39380417984) and [Lean formalization run 39380418011](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39380418011).

Scope note: this test compares Python output against a Python encoding of the Lean recursive definitions; it is a regression check for the documented conventions, not a machine-checked cross-language theorem. It also does not yet prove the edge-to-axis map agrees with every `connectionOperatorWithAxis` entry, and it says nothing by itself about the conjectural `p = 6, 8, 10` residual identity. The next formal step remains either an explicit Lean correspondence lemma or an exact boundary correction for the exceptional powers.


## 4t. Structural reduction for moments beyond four

The current formal trace infrastructure already contains the reusable identity `trace_blockK_pow`: the trace of any natural power of the copy-block-diagonal operator is the sum of the traces of the corresponding copy powers. The missing step for `p = 6, 8, 10` is therefore not the trace of the three diagonal copy blocks itself. It is a full expansion of the glued operator power into cyclic copy-label words, with every transition through the glued boundary retained in its original matrix order.

For `p = 4`, `pOpO_trace4_glue_final` packages that expansion as `glueRHS`, and `cornerTerm` collects the resulting boundary contributions using diagonal entries of `K`, `K^2`, and `K^3`. This is a special low-degree identity; it cannot be reused unchanged for higher p. At degree p, the expansion can contain longer alternating excursions across the glued partner map, and its boundary weights involve ordered products/sums of powers up to degree p−1. Any proposed higher-moment proof must first establish an exact degree-p analogue of `trace4_split`, rather than infer it from `trace_blockK_pow` or from the p=4 formula.

**Concrete next lemma target:** formulate a generic finite-matrix theorem for a block-diagonal operator plus a boundary-supported coupling, expressing `trace((D+E)^p)` as the sum over cyclic words in `D` and `E`; then specialize the word expansion to the involutive glued partner map. This separates generic algebra (which can be proved without Sierpinski geometry) from the geometric claim that particular boundary words vanish or combine into a level-independent correction. No theorem for p=6, 8, or 10 is claimed by this entry.


## 4u. Audit of the existing arbitrary-power lemma

The latest audit confirms `trace_blockK_pow` is already fully general in the exponent `n`; it proves the trace identity for the copy-block-diagonal `blockK` operator at every natural power. The limitation is structural: `pOpO (m+1)` is not just `blockK Hc`; the exact fourth-power theorem first rewrites it through `pOpO_trace4_glue_final`, whose boundary expansion is specifically degree four. Thus strengthening `trace_blockK_pow` would not address the missing higher-moment argument.

The next proof should split into two independent lemmas, avoiding a premature geometry claim:

1. **Algebraic word expansion:** for finite matrices `D,E`, expand `(D+E)^p` into the `2^p` ordered words over `{D,E}` and apply trace linearity. The ordering of factors must be preserved; this is not a commutative binomial theorem.
2. **Glue-word classification:** specialize `D = blockK (Hc ...)` and `E = pOpO - D`, then show which cyclic words involving `E` vanish by support or combine into explicit boundary terms. Only this second lemma depends on `sgGlue`, `σ`, and the Sierpinski corner geometry.

For `p=6,8,10`, the raw expansion has respectively 64, 256, and 1024 words before cyclic and support reductions. A direct expansion in Lean is likely unwieldy; the maintainable target is a recursive word-indexed sum, with small-degree lemmas used to validate the recursion against `trace4_split`. The existing p=4 theorem should serve as a regression check, not be rewritten during this step.

CI was rechecked after the previous log update: commit `f69656cbf57a456e3d6113120e22012e31b39cdd` passed both workflows ([Lean formalization](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39382082225), [Tests](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39382082222)). This confirms the repository remains green, not the conjecture for higher moments.

## 4v. Exact scope of the corner-support result

A source-level audit of `GlueCorner.lean` identifies the strongest unconditional geometric statement currently available for powers of `sgK`:

- `sgK_entry_coord_dist` proves that a nonzero one-step entry changes each lattice coordinate by at most one.
- `pow_entry_coord_dist` lifts this to the (n)-th power by induction over the intermediate state in the matrix-product sum.
- `sgK_pow_zero_of_distinct_glued_corner_coords` therefore proves vanishing between *distinct geometric corner coordinates* whenever (n < 2^m).

This settles that particular support case for (n\le 9) at levels (m\ge4), but only for distinct coordinates. It does **not** settle the same-coordinate/different-spin case, and it does not cover powers (n=8,9) at level (m=3). Those are genuine remaining cases for any argument that needs all glued-corner entries of (K^n) to vanish.

The distinction matters: a coordinate-distance bound cannot imply spin-diagonal cancellation for paths that return to the same vertex. The existing second-power result `sgK_hu2` is a separate edge-unitarity argument and must not be generalized to arbitrary powers without a new proof. In particular, neither `BD_pow` nor the support induction supplies that missing fact.

### Current verified boundary

The current PR head `4b27df57053162883bb2150387e7ed2e70b23888` passed both GitHub Actions workflows on 2026-10-20: [Lean formalization](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39409782910) and [Tests](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39409783057). PR #4 remains an open conditional algebraic result. These CI results do not prove the same-coordinate spin cancellation or the conjectured level-independent residual for (p=6,8,10).

### Next concrete proof obligation

Do not strengthen `sgK_hu2` by analogy. First isolate the same-coordinate spin-off-diagonal entry
`(sgK m θ ax o ^ n) w w'` for glued states with equal geometric coordinate and unequal spin. Expand its intermediate-state sum into closed walks and determine whether cancellation follows from reverse-edge unitarity alone or whether triangular holonomy terms survive. If terms survive, preserve them in the boundary correction. The level-3 powers 8 and 9 should be treated separately rather than hidden by the (m\ge4) distance estimate.

## 4w. Same-corner spin-mixing diagnostic: scope and reproducibility

The script `computational/corner_power_report.py` now reports the spin-off-diagonal entry of each outer-corner (2\times2) block of (H^n), in addition to blocks between distinct corners. This makes the previously missing same-coordinate/different-spin case observable.

**Evidence boundary:** this commit adds the measurement field; it does not add a checked-in result artifact or a reproducible test asserting universal cancellation. Therefore no universal numerical conclusion is recorded here. A finite floating-point scan, even if its entries are near zero, would not prove the exact identity required by Lean. The earlier geometric support lemmas also do not imply same-coordinate spin cancellation.

### Reproducible next check

Run the diagnostic from the repository root for each selected level, angle, and axis mode, preserving the JSON output as an artifact. Inspect the maximum `spin_offdiag_abs` over all three outer corners and powers (1\le n\le9). Any nonzero value beyond a justified numerical tolerance is a counterexample to the proposed blanket cancellation for that configuration; near-zero output is only evidence and must be followed by an exact proof.

The Lean proof target remains an identity for the intermediate-state sum of `(sgK m θ ax o ^ n) w w'` when the geometric coordinates agree and the spin states differ. Its assumptions must state any required orientation and axis conditions explicitly. Until that theorem is proved, the conditional trace reduction remains the supported result, and the level-independent residual conjecture for (p\in\{6,8,10\}) remains unproved.

## 4x. Exact middle-power map for the remaining three-pairing classes

The cyclic-gap tuple counts the K factors *between* consecutive K*N factors. Since each K*N factor itself contributes one leading K, a gap entry a corresponds to a power exponent a + 1 in the word written cyclically as K^a N K^b N K^c N after combining adjacent K factors. The exact unresolved classes and orbit multiplicities from the committed inventory are:

| Moment p | Canonical gap tuple | Actual middle-power exponents | Orbit size |
|---:|---|---|---:|
| 6 | (1,1,1) | (2,2,2) | 2 |
| 8 | (1,1,3) | (2,2,4) | 8 |
| 8 | (1,2,2) | (2,3,3) | 8 |
| 10 | (1,1,5) | (2,2,6) | 10 |
| 10 | (1,4,2) | (2,5,3) | 10 |
| 10 | (1,2,4) | (2,3,5) | 10 |
| 10 | (1,3,3) | (2,4,4) | 10 |
| 10 | (2,2,3) | (3,3,4) | 10 |

The orbit sizes sum to 2, 16, and 50 factor words respectively across the listed target classes; these multiplicities must be retained when collecting cyclic trace contributions. A regression test now checks this gap-to-exponent map and the orbit sizes against the generated inventory.

This calculation narrows the geometric obligation. Every required exponent is at most 6. For distinct geometric corner coordinates, sgK_pow_zero_of_distinct_glued_corner_coords therefore applies at every level m >= 3, since 6 < 2^m. The remaining same-copy corner condition is the same-coordinate/different-spin entry: exponent 2 is covered by sgK_hu2, while exponents 3, 4, 5, and 6 still require a proof. The generic Hermitian/quaternion-form helper in SU2.lean is only an algebraic endpoint; until the quaternionic block form is shown to be preserved by the concrete Hc powers, it does not discharge these hypotheses.

**Status:** exact combinatorial mapping and multiplicities are recorded and regression-tested; the concrete same-coordinate spin cancellation for powers 3–6 and the full residual theorem remain open.


## 4y. Concrete same-point spin cancellation after quaternion-form closure

**Update for PR #8 head `ebfdf002a236d733de6343a7c0ac25099b7a5f9f` (2026-10-21):** the earlier Section 4x statement that same-coordinate spin cancellation for powers 3–6 remained unproved is superseded by the new Lean lemmas in this branch.

The formal chain is:
- `SU2QuaternionForm` and its multiplication/power closure in `SU2.lean`;
- `pHeO_spinBlock_quaternionForm` and `Hc_spinBlock_quaternionForm` for the concrete local blocks;
- `pOpO_hermitian_of_OAnti` and `Hc_hermitian_of_OAnti` under the explicit orientation-antisymmetry hypothesis;
- `Hc_pow_samePoint_spinOffdiag_zero` and `Hc_pow_samePoint_spinOffdiag_zero_any`;
- `sgK_pow_GlueDiag_of_OAnti`, transferring the all-natural-powers cancellation to the glued corner condition.

The PR head has successful GitHub Actions evidence: Lean formalization run 178 and Python tests run 247, including both Python 3.11 and 3.12. Links: https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39559293076 and https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39559293274.

**Scope boundary:** this closes the concrete same-point spin-off-diagonal corner obligation under the stated hypotheses for the exponents used by the eight listed three-pairing classes. It does not itself derive the full higher-moment boundary formula, collect all ordered trace-word contributions into the final residual identity, or prove the level-propagation step. The all-level residual identities for p = 6, 8, 10 therefore remain conjectural until those separate obligations are machine-checked.


## 4z. Conditional four-pairing boundary reduction (PR #8)

**Lean source:** `formalization/EvgenyTheorem/GlueAlg.lean`, theorem
`trace_four_N_powers`.

For a word with four pairing factors, cyclicity of trace moves the final
power to the front and groups the outside factors without commuting any
individual matrices. The theorem then applies the generic two-pairing formula
to the last remaining pair. In the current interface, the middle power
`K^d` must satisfy the explicit glued-corner off-diagonal vanishing
condition. The theorem does not infer that condition from block diagonality.

The resulting identity retains the inner product `G.N * K^b * G.N` inside
the diagonal entry of the outside product. This is a valid conditional
boundary reduction, but it is not yet a fully expanded sum over independent
corner entries: to simplify the inner pair further, the separate corner
condition for `K^b` must also be supplied and used. Nor does this lemma
collect all ordered words or prove their multiplicities cancel in the final
moment defect.

**Verification:** on PR #8 head
`bd968fc314516794187b441f336dee0084ab8305`, GitHub Actions Lean
formalization run 188 and Tests run 257 both completed successfully:
https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39565263648
and https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39565263685.
This is compilation/test evidence for that exact commit, not a proof of the
full higher-moment conjecture.

**Remaining:** establish the required corner hypotheses for each middle
power arising in the ordered expansions; derive a fully explicit boundary
formula for the relevant multi-pairing strata; prove the finite base
transition and the level-propagation step for `p = 6, 8, 10`. The residual
identity remains conjectural until those obligations are discharged.


### Verification addendum for the report commit

The report update itself is on PR head
`1b08908090cbaacc27e5131f125ce06ec52f7a41`. Both required workflows
completed successfully on that exact head:
- Lean formalization, run 189: https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39566107825
- Tests, run 258 (Python 3.11 and 3.12, including slow convergence tests):
  https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39566107585

Thus the source and research-log update are verified together. The mathematical
scope boundary in Section 4z remains unchanged: the full residual identity
and level propagation have not yet been proved.


### Latest verification — explicit four-pairing expansion

The explicit nested-sum theorem `trace_four_N_powers_explicit` was added to
`formalization/EvgenyTheorem/GlueAlg.lean` at PR head
`3a09e814bc7c8b73ee2debed3d3fe45d1b75ce1c`. Both required workflows completed
successfully on that exact commit:
- Lean formalization, run 191: https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39568637413
- Tests, run 260 (Python 3.11 and 3.12, including slow convergence tests):
  https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39568637588

The new lemma expands the inner `N * K^b * N` term into a nested finite sum.
Its hypotheses separately state the corner-vanishing requirements for
`K^b` and `K^d`. This is a verified local reduction only; it does not
establish the multiplicity cancellation or all-level residual identity for
`p = 6, 8, 10`.
