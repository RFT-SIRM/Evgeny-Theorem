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

This split is checked against the exact ordered-word generator by
`test_three_pairing_classes_split_by_unit_gap_and_positive_gap_cases` and
`test_three_pairing_gap_tuple_maps_to_middle_power_and_orbit_multiplicity`.
The latter ties each canonical gap tuple to an actual canonical ordered word,
its three `K*N` factors, the middle exponents (gap + 1), and the exact orbit
weight.

**Updated resolution under an explicit hypothesis.** The concrete operator
argument is now formalized in `GlueCorner.lean`: orientation antisymmetry
makes each copy operator Hermitian; quaternionic spin-block closure then gives
same-point, opposite-spin vanishing for every natural power; and
`sgK_pow_GlueDiag_of_OAnti` transfers this to the glued operator. Therefore
the middle-power corner condition is proved for every exponent under
`OAnti (m + 1) o`, rather than inferred from block diagonality. For each
remaining tuple, rotate the cyclic word so that its smallest gap is the middle
power. Since the three nonnegative gaps sum to p - 3, this exponent is at most
`floor((p - 3)/3) + 1 <= 3 < 2^m` for p in {6,8,10} and m >= 3. The existing
conditional Lean reduction `trace_three_N_word_zero_of_OAnti` then applies.
The five tuples listed above are thus conditionally covered; their exact
representatives and orbit multiplicities remain regression-tested.

This resolves the r=3 gap-class obligation **under the stated orientation
antisymmetry hypothesis**. It does not resolve the separate even-stratum
boundary sums for r=6,8,10, the finite base transition, or level propagation.
No unconditional all-level p-moment identity is claimed.

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


### Verification after Lean linter and elaboration-budget fix

On PR #8 head `2bbdac62ef45458113d63637570a5253141c3172` (2026-10-21),
the Lean formalization workflow completed successfully (run 197) and the
Tests workflow completed successfully (run 266, Python 3.11 and 3.12):
- https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39573201940
- https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/39573201947

This head removes the unused bound hypothesis from
`sgK_pow_GlueDiag_of_OAnti` and fixes the placement of the local
`maxHeartbeats` option for the explicit four-pairing specialization.
These results verify compilation and regression tests for this source state.
They do not prove the final residual identities or level propagation for
moments 6, 8, and 10; those obligations remain open.


## 4aa. Three-pairing class coverage from the concrete Lean theorem

The current `GlueCorner.lean` contains `trace_three_N_powers_of_OAnti`. Under `OAnti (m + 1) o`, it proves
that an ordered three-`N` trace word vanishes whenever its middle power
exponent `b` satisfies `b < 2^m`. The proof obtains the required
corner hypothesis from the same-coordinate spin cancellation and the
distinct-geometric-corner support bound.

For the eight target gap classes recorded in the combinatorial regression
test, the middle-power exponents are respectively:
- p = 6: 2;
- p = 8: 2 and 3;
- p = 10: 2, 5, 3, 4, and 3.

Thus each target middle exponent is at most 5 and is strictly below
`2^m` for every `m >= 3`. Subject to the theorem's explicit orientation-
antisymmetry hypothesis, the generic Lean theorem therefore covers the
three-pairing trace words represented by these classes. This is a conditional
formal result, not a proof that orientation antisymmetry holds for every
input, and not a proof of the full moment identity.

The inventory regression test independently checks the gap-to-exponent
mapping and orbit multiplicities (2, 16, and 50 represented words for the
listed classes at p = 6, 8, and 10). It remains necessary to connect this
class-level coverage to the complete ordered expansion and its coefficients,
then discharge the remaining higher-pairing strata and prove the level-
propagation argument. The all-level residual identities for p = 6, 8, 10
remain open.


## 4ab. Reduction-ledger classification of the full three-pairing stratum

The computational reduction ledger now marks the entire `kn_factor_count = 3`
stratum for p = 6, 8, 10 as `vanishes_by_three_N_corner_lemma_under_OAnti`.
This is justified conditionally by cyclic rotation: if the three cyclic K-gaps
are nonnegative and sum to p - 3 <= 7, their minimum is at most 2. Rotate the
word so that this gap is the middle gap between adjacent N factors. Since each
`K*N` contributes one leading K, the middle power is `min(gap) + 1 <= 3`,
which is less than `2^m` for every m >= 3. The Lean theorem
`trace_three_N_word_zero_of_OAnti` then applies under `OAnti (m + 1) o`.

A regression test checks this bound for every cyclic class with exactly three
`K*N` factors, not just the eight previously highlighted gap tuples. The ledger
still leaves all strata with four or more `K*N` factors explicitly uncovered
by the current generic reductions. This classification is conditional on the
orientation-antisymmetry hypothesis and does not prove the full moment identity
or the level-propagation step.


## 4ac. Four-pairing stratum classified by explicit boundary expansion

The reduction ledger now marks the full `kn_factor_count = 4` stratum as
`explicit_four_N_boundary_formula_under_OAnti`, rather than as an unqualified
vanishing result. Any cyclic word with four `K*N` factors has four positive
K-exponents between consecutive N factors; their sum is p. For p <= 10, each
such exponent is at most p - 3 <= 7, hence below `2^m` for m >= 3. By cyclic
rotation and splitting one cyclic gap into the two outside powers, the word
fits `trace_four_N_powers_explicit_of_OAnti` with the two required middle
exponents below the geometric bound. Under `OAnti (m + 1) o`, Lean therefore
provides the explicit nested boundary sum.

This is a boundary-formula reduction, not cancellation of the four-pairing
stratum. The regression test now distinguishes this status from the proven
conditional vanishing of the three-pairing stratum. Strata with five or more
`K*N` factors remain uncovered by these generic reductions, and the full
moment identity and level propagation remain open.


## 4ad. Conditional five-pairing trace reduction

The Lean theorem `trace_five_N_powers_zero_of_OAnti` now specializes
`trace_five_N_powers_zero` under `OAnti (m + 1) o`. It supplies the two
middle-power corner hypotheses separately using
`sgK_pow_GlueDiag_of_OAnti` and the distinct-coordinate support bound.
For the five-pairing stratum at `p ∈ {6,8,10}`, each cyclic K-gap exponent
is at most `p - 4 ≤ 6`; hence it is below `2^m` for `m ≥ 3`. After cyclic
rotation and splitting one gap into the two exterior powers, the conditional
five-N lemma applies to each ordered word in this stratum.

The reduction ledger and its regression test now record
`vanishes_by_five_N_corner_lemma_under_OAnti` for the complete `r = 5`
stratum. This status is conditional on orientation antisymmetry and on the
word-to-gap decomposition; it is not a proof of the full moment identity.
Strata with six or more `K*N` factors remain outside the current generic
reductions. The residual identities for `p = 6, 8, 10` remain conjectural
until the higher-pairing strata, complete boundary collection, and
level-propagation argument are proved.


## 4ae. Regression coverage for unresolved higher-pairing strata

The inventory test now checks every ledger stratum with six or more
`K*N` factors against the generated ordered-word representatives. For each
such stratum it verifies the exact cyclic-class count, the sum of orbit sizes
against the ordered-word count, canonical rotation of each representative,
the number of `K*N` factors, and the cyclic gap tuple and its sum.

The currently unresolved strata are:
- p = 6: r = 6 (1 ordered word, 1 cyclic class);
- p = 8: r = 6, 7, 8 (28, 8, and 1 ordered words);
- p = 10: r = 6, 7, 8, 9, 10 (210, 120, 45, 10, and 1 ordered words).

These checks close a bookkeeping/regression gap only. They do not establish
that any of these trace contributions vanish, nor do they produce the missing
boundary formula. In particular, block diagonality of K powers alone is not
the required glued-corner off-diagonal hypothesis for the middle powers in
`N * K^b * N`. A mathematical reduction for r >= 6 must state and prove the
needed corner conditions, preserve the order of factors, and account for the
complete boundary contribution before the residual moment identities can be
claimed. The new regression test passed with the Python 3.11 and 3.12 CI jobs;
the Lean build also passed on the same source state.

## 4p. Arbitrary-power glued-corner condition is now formalized

The current working branch contains
`sgK_pow_GlueDiag_of_OAnti` in `formalization/EvgenyTheorem/GlueCorner.lean`.
Under the explicit hypothesis `OAnti (m + 1) o`, it proves
`GlueDiag (sgGlue m) (sgK m θ ax o ^ n)` for every natural exponent `n`.
The same-coordinate case is discharged by Hermiticity of each concrete copy
operator and quaternionic spin-block cancellation for every power; the
distinct-coordinate case uses the glued-partner injectivity property. This is
stronger than the coordinate-distance support estimate and supplies the
spin/copy-resolved corner premise that must not be inferred from block
diagonality alone.

Consequently, for the listed three-pairing gap classes at p = 6, 8, and 10,
the conditional ordered reduction `trace_three_N_word_zero` can use its
middle-power corner premise under `OAnti (m + 1) o`; the canonical gap
enumeration and orbit multiplicities remain checked by the Python regression
tests. This resolves the *corner-hypothesis obligation* for those classes
conditionally. It does not prove the full trace identity or residual recurrence:
the complete ordered boundary contribution for strata r >= 6, the base
transition, and level propagation still require proof. The p = 6, 8, 10
all-level residual identity remains conjectural.

This section supersedes earlier status sentences in Sections 4j–4o that
describe same-coordinate/different-spin arbitrary-power corner vanishing as
open. Those sections remain useful as a record of the development and of the
separate coordinate-support and numerical-convention audits.

## 4q. Six-pairing boundary formula (conditional; cancellation not proved)

Added `trace_six_N_powers_boundary` in `formalization/EvgenyTheorem/GlueAlg.lean`.
For an ordered word with six pairing factors, it groups the word into three
`N * K^n * N` blocks and uses the explicit corner hypotheses for their three
middle powers. Under these hypotheses, each block is replaced by its diagonal
boundary matrix, and the trace is reduced to a trace of the three diagonal
boundary factors separated by the original intervening powers of `K`.
No commutation of the intervening powers is assumed.

For p = 6, 8, 10 and r = 6, the cyclic gap exponents are at most
`p - r + 1 <= 5 < 2^m` for m >= 3. Thus the conditional all-power corner
lemma `sgK_pow_GlueDiag_of_OAnti` supplies the three corner premises under
`OAnti (m + 1) o`. The reduction ledger now marks r = 6 as
`explicit_six_N_boundary_formula_under_OAnti`, preserving its ordered-word
counts and orbit multiplicities: (p=6: 1 word / 1 cyclic class), (p=8: 28 /
4), (p=10: 210 / 22). Regression tests enforce this classification and do
not assert that the resulting boundary trace cancels.

This advances the explicit boundary reduction by one pairing stratum, but
does not resolve the r = 6 contribution to the residual identity. Strata
r >= 7 still lack a generic ordered multi-pairing reduction in this branch.
The base transition and level propagation also remain unproved; the p = 6, 8,
10 all-level residual identity remains conjectural.

## 4r. Conditional seven-pairing vanishing

Added `trace_seven_N_powers_zero` in `formalization/EvgenyTheorem/GlueAlg.lean`.
The proof turns two selected `N * K^n * N` subwords into diagonal boundary
blocks and then applies `trace_three_N_word_zero` to the three remaining
pairing factors. The corner premises for the three selected middle powers are
explicit; under `OAnti (m + 1) o`, they are discharged by the all-power
`sgK_pow_GlueDiag_of_OAnti` theorem.

For p = 8 and 10, every exponent in the r = 7 stratum is at most
`p - r + 1 <= 4 < 2^m` for m >= 3. The ledger now records conditional
vanishing for r = 7, preserving counts and orbit multiplicities (p=8: 8
ordered words / 1 cyclic class; p=10: 120 / 12). Python regression tests check
these values and the conditional status. This closes the r = 7 reduction
obligation under the stated orientation hypothesis; r = 6 remains an explicit
boundary formula, while r >= 8 still need further reductions. The residual
identity and its level propagation remain conjectural.

## 4s. Conditional reductions for eight, nine, and ten pairings

Added three ordered-word reductions in `formalization/EvgenyTheorem/GlueAlg.lean`:

- `trace_eight_N_powers_boundary`: diagonalizes three selected
  `N * K^n * N` blocks and reduces the remaining two N factors to an
  explicit boundary sum.
- `trace_nine_N_powers_zero`: diagonalizes three selected blocks and applies
  `trace_three_N_word_zero` to the remaining three N factors, giving
  conditional vanishing.
- `trace_ten_N_powers_boundary`: diagonalizes four selected blocks and
  reduces the remaining two N factors to an explicit boundary sum.

Each theorem states its middle-power corner hypotheses explicitly. Under
`OAnti (m + 1) o`, `sgK_pow_GlueDiag_of_OAnti` supplies those hypotheses
for the p=8,10 strata because the relevant exponents are bounded by
`p-r+1` and are strictly less than `2^m` for m >= 3. The even-stratum
boundary formulas are not labelled as vanishing. The ledger and regression
tests preserve exact word counts and cyclic-orbit weights: r=8 has (p=8:
1 word / 1 class; p=10: 45 / 5), r=9 has (p=10: 10 / 1), and r=10 has
(p=10: 1 / 1).

This extends the ordered reductions through r=10 for the finite p=6,8,10
inventory, but does not by itself evaluate/cancel the r=8 or r=10 boundary
sums. The r=6 boundary sum also remains unevaluated. Thus the complete
residual identity, finite base transition, and level propagation are still
open; no all-level moment identity is claimed.

## 4t. First obstruction to finishing: even-stratum boundary cancellation

The finite inventory and Lean reductions now separate two logically different
tasks: (1) reducing an ordered trace word to a boundary expression, and
(2) proving that expression cancels. The current theorems establish the first
task for r=6,8,10, not the second. Added a regression test that prevents the
ledger from relabelling any of these even strata as zero without a new proof.

The smallest diagnostic case is p=6, r=6: its stratum has one ordered word
and one cyclic class, with orbit weight one. Thus there is no cancellation
between distinct cyclic classes inside this stratum. If the r=6 contribution
is required to vanish separately, its single boundary trace must itself be
shown zero from additional structure of the concrete operator. Alternatively,
a proof of the full residual identity may establish cancellation against other
r-strata, but that cross-stratum identity must be stated and proved explicitly.
The present corner-diagonalization lemmas alone do not decide between these
possibilities.

Next mathematical target: specialize `trace_six_N_powers_boundary` to the
p=6 all-pairing word and simplify its three diagonal boundary factors using
the concrete `sgK`/`Hc` definitions and `OAnti`. Do not assume the
boundary trace vanishes; either prove the needed identity or preserve it as a
nonzero/unresolved contribution. The p=8 and p=10 boundary sums then require
the same analysis with their full orbit weights.

## 4u. p=6 all-pairing boundary: diagonal-support reduction target

A direct algebraic inspection of the p=6, r=6 specialization of
`trace_six_N_powers_boundary` identifies the residual expression as
`trace (K * D * K * D * K * D)`, where
`D = diagonal (fun w => if G.g w then K (G.σ w) (G.σ w) else 0)`.
This is not, by itself, a zero formula.

For the concrete glued operator, the next reduction to formalize is that K
has no off-diagonal entries between distinct points in the support of G.g:
different copies are separated by block diagonality, and distinct glued
corners in the same copy are handled by `sgK_hkg`. If this premise is
established with the exact hypotheses and the cyclic product is expanded,
the boundary trace reduces to
`∑ w, if G.g w then (K w w)^3 * (K (G.σ w) (G.σ w))^3 else 0`.
Using `sgK_diag`, this is a sum of products of corner degrees, rather than
an automatic cancellation. The involution and corner-degree facts must still
be applied to determine its exact value and prove nonvanishing in Lean.

This is a proof target and an algebraic diagnostic, not yet a committed Lean
lemma or a CI-verified conclusion. In particular, it does not establish the
full p=6 residual identity: any required cancellation with other strata would
need a separate identity preserving the ordered-word multiplicities.
## 4v. p=6 boundary: diagonal support is available from existing corner lemmas

The diagonal-support premise identified in Section 4u follows from existing
formalized facts for the concrete operator when `1 ≤ m`: `sgK_hkg` makes
`sgK w w' = 0` for distinct glued states in the same copy, and `blockK_BD`
makes the entry zero when the copy indices differ. Thus the restriction of
`K = sgK m θ ax o` to the support of `(sgGlue m).g` is diagonal; this is a
consequence of the existing lemmas, not an additional geometric conjecture.

Algebraically, with
`D = diagonal (fun w => if (sgGlue m).g w then
  K ((sgGlue m).σ w) ((sgGlue m).σ w) else 0)`,
expanding the trace and using that support-diagonality forces the three
indices to coincide gives
`trace (K * D * K * D * K * D) =
 ∑ w, if (sgGlue m).g w then
   (K w w)^3 * (K ((sgGlue m).σ w) ((sgGlue m).σ w))^3 else 0`.
By `sgK_diag`, each diagonal K entry is the degree of its underlying local
point. This identifies the p=6, r=6 term as a degree-weighted boundary sum,
not a term that vanishes by the corner hypotheses alone.

The equality above has been derived from the definitions and existing lemmas
as an algebraic proof target, but has **not** yet been added as a Lean theorem.
No numerical value or cancellation with other strata is claimed. The current
Lean and Python CI passed for documentation commit
`6791424dc4bad8d71127c257dc6e8e164a8fbc90`; a new source-level proof and its
CI verification are still needed before this reduction can be treated as
machine-checked.


## 4w. Numerical evaluation of the p=6, r=6 boundary term (conditional calculation)

For the concrete Sierpinski-gasket gluing, the support of `(sgGlue m).g`
contains six geometric corner endpoints (two per copy) and two spin states
per endpoint, hence 12 indexed states. At level m >= 1, each outer corner
has graph degree 2. Under this corner-degree fact, `sgK_diag` makes each
summand in the p=6 all-pairing boundary expression equal to
`2^3 * 2^3 = 64`. Summing over the 12 support states gives the boundary
contribution `12 * 64 = 768`, not zero.

This is a concrete arithmetic evaluation of the identified boundary
expression, conditional on the support-cardinality and corner-degree facts.
Those facts and the resulting specialization have not yet been assembled
into a machine-checked Lean theorem in this branch. Therefore 768 is recorded
as a derived diagnostic, not as a CI-verified theorem or as a disproof of the
full residual identity: cancellation against other strata remains logically
possible and would require a separate weighted identity preserving all orbit
multiplicities.


## 4x. Same all-pairing arithmetic for p=8 and p=10 (conditional)

For the top even strata r=p, the boundary formula contains p/2 corner-diagonal
factors and p/2 intervening K factors. Under the same support-diagonality and
corner-degree assumptions recorded in 4w, each of these p factors contributes
2 to each summand. Thus each support state contributes `2^p`, and the 12
support states contribute `12 * 2^p`. The conditional diagnostic values are:

- p=8, r=8: `12 * 2^8 = 3,072`.
- p=10, r=10: `12 * 2^10 = 12,288`.

This count includes both the corner-diagonal factors and the intervening K
factors; it does not count only the `N*K*N` blocks.

These are conditional evaluations of the all-pairing boundary terms, not
machine-checked Lean theorems. They show that the top even stratum itself
does not vanish under the stated degree assumptions. They do not rule out
cancellation with lower-r strata in the full p=8 or p=10 residual identity;
that requires the complete weighted sum over all ordered representatives
and their orbit multiplicities. No such cross-stratum cancellation is claimed.



## Exact finite calculation checkpoint: theta = pi, H6/H8/H10

The branch `moment-6-8-10` now includes a sparse matrix-power calculation over
Gaussian integers ℤ[i]. At θ = π, the operator entries are exact integers
or Gaussian integers, so these trace differences are not floating-point
approximations. The Python tests compute Δ_m^{(p)} = Tr(H_C^p) - Tr(H_{C'}^p)
independently for levels m = 1,...,5:

| m | Δ(H⁶) | Δ(H⁸) | Δ(H¹⁰) |
|---:|---:|---:|---:|
| 1 | -6,744 | -547,552 | -32,992,520 |
| 2 | -14,976 | -1,373,696 | -94,971,520 |
| 3 | -39,648 | -3,843,584 | -280,407,040 |
| 4 | -113,664 | -11,253,248 | -836,713,600 |
| 5 | -335,712 | -33,482,240 | -2,505,633,280 |

For R_m^{(p)} = Δ_m^{(p)} - 3Δ_{m-1}^{(p)}, the exact sequences for
m = 2,...,5 are:

- H⁶: 5,256; 5,280; 5,280; 5,280.
- H⁸: 268,960; 277,504; 277,504; 277,504.
- H¹⁰: 4,006,040; 4,507,520; 4,507,520; 4,507,520.

Thus the exact finite computations establish stabilization of these residuals
from m = 3 through m = 5 at θ = π for the concrete matrices in this
repository. This is evidence for a recurrence, not a proof for all m or all
angles. The all-level analytic cancellation of the remaining even boundary
strata is still open, and the H⁶/H⁸/H¹⁰ closed forms are not
claimed as proved.

Verification at commit `5b260c1ab203ca39754cd2585f9195ccc9843a1d`:
- Lean formalization build: passed.
- Python test suite, including fast and slow tests, on Python 3.11 and 3.12: passed.


## Finite-level extension: checking the next transition

The regression suite has also been extended beyond levels 1--5. For each
$p \in \{6,8,10\}$ it checks, on a fixed five-angle set, the numerical
identity
\[
R_5^{(p)}(\theta)=R_6^{(p)}(\theta),\qquad
R_m^{(p)}(\theta)=\Delta_m^{(p)}(\theta)-3\Delta_{m-1}^{(p)}(\theta).
\]
Separate grid tests check $R_3=R_4=R_5$ over 11 angles, and $R_3=R_4$ over
a 17-angle grid. These are finite numerical stress tests with explicit
floating-point tolerances; they are not proofs for a continuum of angles or
all levels.

CI verification at commit `65cc18d9b36f4ed1f14f4145c1c3ba9525b1e266`:
- Lean formalization: passed.
- Python test workflow: passed.

The proof obligation is unchanged: derive the weighted cancellation among the
remaining even-pairing boundary strata for arbitrary level and angle. The
current finite tests provide further evidence, but do not discharge that
obligation.


## Candidate closed forms at the special angle θ = π

The exact residual data suggest the following compact formulas, restricted to
the special angle θ = π and levels m ≥ 3:

- H⁶: Δ_m(π) = −37008 · 3^(m−3) − 2640.
- H⁸: Δ_m(π) = −3704832 · 3^(m−3) − 138752.
- H¹⁰: Δ_m(π) = −278153280 · 3^(m−3) − 2253760.

These are obtained by solving the first-order recurrence
Δ_m − 3Δ_(m−1) = R, using the exact residuals R = 5280, 277504,
4507520 observed from m = 4 onward. The added exact-integer regression
checks verify these formulas only at m = 3, 4, 5, 6. They are therefore
finite-data-supported candidates, not a proof of the recurrence for all
m. In particular, they do not provide the missing all-angle formulas for
H⁶, H⁸, or H¹⁰.


## Exact-arithmetic regression refresh (2026-10-22)

The sparse finite-level certificate now uses Python-integer Gaussian arithmetic
through every matrix product, rather than complex floating-point sparse
multiplication followed by an integer-valuedness check. The regression test
checks the full delta sequence for levels 1--6 and the five residuals for
levels 2--6, for each of p = 6, 8, 10.

| m | Δ(H⁶) | Δ(H⁸) | Δ(H¹⁰) |
|---:|---:|---:|---:|
| 1 | -6,744 | -547,552 | -32,992,520 |
| 2 | -14,976 | -1,373,696 | -94,971,520 |
| 3 | -39,648 | -3,843,584 | -280,407,040 |
| 4 | -113,664 | -11,253,248 | -836,713,600 |
| 5 | -335,712 | -33,482,240 | -2,505,633,280 |
| 6 | -1,001,856 | -100,169,216 | -7,512,392,320 |

The residual sequences for m = 2,...,6 are:

- H⁶: 5,256; 5,280; 5,280; 5,280; 5,280.
- H⁸: 268,960; 277,504; 277,504; 277,504; 277,504.
- H¹⁰: 4,006,040; 4,507,520; 4,507,520; 4,507,520; 4,507,520.

CI at commit `95e65dd4539e291be672c28b3152816da2e2fd9f`:
- Python tests on Python 3.11 and 3.12: passed.
- Lean formalization build: passed.

This closes the exact finite-data checkpoint through level 6. It does not
close the proof obligation identified in Sections 4t--4x: even-stratum
boundary expressions can be nonzero individually, and their weighted
cancellation in the full moment difference remains unproved. In particular,
the formulas at θ = π remain finite-data-supported conjectures, not all-level
theorems.

## 4y. Concrete consequence: the top strata force cross-stratum accounting

The all-pairing diagnostics in Sections 4w and 4x imply a useful constraint on
any proposed proof strategy. Under the stated support-diagonality and corner
degree assumptions, the top strata contribute respectively 768, 3,072, and
12,288 for p = 6, 8, and 10. Therefore a proof cannot close by declaring every
even stratum zero separately. If the target trace identity is correct, its
boundary bookkeeping must either (i) exhibit an exact cancellation of each
top-stratum term against lower even strata with the correct ordered-word
multiplicities, or (ii) show that the hypotheses used in the diagnostic do not
hold for the particular comparison being evaluated. The latter must be
demonstrated explicitly; it cannot be silently assumed.

For the next formal step, retain the boundary terms as named quantities rather
than simplify them to zero. For each p, define B_{p,r} to be the sum of the
boundary expression for the r-pairing stratum over canonical cyclic
representatives, weighted by their rotation-orbit sizes. The required
closure obligation is then a finite, explicit identity among the B_{p,r}
(and the all-K term) for p = 6, 8, and 10. The Python inventory already
supplies the representatives and orbit weights; the missing mathematical
content is the operator-level evaluation of these weighted boundary sums.
This notation is a proof plan only: no B_{p,r} cancellation theorem is claimed
by this section, and no new Lean theorem or CI result is implied.


## Exact level-seven extension (2026-10-22)

The exact sparse Gaussian-integer regression has now been extended to level
7 for all three even powers. The tests assert the candidate special-angle
formula and its residual directly against `delta_at_pi` and
`residual_at_pi`, which recompute the traces from the sparse operator rather
than substituting the candidate formula into itself.

| p | exact Δ₇(π) checked | exact R₇(π) checked |
|---:|---:|---:|
| 6 | -3,000,288 | 5,280 |
| 8 | -300,230,144 | 277,504 |
| 10 | -22,532,669,440 | 4,507,520 |

Both Python CI matrix jobs (3.11 and 3.12), including the slow-test stage, and
the Lean formalization build passed for the code commit
`e47287354d62d44c9857afc71f06a3ae583ec98e`.

This adds one more exact finite-level checkpoint for the `θ = π` candidates.
It still does not establish their validity for all levels, nor the desired
all-angle identity. The unresolved proof obligation remains the weighted
cancellation of the nonzero even-pairing boundary strata; the new tests do
not discharge it.


## 4z. Exact bookkeeping target for the even strata

The cancellation claim should be stated as axis-independence of the *total*
boundary correction, not as vanishing of each stratum. This distinction is
necessary because the top-stratum diagnostics in Sections 4w--4x are nonzero.

Fix an even power p in {6, 8, 10}. Write an ordered word as a binary word
u of length p, where 1 marks a selected K*N factor and 0 marks a K factor.
Let r(u) be the number of 1s. For each cyclic class [u], let o(u) be its
rotation-orbit size (the number of distinct rotations, not p divided by an
assumed generic stabilizer). Let E_{p,r,[u]}(ax) denote the boundary expression
obtained by applying the already formalized N-boundary reduction to that
ordered word for axis function ax; for a word in a class this expression is
read after the corresponding cyclic rotation of the trace. Define the weighted
stratum quantity

  B_{p,r}(ax) = sum_{[u] : r(u)=r} o(u) * E_{p,r,[u]}(ax).

This definition is a bookkeeping specification; E is intentionally left as
the output of the relevant boundary theorem, rather than silently replacing
it by zero. The orbit weight ensures that the sum is over the original
ordered expansion with multiplicity. The combinatorial sanity check is
  sum_{[u] : r(u)=r} o(u) = binomial(p,r),
which must hold for every p and r. In particular the complete word counts
are 64, 256, and 1024 for p=6, 8, and 10 respectively.

The already established odd-stratum vanishing lemmas remove odd r under their
stated OAnti and exponent hypotheses. The r=0 term is the unglued K^p trace.
Consequently the remaining correction has the schematic form

  F_p(ax) = B_{p,2}(ax) + B_{p,4}(ax) + ... + B_{p,p}(ax),

with the precise E expressions determined class-by-class by the existing
four-, six-, eight-, and ten-N boundary formulas. The required recurrence
closure is the identity

  F_p(ax) = F_p(ax')

for admissible axis functions ax, ax' (equivalently, the difference of these
weighted sums is zero). It is *not* justified to assert B_{p,r}=0 separately.
For p=6 the target is B_{6,2}+B_{6,4}+B_{6,6} axis-independent; for p=8
it is B_{8,2}+B_{8,4}+B_{8,6}+B_{8,8}; for p=10 it is
B_{10,2}+B_{10,4}+B_{10,6}+B_{10,8}+B_{10,10}.

The present Lean development proves reductions of individual ordered words to
boundary expressions and proves the degree-four axis-independence argument,
but does not yet define these B quantities or prove the displayed higher-power
axis-independence identities. The next formal implementation should introduce
the ordered-word/cyclic-class indexing and the orbit-size multiplicity lemma
before attempting any operator-level cancellation. Until those lemmas compile,
this section is a precise proof obligation, not a Lean theorem or a claimed
proof of the moment recurrence.

## 4aa. The two-pairing layer is the base case for boundary-sum comparison

The next useful reduction is to separate the lowest even layer from the genuinely nested ones. For a word with exactly two occurrences of K*N, let the two cyclic K-gaps be g1,g2 >= 0, with g1+g2=p-2. The corresponding powers between successive N factors are g1+1 and g2+1, because each selected K*N contributes its own leading K.

Write the cyclic word as K^(g1+1) * N * K^(g2+1) * N, with g1+g2=p-2. This has total K-degree p and is the specialization (a,b,c)=(g1+1,g2+1,0) of trace_two_N_powers. Its boundary expression is exactly the sum over glued x of (K^(g1+1))(x,x) times (K^(g2+1))(sigma(x),sigma(x)), assuming the required corner-vanishing hypothesis for the middle power K^(g2+1). The order of the two gaps can be exchanged by choosing the other cyclic representative; no commutation of N through K is used.

For p=6,8,10, the r=2 class counts are respectively 3, 4, and 5, while the ordered-word multiplicities are binomial(p,2)=15,28,45. Their cyclic gap representatives are already recorded in trace_word_inventory_p6_p8_p10.json; each representative's orbit size is its weight. This layer is therefore the simplest place to define a concrete B_{p,2} in Lean and verify that the gap encoding agrees with the generic two-N theorem.

This does not by itself yield the required cancellation: B_{p,2} must be compared with the r=4 and higher even boundary sums. The higher layers contain products of several diagonal boundary factors separated by K powers, so their comparison requires additional structure (for example, a common endpoint-sum identity), not just the orbit-count lemma. No such identity is asserted here.
## 4ab. Closed weighted formula for the two-N stratum

The r=2 orbit bookkeeping can be collapsed into a single gap sum. Define, for 1 <= a <= p-1,

  E_a := sum_{x : G.g(x)} (K^a)(x,x) * (K^(p-a))(sigma(x),sigma(x)).

By `trace_two_N_powers`, the cyclic word with gaps (a-1,p-a-1) has boundary contribution E_a, whenever the corner-vanishing premise for K^(p-a) is available. The cyclic gap classes are unordered pairs {a,p-a}: for a != p-a the class orbit has size p, while for a=p-a its orbit has size p/2. Therefore the orbit-weighted sum over the r=2 classes is exactly

  B_{p,2} = (p/2) * sum_{a=1}^{p-1} E_a.

The factor p/2 is valid because each unequal pair {a,p-a} appears twice in the ordered sum and each equal pair appears once. This is a combinatorial identity, not a cancellation claim. The orbit totals it reproduces are 15, 28, and 45 for p=6, 8, and 10.

Equivalently, the lowest even stratum is now reduced to a single weighted sum of products of diagonal entries of complementary powers of K. The unresolved step is to express the r=4, r=6, ... boundary strata in a compatible form and prove that their sum cancels the axis-dependent part of this expression. The current Lean theorem supplies each E_a once its hypotheses are met; it does not yet prove the global cross-stratum identity.
## 4ac. Explicit r=4 boundary kernel and finite indexing target

The next stratum is r=4. For a cyclic gap tuple (g1,g2,g3,g4), with each gi >= 0 and sum gi=p-4, the corresponding word is cyclically represented by

  K^(g1+1) * N * K^(g2+1) * N * K^(g3+1) * N * K^(g4+1) * N.

Applying `trace_four_N_powers_explicit` after cyclic rotation gives the boundary kernel

  sum_{x:g(x)} [ sum_{y:g(y)} ((K^(g1+1))(x,y) * (K^(g2+1))(sigma(y),sigma(y))) * (K^(g3+1))(y,x) ] * (K^(g4+1))(sigma(x),sigma(x)),

with the exponents aligned to the theorem arguments (a,b,c,d,e)=(g1+1,g2+1,g3+1,g4+1,0) after rotating the word so that the final outside exponent is zero. In particular, the first matrix factor in the inner sum is K^(g1+1), since e=0; there is no extra K^(g4+1) factor on its left. If a different cyclic representative is used, the same theorem must be instantiated with that representative's ordered gaps; the factors must not be commuted.

For fixed p, the r=4 cyclic classes are necklaces of four nonnegative gaps summing to p-4, modulo cyclic rotation. Their orbit size is the number of distinct rotations of the gap tuple, and it supplies the exact multiplicity in B_{p,4}. The inventory already gives 3, 5, and 14 classes for p=6, 8, and 10 respectively (their weighted totals must be binomial(p,4)=15,70,210).

This gives a concrete finite target for implementation: generate each canonical four-gap tuple, retain its rotation-orbit size, instantiate the four-N boundary formula with the corresponding ordered exponents, and sum. The remaining proof is then an equality of these explicit double endpoint sums with the r=2 and higher even-stratum kernels. The formula itself does not imply that this equality holds.
### Ordered-gap summation formula for B_{p,4}

Let E(g1,g2,g3,g4) be the four-N boundary kernel above. The sum over cyclic classes weighted by the original binary-word orbit size can be rewritten as

  B_{p,4} = (p/4) * sum_{g1+g2+g3+g4=p-4, gi>=0} E(g1,g2,g3,g4),

where the sum is over all ordered four-tuples of nonnegative gaps. Reason: an r-marked binary word has a cyclic orbit p/r times the size of the corresponding gap-tuple rotation orbit. Thus for r=4, the word-orbit weight is p/4 times the gap-orbit weight. Since E is invariant under cyclic rotation of the word by trace cyclicity, summing once over all ordered gap tuples is equivalent to summing each gap necklace with its gap-orbit size.

This gives a direct computational indexing set without needing a separate canonical-necklace representative in the formula. The number of ordered tuples is binomial(p-1,3), namely 10, 35, and 84 for p=6, 8, and 10; the prefactor p/4 restores the original word multiplicities, giving total weights binomial(p,4)=15, 70, and 210. This is the r=4 analogue of B_{p,2}=(p/2) sum_{a=1}^{p-1} E_a.

Important: this identity only reorganizes multiplicities. It does not assert that E is equal across tuples, nor that B_{p,4} cancels B_{p,2}.
## 4ad. General weighted gap formula for every stratum

The r=2 and r=4 prefactors are instances of one exact orbit identity. Fix 1 <= r <= p and let E(g1,...,gr) be the trace contribution assigned to the cyclic word with gap tuple g, where gi >= 0 and sum gi=p-r. Assume E is invariant under cyclic rotation of g, as it is when it is obtained from a trace and the corresponding word is cyclically rotated. Then

  B_{p,r} = (p/r) * sum_{g1+...+gr=p-r, gi>=0} E(g1,...,gr).

Proof of the multiplicity factor: a gap tuple has r positions, while its binary word has p positions. If the tuple has rotational stabilizer of size s, its gap orbit has size r/s and the corresponding binary-word orbit has size p/s. Their ratio is p/r. Thus weighting cyclic word classes by their word-orbit sizes is exactly p/r times summing the rotation-invariant E over all ordered gap tuples. This argument also handles periodic tuples; no assumption of a full orbit is needed.

The finite inventory/test suite now checks the counts and weights for every even stratum relevant to p=6,8,10. This resolves the indexing and multiplicity issue uniformly. It does not resolve the operator identity: each E still depends on the ordered gap tuple through products of K powers and diagonal boundary factors. The remaining theorem is the axis-independence of the sum over all even r after substituting the appropriate boundary kernel for each r.

### Implementation correction: compute the orbit ratio after multiplying

The exact class weight is (p * gap_orbit_size) / r, not (p // r) * gap_orbit_size. The latter incorrectly truncates p/r when r does not divide p (for example p=6,r=4). Since a gap orbit size is r divided by its rotational stabilizer, the product p * gap_orbit_size is divisible by r, so integer division after multiplication is exact. The inventory implementation now uses (p * len(members)) // r, and a new regression test compares the multiset of gap-derived word weights with the actual binary-necklace orbit weights class by class for every p in {6,8,10} and every 1 <= r <= p. Workflow status for this test commit has not yet appeared, so it should be treated as added but not CI-verified.

## 4ae. Six-N boundary kernel from the existing Lean theorem

The existing `trace_six_N_powers_boundary` gives a concrete kernel for r=6, rather than an unspecified E. Let a six-gap tuple g=(g1,...,g6) satisfy gi >= 0 and sum gi=p-6. Choose the cyclic word

  K^(g1+1) N K^(g2+1) N K^(g3+1) N K^(g4+1) N K^(g5+1) N K^(g6+1) N.

Instantiate `trace_six_N_powers_boundary` with (a,b,c,d,e,f,g)=(g1+1,g2+1,g3+1,g4+1,g5+1,g6+1,0). The theorem reduces the trace to

  trace( K^(g1+1) * D_(g2+1) * K^(g3+1) * D_(g4+1) * K^(g5+1) * D_(g6+1) ),

where D_q is the diagonal matrix with entries (K^q)(sigma(y),sigma(y)) on glued indices and zero elsewhere. This instantiation requires the three explicit corner-vanishing hypotheses for the powers K^(g2+1), K^(g4+1), and K^(g6+1). Those hypotheses must be discharged from the available `GlueDiag`/OAnti lemmas for each concrete tuple; they must not be dropped from the statement.

Thus the six-N layer is a trace of three K-power blocks alternating with three diagonal boundary blocks. Its weighted sum is (p/6) times the sum of this kernel over all ordered six-gap tuples summing to p-6, provided cyclic invariance is established for the chosen kernel. This makes B_(6,6) at p=6 the single tuple (0,0,0,0,0,0), with kernel trace(K D_1 K D_1 K D_1); for p=8 and p=10 the same formula ranges over 7 and 84 ordered tuples respectively.

This is an explicit operator-level target, but not yet the cancellation identity: the alternating diagonal kernels for r=6 must still be compared with the r=2, r=4, and, for p>=8, r=8 and higher layers.
## 4af. Hypothesis audit: `GlueDiag` does not discharge the six-N corner premises

A crucial distinction surfaced when matching the generic six-N theorem to the gasket-specific lemmas. `trace_six_N_powers_boundary` requires, for each selected exponent q=b,d,f, the condition

  ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → (K^q) w w' = 0.

By contrast, `sgK_pow_GlueDiag_of_OAnti` proves `GlueDiag (sgGlue m) (sgK^q)`, whose definition has the additional premise `cp (σ w) = cp (σ w')`. This is strictly weaker: it does not cover pairs of distinct glued corners whose partners lie in different copies. Therefore it is not valid to claim that the three hkg premises in the six-N theorem follow directly from `sgK_pow_GlueDiag_of_OAnti`.

The exact next Lean obligation is a stronger corner-off-diagonal lemma: under `OAnti (m+1) o`, prove `(sgK m θ ax o ^ q) w w' = 0` for distinct glued w,w' in the same copy, with no equality assumption on the copy labels of their partners. The case q=1 is `sgK_hkg`; the needed q>1 result is not supplied by the current GlueDiag theorem. Any proof must use the geometry of distinct gasket corners and the structure of powers, or derive an alternative boundary theorem whose hypotheses genuinely match `GlueDiag`.

This audit corrects the proof plan: the six-N kernel written in §4ae is a valid specialization of the generic theorem only once these stronger premises are established. Until then, it is a conditional reduction, not an instantiated gasket theorem.
### Refined next obligation: use a distance bound, not an all-powers corner lemma

The stronger lemma proposed above must not be stated for arbitrary q without a distance hypothesis: powers of a graph adjacency operator can connect distinct corners once q reaches their graph distance. The plausible geometric route is instead to prove that distinct corners in one gasket copy have graph distance at least 2^m, then derive the needed zero entry for q < 2^m by induction on matrix powers (or by a path-expansion lemma).

For fixed moment degree p in the intended large-level regime 2^m > p, every selected exponent q <= p is below this distance threshold, so the six-N corner hypotheses may follow. This is only a proof strategy until the corner-distance theorem and the power-entry lemma are formalized. It also leaves small levels with 2^m <= p to be handled separately; do not silently claim the boundary formula for those levels.
## 4ag. Exact level thresholds for applying the six-N boundary theorem

For an r=6 gap tuple in degree p, each selected middle exponent is gi+1 and the gap sum is p-6. Consequently gi+1 <= p-5, not merely <= p. Thus the new `trace_six_N_powers_boundary_of_OAnti` applies uniformly to every r=6 word of total degree p as soon as p-5 < 2^m.

For the target degrees this gives:

- p=6: all middle exponents equal 1; the bound requires 1 < 2^m, hence m >= 1.
- p=8: every middle exponent is at most 3; it suffices that m >= 2.
- p=10: every middle exponent is at most 5; it suffices that m >= 3.

These are sufficient level thresholds for the six-N boundary reduction only. They do not show that the six-N contribution vanishes, nor that it cancels the other even strata. For levels below these thresholds, the generic boundary theorem remains conditional on the individual corner premises.
## 4ah. Eight-N wrapper: exact degree thresholds

`trace_eight_N_powers_boundary_of_OAnti` has four middle exponents b,d,f,h. For a gap tuple with r=8 and total degree p, the eight nonnegative gaps sum to p-8, so each middle exponent is at most p-7. Hence all eight-N words satisfy the wrapper's distance bounds when p-7 < 2^m.

- p=8: each middle exponent is 1; it suffices that m >= 1.
- p=10: each middle exponent is at most 3; it suffices that m >= 2.

Together with the r=6 wrapper, this supplies conditional boundary reductions for the r=6 layer in degrees 6,8,10 and the r=8 layer in degrees 8,10, at the stated levels. It still does not supply an r=10 wrapper, and none of these reductions prove cancellation between the even strata.
## 4ai. Ten-N wrapper and uniform degree thresholds

The new `trace_ten_N_powers_boundary_of_OAnti` discharges the five corner premises for the r=10 boundary theorem when b,d,f,h,j < 2^m. In a degree-p word with ten N factors, the ten gaps sum to p-10, so each middle exponent is at most p-9.

For the target p=10, all gaps are zero and all five middle exponents are 1; the sufficient bound is 1 < 2^m, i.e. m >= 1. The wrapper therefore covers the unique r=10 word at degree ten at every positive level, conditional on its underlying geometric distance lemma and successful Lean compilation.

At this point wrappers have been authored for r=6,8,10. This is a source-level milestone only: current visible Actions results do not include these latest wrapper commits, so compilation remains unverified. More importantly, even successful compilation would only establish the boundary reductions. The main remaining theorem is still the exact cancellation/axis-independence identity across all even strata.

## 4aj. CI verification after namespace repair; remaining theorem stated precisely

Commit `832674619617357e2a7d0c3e8822920388fd141d` repairs the namespace around the concrete (r=6,8,10) boundary wrappers in `GlueCorner.lean`. Both GitHub Actions workflows completed successfully on that exact commit:

- Lean formalization, push: run `39831944688` — success.
- Python tests, push: run `39831944779` — success.
- The corresponding pull-request runs `39831954958` (Lean) and `39831955466` (Python) also succeeded.

Thus the current wrappers compile and the Python regression suite passes. This is a verified source/CI milestone, not a proof of the higher-moment recurrence.

### Exact remaining mathematical obligation

For each (p\in\{6,8,10\}), the word expansion of ((K+KN)^p) has already been partitioned by the number (r) of (KN) factors, with exact cyclic-orbit multiplicities. Odd strata are handled by the existing conditional vanishing lemmas; the even strata (r=2,4,6) (and (r=8) for (p=8,10), (r=10) for (p=10)) reduce to boundary kernels under the stated corner hypotheses.

What is still missing is an identity between the **weighted sums of those even-stratum boundary kernels** that yields the desired axis-independence / defect recursion. The (r=6,8,10) wrappers only expose the kernels; they do not make them zero and do not compare them with lower even strata. No all-level theorem
[
\Delta_m^{(p)}(\theta)=3\Delta_{m-1}^{(p)}(\theta)+C_p(\theta)
]
for (p=6,8,10) has been proved by the work recorded here.

Finite exact data at (\theta=\pi) supports a stable residual from level (m\ge3) in the tested range, but that is evidence for a conjecture, not a proof for general (\theta\) or all levels. Do not promote the finite regression to a theorem. The next proof step must derive the cross-stratum kernel identity (or find a counterexample); adding more individual boundary wrappers is not a substitute.

## 4ak. Reversal pairing census for even strata

The combinatorial reversal quotient was refined into a fixed-vs-paired census. For each cyclic gap class, reverse the gap tuple, canonicalize by cyclic rotation, and pair the two cyclic classes if they differ. This is still a combinatorial partition only: no equality of the associated matrix traces is assumed.

Exact results (fixed classes, paired orbits, fixed word weight, paired word weight):

| p | r | fixed | paired | fixed weight | paired weight | total |
|---:|---:|---:|---:|---:|---:|---:|
| 6 | 2 | 3 | 0 | 15 | 0 | 15 |
| 6 | 4 | 3 | 0 | 15 | 0 | 15 |
| 6 | 6 | 1 | 0 | 1 | 0 | 1 |
| 8 | 2 | 4 | 0 | 28 | 0 | 28 |
| 8 | 4 | 6 | 2 | 38 | 32 | 70 |
| 8 | 6 | 4 | 0 | 28 | 0 | 28 |
| 8 | 8 | 1 | 0 | 1 | 0 | 1 |
| 10 | 2 | 5 | 0 | 45 | 0 | 45 |
| 10 | 4 | 10 | 6 | 90 | 120 | 210 |
| 10 | 6 | 10 | 6 | 90 | 120 | 210 |
| 10 | 8 | 5 | 0 | 45 | 0 | 45 |
| 10 | 10 | 1 | 0 | 1 | 0 | 1 |

The total weight in each row agrees with \(\binom{p}{r}\). Nontrivial reversal pairs occur only at (p,r)=(8,4),(10,4),(10,6) in this census. If an independently proved trace-reversal identity is available for the model, these pairs could reduce the number of distinct algebraic cases; without it they must remain separate. In particular, this census does not itself prove the cross-stratum cancellation needed for the all-level recurrence.

## 4al. Full binary-word reversal quotient

The reversal grouping was extended from individual even-r gap inventories to all binary factor words of lengths p=6,8,10. This groups cyclic necklace classes under word reversal, preserving the exact size of each rotation orbit. The result is a smaller combinatorial census, but it does not assert equality of the corresponding operator traces.

| p | all words | cyclic classes | classes after reversal pairing |
|---:|---:|---:|---:|
| 6 | 64 | 14 | 13 |
| 8 | 256 | 36 | 30 |
| 10 | 1024 | 108 | 78 |

The weight sum remains exactly (2^p) for each p, and every reversal group contains either one or two cyclic classes. This provides a whole-expansion inventory to complement the even-stratum gap census.

Mathematical caveat: trace cyclicity identifies rotations. It does not, by itself, identify a word with its reversal. To use this quotient to reduce the operator calculation, one must prove a reversal identity for the actual factors K and K*N (for example, via a suitable transpose/dagger relation and the hypotheses on N). Until that is established, the 13/30/78 values are counts of candidate symmetry classes, not counts of distinct trace values. The cross-stratum cancellation identity and the all-level defect recurrence remain open.

## 4am. Reversal classes resolved by KN-count strata

The full-word reversal census has now been stratified by the number r of (KN) factors. This is more useful than the global 13/30/78 totals because the trace expansion and the boundary formulas are organized by r. The exact values below are computed from binary words and cyclic orbit weights; each stratum total is checked against (inom{p}{r}).

| p | r | cyclic classes | reversal classes | paired reversal orbits | fixed weight | paired weight |
|---:|---:|---:|---:|---:|---:|---:|
| 6 | 2 | 3 | 3 | 0 | 15 | 0 |
| 6 | 3 | 4 | 3 | 1 | 8 | 12 |
| 6 | 4 | 3 | 3 | 0 | 15 | 0 |
| 8 | 2 | 4 | 4 | 0 | 28 | 0 |
| 8 | 3 | 7 | 5 | 2 | 24 | 32 |
| 8 | 4 | 10 | 8 | 2 | 38 | 32 |
| 8 | 5 | 7 | 5 | 2 | 24 | 32 |
| 8 | 6 | 4 | 4 | 0 | 28 | 0 |
| 10 | 2 | 5 | 5 | 0 | 45 | 0 |
| 10 | 3 | 12 | 8 | 4 | 40 | 80 |
| 10 | 4 | 22 | 16 | 6 | 90 | 120 |
| 10 | 5 | 26 | 16 | 10 | 52 | 200 |
| 10 | 6 | 22 | 16 | 6 | 90 | 120 |
| 10 | 7 | 12 | 8 | 4 | 40 | 80 |
| 10 | 8 | 5 | 5 | 0 | 45 | 0 |

The census is symmetric under (r\leftrightarrow p-r), as expected for complementing the binary factor labels. For even r-strata, this identifies exactly which strata contain nontrivial reversal pairs. The combinatorics is now pinned by tests; it still does not establish equality of traces within reversal pairs. Since transpose reverses products but also transposes each factor, a proof must explicitly relate (K^T) and ((KN)^T) to the factors in the original word. No such identity is inferred from cyclicity alone.

## 4an. Expanded operator words after substituting each KN as K·N

The previous inventory treats each chosen factor as either (K) or the compound factor (KN). For the boundary analysis, expand each compound factor explicitly as two letters (K,N). A factor word with p slots and r occurrences of (KN) becomes a matrix word of length p+r containing exactly p copies of K and r copies of N.

Grouping these expanded words under cyclic rotation and reversal gives the following exact census for 1 ≤ r ≤ p−1:

| p | r | expanded length p+r | reversal classes | factor-word weight |
|---:|---:|---:|---:|---:|
| 6 | 1 | 7 | 1 | 6 |
| 6 | 2 | 8 | 3 | 15 |
| 6 | 3 | 9 | 3 | 20 |
| 6 | 4 | 10 | 3 | 15 |
| 6 | 5 | 11 | 1 | 6 |
| 8 | 1 | 9 | 1 | 8 |
| 8 | 2 | 10 | 4 | 28 |
| 8 | 3 | 11 | 5 | 56 |
| 8 | 4 | 12 | 8 | 70 |
| 8 | 5 | 13 | 5 | 56 |
| 8 | 6 | 14 | 4 | 28 |
| 8 | 7 | 15 | 1 | 8 |
| 10 | 1 | 11 | 1 | 10 |
| 10 | 2 | 12 | 5 | 45 |
| 10 | 3 | 13 | 8 | 120 |
| 10 | 4 | 14 | 16 | 210 |
| 10 | 5 | 15 | 16 | 252 |
| 10 | 6 | 16 | 16 | 210 |
| 10 | 7 | 17 | 8 | 120 |
| 10 | 8 | 18 | 5 | 45 |
| 10 | 9 | 19 | 1 | 10 |

Every stratum preserves the original factor-word weight (inom{p}{r}); all strata together sum to (2^p). This is a more operator-faithful inventory because it exposes the interleaving of K and N instead of treating KN as an indivisible symbol.

Important caveat: the reversal quotient remains a symbolic candidate quotient. In the concrete model, the established Hermiticity statement is for the **conjugate transpose** of the copy operator. It does not automatically imply a plain-transpose identity for each K and N letter, nor does it prove equality of traces for all reversed expanded words. The next formal step must derive the appropriate adjoint relation for the glued operator and pairing matrix, then use cyclicity to identify exactly which expanded-word traces are equal. The cross-stratum cancellation and all-level recurrence remain unproved.

## 4ao. Adjoint reversal induces an involution on cyclic factor words

A useful distinction emerged between reversing the expanded matrix word and reversing the original two-choice factor word. A factor word of length p is expanded by replacing each (KN) tile with (K,N). Reversing the expanded circular word still admits a (K) / (KN) tiling after choosing a cyclic boundary, so it induces a map on cyclic factor classes. The implementation now constructs this map explicitly and checks that it preserves r and is an involution on cyclic classes for p=6,8,10.

The exact census below gives (cyclic classes, fixed cyclic classes, paired orbits, fixed factor-word weight):

| p | r | cyclic classes | fixed classes | paired orbits | fixed weight | paired weight |
|---:|---:|---:|---:|---:|---:|---:|
| 6 | 2 | 3 | 3 | 0 | 15 | 0 |
| 6 | 3 | 4 | 2 | 1 | 8 | 12 |
| 6 | 4 | 3 | 3 | 0 | 15 | 0 |
| 8 | 2 | 4 | 4 | 0 | 28 | 0 |
| 8 | 3 | 7 | 3 | 2 | 24 | 32 |
| 8 | 4 | 10 | 6 | 2 | 38 | 32 |
| 8 | 5 | 7 | 3 | 2 | 24 | 32 |
| 8 | 6 | 4 | 4 | 0 | 28 | 0 |
| 10 | 2 | 5 | 5 | 0 | 45 | 0 |
| 10 | 3 | 12 | 4 | 4 | 40 | 80 |
| 10 | 4 | 22 | 10 | 6 | 90 | 120 |
| 10 | 5 | 26 | 6 | 10 | 52 | 200 |
| 10 | 6 | 22 | 10 | 6 | 90 | 120 |
| 10 | 7 | 12 | 4 | 4 | 40 | 80 |
| 10 | 8 | 5 | 5 | 0 | 45 | 0 |

Fixed and paired weights sum to (inom{p}{r}) in every row. The strata r=0,1,p−1,p have only fixed classes and are omitted from the table.

This gives the correct combinatorial partner for the adjoint relation: if the concrete matrices K and N are Hermitian, then the trace of an expanded product is conjugated when the order of all K/N letters is reversed. The retiling map therefore pairs factor-word contributions by complex conjugation, not necessarily by equality. Consequently the full weighted expansion is real, and any paired orbit contributes twice the real part of one representative trace. This does not yet prove that individual traces are real or that the cross-stratum boundary contributions cancel. Those remain separate obligations for the recurrence proof.

## 4ap. Remove the top-stratum constant before searching for p=6 cancellation

The all-pairing boundary term should not be targeted for vanishing. Under the
support-diagonality and corner-degree facts in §§4u–4x, its value depends only
on the degree-two outer corners, not on the orientation/axis choice. The
conditional values are
`B_{6,6}=768`, `B_{8,8}=3072`, and `B_{10,10}=12288`.
For two operator choices on the same gasket graph, these top-stratum constants
therefore cancel when taking their trace-defect difference, provided the
same gluing support and diagonal-degree hypotheses are used on both sides.

This sharpens the p=6 target. Writing the nontrivial even boundary contribution
as `B_{6,2}+B_{6,4}+B_{6,6}`, the next identity to prove is not
`B_{6,6}=0`, which is false under the stated hypotheses. Instead, compare
the two operator choices and prove the required relation for
`(B_{6,2}+B_{6,4})-(B'_{6,2}+B'_{6,4})`; the top term drops out separately.
For p=8 and p=10, the analogous comparison must include all lower even
strata, while the top term can be removed from the comparison under the same
hypotheses.

This is a reduction of the proof target, not a new Lean theorem. The constants
remain conditional diagnostics until their support cardinality and diagonal
degree premises are assembled into a machine-checked result. No cancellation
between the lower even strata is claimed here.

## 4aq. CI confirmation for the refined p=6 target

The documentation-only target refinement in commit
`2b33a6db1d92fd602c9e280a49058c9f4f96cf38` has now completed CI successfully:
the Lean formalization workflow and the Python tests both report success for
that exact SHA (the push test and pull-request checks). This confirms the
existing source still builds; it does not turn the conditional boundary
diagnostics into a proof of the p=6 lower-stratum cancellation.

The next source change should wait until the two-N and four-N boundary sums
have been written in one common notation and their coefficients compared
without assuming reversal-pair equality. Adjoint reversal only gives complex
conjugacy in general. In particular, do not collapse a cyclic/reversal orbit
to twice one real trace unless reality of that representative has separately
been proved.

## 4ar. Concrete cyclic-class expressions for the p=6 lower even strata

The exact word inventory fixes the three cyclic representatives and their
multiplicities in each lower even stratum. Let
`T_{a,b} := ∑_{x : g x} (K^a)_{x,x}(K^b)_{σx,σx}`, with the same glued
boundary support and the relevant corner hypotheses as
`trace_two_N_powers_of_BD`. Then the r=2 contribution has the explicit form
`B_{6,2} = 6 T_{1,5} + 6 T_{2,4} + 3 T_{3,3}`.
This follows from the cyclic gap representatives `(0,4)`, `(1,3)`,
`(2,2)`: each KN tile contributes one K before its N, so the intervening
K-power pairs are `(1,5)`, `(2,4)`, and `(3,3)`. Their exact orbit
weights are `6,6,3`, not a uniform factor of six.

For r=4, define `U_{a,b,c,d}` to be the explicit nested boundary sum obtained
from `trace_four_N_powers_explicit` for the cyclic word
`K^a N K^b N K^c N K^d N`, with `a+b+c+d=6` and the four intervening
powers all positive. The three cyclic gap representatives are
`(0,0,0,2)`, `(0,0,1,1)`, and `(0,1,0,1)`, hence the intervening powers
are `(1,1,1,3)`, `(1,1,2,2)`, and `(1,2,1,2)`, with weights `6,6,3`.
Thus
`B_{6,4} = 6 U_{1,1,1,3} + 6 U_{1,1,2,2} + 3 U_{1,2,1,2}`.

These are exact class-weighted reductions, not cancellation identities. The
remaining p=6 question is now term-level: under the concrete axis comparison,
does the difference of these two weighted sums vanish? The r=2 formula is
already a single boundary sum of diagonal power entries; the r=4 formula is a
nested sum with off-diagonal K entries between boundary points. No equality
between individual T and U terms is assumed, and the cyclic census alone gives
no such equality.

## 4as. Kernel-level form of the p=6 four-pairing boundary terms

Expanding the three specializations in `trace_p6_lower_even_strata_boundary`
one level further makes the obstruction more concrete. Write
`d_j(x) := (K^j)_{σ(x),σ(x)}` on the glued locus. The nested sums are

```text
U_{1,1,1,3} = ∑_{x,y glued} K[x,y] K[y,x] d_1(y) d_3(x),
U_{1,1,2,2} = ∑_{x,y glued} K[x,y] (K²)[y,x] d_1(y) d_2(x),
U_{1,2,1,2} = ∑_{x,y glued} K[x,y] K[y,x] d_2(y) d_2(x).
```

Here “x,y glued” means both `G.g x` and `G.g y`; the summands outside
that support are zero. If `K` is Hermitian, then
`K[y,x] = conj(K[x,y])` and `(K²)[y,x] = conj((K²)[x,y])`.
Thus the first and third kernels are weighted by `|K[x,y]|²`, while the
middle term is a mixed kernel
`K[x,y] * conj((K²)[x,y])`. This distinction matters: it is not valid to
replace all three terms by absolute-square sums or to assume they cancel
individually.

This kernel form suggests the next concrete comparison: establish which
boundary-point pairs `(x,y)` have nonzero `K[x,y]` and `(K²)[x,y]` for
the two axis choices, then compare the weighted diagonal factors
`d_1,d_2,d_3` on those pairs. The current Lean lemma proves the nested-sum
identities but does not yet prove that the two operator choices have equal
weighted sums. No cancellation theorem is claimed in this section.

## 4at. CI recovery and the remaining support bridge

Commit `784c987` is now confirmed green on both workflows: Lean formalization and
Python tests. This repairs the p=6 theorem's right-hand side so its three
four-`N` strata match the diagonal forms proved by
`trace_four_N_powers_diagonal_left_one`.

A useful distinction for the next proof step: `sgK_glued_offdiag` proves
only the one-step fact `sgK w w' = 0` for distinct glued states. It does
**not** by itself imply `(sgK ^ n) w w' = 0`: a power can travel through
unglued intermediate states. The abstract p=6 boundary theorem still assumes
the stronger power-by-power condition `hkg` for exponents through 5.

The repository already has the right ingredients for replacing that abstract
assumption in the concrete Sierpinski case:
- `sgK_pow_entry_coord_dist` bounds the coordinate displacement of a nonzero
  entry of `sgK ^ n) by `n`;
- `glued_corner` restricts glued coordinates to `(0,0)`, `(2^m,0)`,
  and `(0,2^m)`;
- `sgK_pow_GlueDiag_of_OAnti` handles same-coordinate, opposite-spin
  entries of every power under `OAnti (m+1) o`.

For `m ≥ 3` and `n ≤ 5`, distinct corner coordinates are separated by
`2^m ≥ 8 > n`, so coordinate support should force the distinct-coordinate
case to vanish. The remaining formalization task is to combine that distance
argument with `sgK_pow_GlueDiag_of_OAnti` (including its partner-coordinate
premise) into a concrete theorem supplying the `hkg` premise. Until that bridge
is proved, the concrete p=6 specialization is not yet discharged from the
abstract boundary formula. No all-level moment recurrence is claimed.

## 4au. Concrete p=6 boundary specializations

The support bridge described in §4at has now been formalized as
`sgK_pow_hkg_up_to_five_of_OAnti` in `GlueCorner.lean`, and both CI
workflows passed for commit `ceedec5`. In `GlueTrace.lean`, theorem
`sg_trace_p6_lower_even_strata_boundary` specializes the abstract lower
even-strata identity to `sgK`/`sgGlue` for `m ≥ 3` under `OAnti`.

The next commit adds the analogous specialization
`sg_trace_p6_top_stratum_boundary`: the six-`N) top stratum is expressed
as `Tr(K D K D K D)`, with `D) the diagonal matrix of partner-corner
values. The top term is retained exactly; it is **not** proved zero.

CI for the new top-stratum specialization is currently running (commit
`c9a9402`). If green, this gives a concrete decomposition of all p=6 even
boundary strata. The remaining mathematical obstacle is comparison between
two axis choices: the lower strata depend on diagonal entries of powers
`K^a), while the top stratum still involves off-diagonal entries of `K)
between glued corners. The existing p=4 recursion hypothesis `hcorner)
only identifies corner diagonals of `K), `K²), and `K³`; it does not by
itself establish equality of `Tr(K D K D K D)` across axis choices. No
p=6 cancellation identity or p=6,8,10 moment recurrence is claimed.

## 4av. Exact target for collapsing the p=6 top stratum

CI is green for both `c9a9402` (the concrete top-stratum specialization)
and `5cf3716` (the research-log update). The new specialization is therefore
checked, not merely queued.

The concrete one-step lemma `sgK_glued_offdiag` is stronger than a
same-copy statement: it says `sgK w w' = 0` whenever both states are glued
and `w ≠ w'`, including states in different copies. Let
`d(x) = if g(x) then K (σ x) (σ x) else 0` and `D = diagonal d`.
Then `D) is supported on glued states, and every off-diagonal matrix entry
of `K) between points in that support vanishes. Expanding the trace gives
the exact candidate identity

```
Tr(K D K D K D)
  = ∑ x, if g x then
      (K x x * K (σ x) (σ x)) *
      (K x x * K (σ x) (σ x)) *
      (K x x * K (σ x) (σ x))
    else 0
```

This is a finite-matrix consequence of support, not an assumption about the
desired moment cancellation. It is the next lemma to formalize. It would
reduce the top stratum to a sum of cubes of the paired corner-diagonal
product, but does **not** alone show equality between two axis choices: one
still needs equality of the paired diagonal products (or a weighted-sum
identity). Keep that comparison as a separate obligation.

## 4aw. Algebraic expansion of the top p=6 boundary term

The CI runs for `963c8ed` completed successfully: Lean formalization and Python
tests are green. The new observation in §4av can be checked directly by
expanding the trace. For `D = diag(d)` with `d(x)=0` off the glued set,
`Tr(K D K D K D)` is the finite sum over triples `x,y,z` of
`K x y * d(y) * K y z * d(z) * K z x * d(x)`.
Every nonzero summand has `g x`, `g y`, and `g z`. The existing
`sgK_glued_offdiag` then forces `x=y=z`: if any adjacent pair differs,
the corresponding K entry vanishes. The surviving summand is
`(K x x * d(x))^3`. With `d(x)=K (σ x) (σ x)` on glued states, this is
the proposed paired-diagonal cube formula.

Formalization note: keep the support condition explicit in the helper lemma;
do not try to use `sgK_glued_offdiag` on indices before proving that the
diagonal factors force those indices to be glued. A clean generic helper
should state both (i) `d x = 0` whenever `¬ g x`, and (ii) off-diagonal
vanishing of K between any two g-supported indices. The concrete theorem can
then discharge these hypotheses using `sgGlue` and `sgK_glued_offdiag`.

This reduction does not settle axis comparison. The resulting sum is
`∑ x, if g x then (K x x * K (σ x) (σ x))^3 else 0`; equality for two axis
choices still requires a separate invariant for these paired diagonal
products. No moment recurrence is claimed here.

## 4ax. Verified CI and an algebraic route to the diagonal collapse

The two workflows for `c23bdff` have now completed successfully. The top
stratum remains the next formal proof target.

A useful way to avoid expanding all six matrix factors at once is to first
prove a support lemma for `D K D). If `D = diagonal d`, `d x = 0` off
the glued set, and `K x y = 0` for distinct glued states, then
`(D * K * D) x y = d x * K x y * d y` is zero whenever `x ≠ y):
if either diagonal coefficient is zero, the product vanishes; otherwise both
indices are glued and the off-diagonal hypothesis applies. Thus `D*K*D`
is diagonal. This is a simpler local target than immediately expanding
`Tr(K D K D K D)).

The remaining trace can then be reduced by associativity and the finite-matrix
identity `trace_mul_comm`, keeping the diagonal support explicit until the
last simplification. This approach is preferable to claiming the cube formula
from a verbal expansion: the Lean proof must still justify the finite sums
and the collapse of every off-diagonal term.

No source theorem was added in this step; this entry records the checked
algebraic route for the next Lean lemma. The axis-comparison identity and the
moment recurrence remain open.

## 4ay. The trace-collapse step needs support as well as diagonality

The concrete sandwich lemmas in `GlueAlg.lean` and `GlueTrace.lean`
now pass Lean CI (commit `d0689e0`). The next identity should be proved with
the support condition kept explicit, rather than inferred from diagonality
alone.

Let (D=\operatorname{diag}(d)), where (d_x=0) off (g), and assume
(K_{xy}=0) whenever (x,y\in g) and (x\ne y). Then the trace expansion
is
[
\operatorname{Tr}(KDKDKD)
=\sum_{x,y,z}K_{xy}d_yK_{yz}d_zK_{zx}d_x.
]
A nonzero term forces (x,y,z\in g) by the three diagonal weights. The
off-diagonal hypothesis then forces (x=y=z), so the sum reduces to
[
\sum_{x\in g}(K_{xx}d_x)^3.
]
This direct finite-sum proof is the intended next theorem. It uses both
support and boundary off-diagonal vanishing; the already proved statement
that (DKD) is diagonal is a useful intermediate lemma but is not by itself
the whole trace argument.

The specialized choice (d_x=K_{\sigma(x),\sigma(x)}) gives the paired
diagonal cube sum. Its invariance under changing the axis is still a separate
claim and is not implied by this trace reduction.

## 4az. Correct factorization for the p=6 top trace

The concrete specialization `sg_trace_p6_top_stratum_cube` is now green in
Lean CI (commit `b4bc08a`). Its conclusion is only
`Tr(K D K D K D) = Tr((K D)^3)`; this is a reassociation identity and does
not evaluate the trace.

For the next reduction, let (D=\operatorname{diag}(d)), with (d_x=0)
outside the glued locus (g), and assume (K_{xy}=0) for distinct (x,y)
both in (g). The already formalized sandwich statement says
(A=DKD) is diagonal. By cyclicity and associativity,
[
\operatorname{Tr}(KDKDKD)=\operatorname{Tr}(K(DKD)KD)
=\operatorname{Tr}(KAKD).
]
Expanding the latter trace gives the two-index kernel
[
\sum_{x,y} K_{xy} A_{yy} K_{yx} d_x.
]
Since (A_{yy}=d_y K_{yy} d_y), its support forces (y\in g), and
(d_x) forces (x\in g). The glued-locus off-diagonal hypothesis then
forces (x=y). The desired collapse is therefore
[
\sum_{x\in g} K_{xx}^3 d_x^3
=\sum_{x\in g}(K_{xx}d_x)^3.
]
This derivation makes the exact remaining formalization target clear: a
generic finite-matrix lemma for `Tr(K * A * K * D)` when `A,D` are
diagonal, with support and restricted off-diagonal hypotheses explicit.
Only after that generic lemma passes CI should it be specialized to `sgK`.
No axis-invariance or moment recurrence is claimed by this reduction.

## 4ba. CI restored; sharpened next proof obligation (2026-10-24)

Commit `dc319ed` removes the unverified generic diagonal-cube lemma. Both
Lean formalization and Python tests pass on that commit. Do not reintroduce
the removed proof without compiling it in the project environment.

The existing concrete fact is stronger than a mere hope but narrower than
the desired trace evaluation:
`sgK_corner_sandwich_eq_diagonal` proves that (A=D K D) is diagonal,
where (D=\operatorname{diag}(d)) and (d) is supported on the glued locus.
It does **not** imply that (KD) is diagonal: entries (K_{xy}d_y) with
(x\notin g, y\in g) are not covered by `sgK_glued_offdiag`.

A safe route for the top trace is the cyclic regrouping
[
\operatorname{Tr}(KDKDKD)=\operatorname{Tr}(K(DKD)KD)
=\operatorname{Tr}(KAKD).
]
Since (A=DKD) is diagonal, expand the trace into a two-index sum:
[
\sum_{x,y} K_{xy} A_{yy} K_{yx} d_x.
]
The supports of (A_{yy}) and (d_x) force (x,y\in g). Only then may
`sgK_glued_offdiag` be applied to conclude that nonzero terms have (x=y).
This yields (sum_{x\in g}K_{xx}^2 A_{xx}d_x), and using
(A_{xx}=d_xK_{xx}d_x) gives (sum_{x\in g}(K_{xx}d_x)^3).

The next formalization should isolate precisely this two-index trace lemma,
not claim that (KD) is diagonal and not repeat the earlier failed
three-diagonal-product proof. Require CI to pass before specializing it to
`sgK`. Axis invariance remains an independent open obligation.

## 4bb. Exact level-3 test rules out unrestricted axis-pattern equality (2026-10-24)

A separate exact-arithmetic diagnostic was run against the definitions in
`src/graph/sg_graph.py` and `src/operators/operators.py`, at level 3 and
`theta = pi`. At this parameter, each flux rotation is exactly
`-i * sigma_axis`, so the resulting matrix has Gaussian-integer entries.
The calculation used integer real/imaginary matrix multiplication, not
floating-point powers.

For the repository's two documented configurations, the full operator traces
are:

| power p | cycling axes x/y/z (`commuting=False`) | common z axis (`commuting=True`) |
|---:|---:|---:|
| 4 | 52,572 | 52,732 |
| 6 | 2,080,992 | 2,120,640 |
| 8 | 89,944,892 | 93,788,476 |
| 10 | 4,082,500,316 | 4,362,907,356 |

Thus these two configurations do not have equal full spectral moments at
this level and parameter. This is a counterexample to any *unrestricted*
claim that the cycling-axis and common-axis operators have identical moments;
it is not a counterexample to gauge invariance, and it does not settle any
more narrowly stated comparison between particular axis assignments or
glued-boundary contributions. In particular, do not try to prove equality
between these two configurations from the corner-diagonal reduction alone.
First state precisely which axis choices are being compared and verify that
the desired equality is actually true for that comparison.

This is a diagnostic entry only. No Lean theorem is inferred from the
calculation, and no moment recurrence is claimed.


## 4bc. Precise algebraic target for the p=6 top-stratum collapse (2026-10-24)

The next proof obligation is now stated as a concrete finite-matrix identity, not as an axis-invariance assertion. Let D = diag(d), with d_x = 0 off the glued set g, and assume K_xy = 0 whenever x,y are in g and x != y. The desired intermediate identity is

$$
\operatorname{Tr}(KDKDKD) = \sum_{x\in g}(K_{xx}d_x)^3.
$$

The safe factorization is KDKDKD = K(DKD)KD, with associativity understood. The existing lemma diagonal_sandwich_offdiag_zero proves that A = DKD is diagonal, and trace_diagonal_sandwich_eq_sum evaluates its trace. To finish the displayed identity one must still expand Tr(KAKD) into a two-index sum and use support of both A and D to force both indices into g, where the off-diagonal hypothesis on K applies. It is invalid to infer that KD itself is diagonal from the current hypotheses.

This note is a proof plan, not a Lean theorem. No axis-invariance statement follows from this identity alone: the resulting sum still depends on the diagonal entries of the particular operator. The next code change should add and compile the two-index trace lemma before specializing it to the concrete sgK operator.


## 4bd. Support-sensitive p=6 top-stratum collapse (2026-10-25)

The current PR branch now contains the Lean theorem
`sg_trace_p6_top_stratum_diagonal_cube` in
`formalization/EvgenyTheorem/GlueTrace.lean`. It combines the already proved
boundary regrouping with the two-index trace-collapse lemma. The support
conditions are explicit: both diagonal weights vanish off the glued locus,
and `sgK_glued_offdiag` is used only after both summation indices have been
shown to lie in that locus. The result is the exact finite-level identity

$$
\operatorname{Tr}(K N K N K N K N K N K N)
= \sum_{x\in g}
  \left(K_{xx}K_{\sigma(x),\sigma(x)}\right)^3,
$$

under the theorem's stated `OAnti (m + 1) o` hypothesis and the concrete
definitions of `K`, `N`, `g`, and `σ`.

**Verified CI for commit `2ac025af202c5a9e0986e0ee8b6591a7b3c014c8`:**
the Lean `Build formalization` job passed, and both Python 3.11 and 3.12
jobs passed their fast and slow tests. This verifies compilation and the
repository's test suite for that exact commit. The subsequent documentation
commit, if any, must be checked separately.

This closes the specific finite-matrix reduction for the p=6 top boundary
trace. It does **not** show that the displayed sum is independent of the axis
assignment, does not cancel the other even-`r` strata, and does not prove
`R_m^(p)=R_4^(p)` for all levels or angles. The next mathematical obligation
remains a justified comparison/cancellation of the explicit even-stratum
boundary sums, followed by a proof of the finite base transition and the
level-propagation step. Numerical agreement at θ=π remains finite exact
evidence only.
