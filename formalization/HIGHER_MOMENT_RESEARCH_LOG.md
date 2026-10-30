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


## 4be. Correct recurrence target for the higher-moment boundary sum (2026-10-25)

A correction to the wording in §4aa is necessary. The phrase
`F_p(ax) = F_p(ax')` is too strong for the observed higher-moment recurrence
and must not be used as the proof target without an additional theorem showing
that the relevant boundary correction cancels completely. The exact
`theta = pi` data give nonzero stabilized residuals
`R_6 = 5280`, `R_8 = 277504`, and `R_10 = 4507520`; hence the total
boundary contribution to the defect recurrence is not zero in those cases.

The correct target should be formulated from the actual expansion of the
defect recurrence. If `F_{p,m}(ax)` denotes the fully weighted sum of the
even-stratum boundary terms at level `m`, the required statement is that the
**difference for the two specified operator/axis configurations** gives the
moment residual:
`F_{p,m}(ax) - F_{p,m}(ax') = R_p(theta)`,
with the appropriate level indexing verified against the expansion. For the
conjectured stabilization, one must additionally prove that this difference
is independent of `m` from the claimed starting level. This is a target
statement, not yet a theorem: the exact finite values at `theta = pi` do not
determine the all-angle function `R_p(theta)`.

Accordingly, the top-stratum reduction in §4bd is only one component of the
calculation. Its trace is reduced to an explicit diagonal sum and is not
claimed to vanish. The remaining task is to assemble every even-stratum
contribution with the correct cyclic-orbit weights, subtract the two
specified configurations, and prove the resulting level transition. Do not
infer the recurrence by asserting separate vanishing or axis-independence of
each even stratum.

## 4bf. Audit after reverting the uncompiled paired-corner lemma (2026-10-27)

**Repository state.** The speculative lemma `sg_paired_corner_sum_swap` was removed by reverting the uncompiled change. The current branch head is `70a91c60a2ceb33a03dcdc1a2a3bda8abdeb11c1`; `GlueTrace.lean` is restored to the previously verified source (blob `3965e79d8829694efe9cfe8fd6ed7ce719032896`). The Lean formalization workflow and the Python 3.11/3.12 test workflows passed for that revert commit. This validates the restored baseline only; it does not prove the higher-moment recurrence.

**What is already proved for p=6.** The current source has:
- `sg_trace_p6_lower_even_strata_boundary`: the three r=2 boundary classes and their exact weights (6,6,3), reduced to explicit paired-corner sums;
- `sg_trace_p6_top_stratum_boundary` and `sg_trace_p6_top_stratum_diagonal_cube`: the r=6/top-stratum trace is reduced to the paired diagonal cube sum under explicit support and glued-off-diagonal hypotheses;
- `sg_trace_p6_all_even_strata_boundary`: assembles the lower r=2 and r=4 contributions plus the r=6 top contribution in one equation;
- `glued_sum_partner_product_swap` in `GlueAlg.lean`: a verified involution-based finite-sum identity on the glued subtype. This is the existing correct helper for swapping partner-indexed products; do not duplicate it using an unverified permutation constructor.

**Exact gap before the next Lean edit.** The boundary equation is an expansion, not a cancellation theorem. The next task is to write down, outside Lean first, the fully weighted difference between the *two precisely named operator/axis configurations* for the p=6 boundary expression. The derivation must preserve all three lower-stratum weights (6,6,3), all three r=4 weights (6,6,3), and the r=6 term; it must state which diagonal powers or paired products are claimed to match under the partner involution, and prove those equalities from actual operator hypotheses. Do not assume unrestricted axis independence: the exact level-3 trace diagnostic in §4bb disproves that broader claim for cycling x/y/z versus common z.

**Next action sequence.**
1. Inspect the definitions of the two intended configurations and confirm the exact target difference against the defect recurrence; if the configurations are not specified unambiguously in source/research notes, stop and resolve that before coding.
2. Build a symbolic term ledger for the p=6 expression with columns: canonical gap tuple/class, orbit weight, explicit corner expression, corresponding term for the second configuration, and the exact lemma/hypothesis needed to equate or subtract them.
3. Use `glued_sum_partner_product_swap` only where the summands really have the required (f(x)h(σx)) form; it cannot by itself prove equality of axis-dependent factors.
4. Only after the ledger algebraically reduces to the required residual, formalize the smallest missing identity. Run Lean CI and both Python jobs; keep the source unchanged if the proposed identity cannot be justified.

**Status:** no new mathematical theorem is claimed by this entry. The next step is the exact p=6 weighted comparison/term ledger, not another speculative symmetry lemma and not a heartbeat increase.

## 4bg. Concrete p=6 term ledger after source re-check (2026-10-27)

The source theorem `sg_trace_p6_all_even_strata_boundary` was re-read against its exact right-hand side. The boundary expression has seven contributions; the ledger below records the coefficients and the corresponding kernel form. This is an expansion ledger, not a claim that corresponding terms in two configurations are equal.

| Stratum | Ordered gap pattern represented in the source | Weight | Explicit contribution on the glued locus |
|---|---|---:|---|
| (r=2) | ((1,5,0)) | 6 | (sum_x K_{xx}(K^5)_{sigma x,sigma x}) |
| (r=2) | ((2,4,0)) | 6 | (sum_x (K^2)_{xx}(K^4)_{sigma x,sigma x}) |
| (r=2) | ((3,3,0)) | 3 | (sum_x (K^3)_{xx}(K^3)_{sigma x,sigma x}) |
| (r=4) | ((1,1,1,3)) | 6 | (sum_x K_{xx} d_1(x) K_{xx} d_3(x)) |
| (r=4) | ((1,1,2,2)) | 6 | (sum_x K_{xx} d_1(x) (K^2)_{xx} d_2(x)) |
| (r=4) | ((1,2,1,2)) | 3 | (sum_x K_{xx} d_2(x) K_{xx} d_2(x)) |
| (r=6) | ((1,1,1,1,1,1)) | 1 | (tr(K D K D K D), D_{xx}=1_{g(x)}(K)_{sigma x,sigma x}) |

Here (d_j(x)=(K^j)_{sigma x,sigma x}) on glued points. The r=2 and r=4 terms are single sums over x; the r=6 term in sg_trace_p6_all_even_strata_boundary is a diagonal-sandwich trace, not automatically a sum of diagonal cubes. The actual Lean theorem encodes support using `if G.g x then ... else 0`. Gap-pattern labels are the canonical classes represented by the existing source specializations; cyclic-word multiplicities remain those in the machine-readable inventory/ledger.

**Important correction to the immediate next step:** the source defines a generic axis function `ax : ℕ → Axis`, but the current theorem statement alone does not identify a unique pair `ax, ax'` whose boundary difference is the target residual. The log's previous instructions to compare “the two specified configurations” cannot be executed safely until the intended pair is pinned to the exact operator definitions and recurrence. The known pair `commuting=False` (cycling x/y/z) versus `commuting=True` (common z) is explicitly ruled out as an unrestricted moment-equality target by §4bb; do not silently substitute that pair.

**Next action:** trace the definition of the defect/target recurrence back to the exact operators and record the two configurations and level indexing. Then duplicate the ledger columns for the second configuration and derive the *difference* term by term. If no source definition determines the pair, keep this as a documented blocking mathematical specification rather than inventing a target theorem. No Lean source theorem was added in this step.

## 4bh. Correction: the intended comparison pair is identifiable in source (2026-10-27)

The source re-check resolves the configuration-specification question raised in §4bg. The intended pair is explicitly defined by `THEOREM.md` and the operator builder:
- (C): `commuting=False`, axis `i % 3` (cycling x/y/z by face index);
- (C'): `commuting=True`, fixed z axis (axis index 2);
- in Lean's p=4 defect notation, this is `ax = faceAxis` and `ax' = fun _ => 2`, with the numbering orientation `oNum` / `fun p q => vIdx m p ≤ vIdx m q`, as stated by `traceDefect_eq_defectO`.

Therefore the pair itself is not unspecified. The real open obligation is more precise: the existing p=6 boundary expansion is parameterized by one `ax` at a time. The proof must instantiate it separately at `faceAxis` and `fun _ => 2`, subtract the two fully weighted expressions, and then prove that this difference equals the p=6 defect residual with the correct level indexing. It must not try to prove that either the full moments or each individual stratum is equal between (C) and (C'); §4bb explicitly rules out that stronger claim.

For level propagation, the existing `defectO_succ` is a fourth-moment theorem and cannot be reused as a p=6 recurrence without a new p=6 splitting proof. Its orientation recursion identifies the relevant sub-orientations `oBo m o` and `oCo m o`; the p=6 argument must track those same branches and their weights rather than infer a recurrence from the boundary ledger alone.

**Revised next action:** construct both sides of the p=6 boundary difference using the exact (C,C') pair above; reduce their difference algebraically to the residual target; then separately prove the level transition. The p=6 term ledger in §4bg remains a single-configuration ledger and must be duplicated with (K_C) and (K_{C'}) labels before any equality or cancellation claim. No Lean code was changed.

## 4bi. Paired symbolic form of the p=6 boundary difference (corrected 2026-10-27)

Set \(K_C := \mathrm{sgK}(m,\theta,\mathrm{faceAxis},o)\) and \(K_{C'} := \mathrm{sgK}(m,\theta,\mathrm{fun}\ \_ \mapsto 2,o)\). For \(Q\in\{C,C'\}\), define
\(a_{j,Q}(x):=(K_Q^j)_{xx}\) and \(d_{j,Q}(x):=(K_Q^j)_{\sigma x,\sigma x}\) on glued points. Re-reading the exact RHS of \`sg_trace_p6_all_even_strata_boundary\` shows that the r=4 contributions are **single sums over x**, not double sums over x,y. The paired difference of the two boundary expressions is therefore:

    B6(m) =
      6 Σ_x [a_1,C(x) d_5,C(x) - a_1,C'(x) d_5,C'(x)]
    + 6 Σ_x [a_2,C(x) d_4,C(x) - a_2,C'(x) d_4,C'(x)]
    + 3 Σ_x [a_3,C(x) d_3,C(x) - a_3,C'(x) d_3,C'(x)]
    + 6 Σ_x [a_1,C(x) d_1,C(x) a_1,C(x) d_3,C(x)
             - a_1,C'(x) d_1,C'(x) a_1,C'(x) d_3,C'(x)]
    + 6 Σ_x [a_1,C(x) d_1,C(x) a_2,C(x) d_2,C(x)
             - a_1,C'(x) d_1,C'(x) a_2,C'(x) d_2,C'(x)]
    + 3 Σ_x [a_1,C(x) d_2,C(x) a_1,C(x) d_2,C(x)
             - a_1,C'(x) d_2,C'(x) a_1,C'(x) d_2,C'(x)]
    + Σ_x [(a_1,C(x) d_1,C(x))³ - (a_1,C'(x) d_1,C'(x))³].

The r=6 term in the original theorem is the diagonal-sandwich trace
\(\operatorname{tr}(K D K D K D)\), with \(D_{xx}=d_{1,Q}(x)\) on glued points and zero elsewhere; the final sum shown above is its further diagonal-cube specialization only when the separate hypotheses of \`sg_trace_p6_top_stratum_diagonal_cube\` are available. Thus the paired formula is to be used with the exact theorem/hypotheses actually invoked, not by silently replacing the sandwich trace.

**Correction to the previous draft:** the earlier version incorrectly wrote the r=4 terms as double sums with off-diagonal entries \(K_{xy}K_{yx}\) and \(K_{xy}(K^2)_{yx}\). Those terms do not match the checked Lean theorem's RHS. The corrected expressions above mirror its single-index diagonal products. No cross-configuration cancellation is asserted.

**Proof gate before Lean:** independently derive from the p=6 trace splitting whether this paired boundary difference equals \(\Delta_m^{(6)}-3\Delta_{m-1}^{(6)}\), or whether additional orientation/subcopy terms remain. The p=4 theorem \`defectO_succ\` does not settle this. No new Lean theorem or cancellation is claimed.

## 4bj. Full audit of the latest p=6 ledger correction (2026-10-27)

I compared the literal RHS of sg_trace_p6_all_even_strata_boundary (GlueTrace.lean, lines 379–412) with the research ledger. The earlier §4bg/first §4bi draft was wrong in two places: it described the r=4 terms as double sums over off-diagonal entries, and it presented the r=6 term as a diagonal-cube sum without preserving the theorem's exact hypotheses. These were documentation errors, not Lean source changes. §4bg and §4bi have now been corrected to match the source: r=4 are single-index diagonal products; the unified theorem's r=6 term is tr(K D K D K D). The diagonal-cube form is available only through the separate specialization theorem and its hypotheses.

The latest code-bearing commit before these log-only corrections, 2beebb80c4db4ff0e996d42c28747d3196138331, has confirmed green CI:
- Lean formalization run 40405788009: success.
- Python tests run 40405788047: success, both Python 3.11 and 3.12 jobs passed.

The correction-only commit is 605bce8cdbc04fe5473efd1cd1827cdf531d83b2; its Lean workflow is currently in progress and its Python workflow is queued as of this entry. Do not call that commit green until both workflows finish.

**Next mathematical step (no speculative lemma):** prove or refute the missing bridge between the exact p=6 trace split and the paired boundary expression. First locate/derive a p=6 analogue of the p=4 recursive split defectO_succ; do not infer it from sg_trace_p6_all_even_strata_boundary, because that theorem only expands a chosen stratum sum for one operator and one orientation. The bridge must track the three recursive subcopies/orientations oBo m o, oCo m o, plus the correct level-indexed defects. Only if this bridge is established should the axis-difference and residual-stabilization claims be attempted. Until then, keep the p=6, p=8, p=10 stabilization statements explicitly conjectural and make no Lean-code edit.

## 4bk. Re-audit: the exact missing p=6 gluing theorem (2026-10-27)

This entry records a source-level check against the current PR head \`1cdc4bbe77cb7a5beaec7b6cf93318cbae90044b\`. Its CI is green: Lean formalization run \`40408426515\` passed; Python test run \`40408426538\` passed for both 3.11 and 3.12. No Lean source was changed in this audit.

### What is already in place

- \`trace_orderedWordExpansion\` in \`TraceExpand.lean\` gives the exact ordered trace expansion of \((A+B)^p\), preserving all \(2^p\) words and multiplicities. For \(p=6\), this supplies a trustworthy algebraic expansion engine; it does not by itself identify the glued-operator summands.
- \`trace_blockK_pow\` is already general in the power \(n\): the trace of a copy-block-diagonal power is the sum of the three corresponding copy traces.
- The p=6 concrete even-stratum reductions are present in \`GlueTrace.lean\`: r=2 and r=4 have exact weighted boundary sums (weights \(6,6,3\)); r=6 is an exact diagonal-sandwich trace. The odd strata r=1,3,5 have conditional vanishing reductions under the stated \`OAnti\` and corner hypotheses. These facts classify/reduce the words after they are known to occur in the glued trace expansion.
- \`pOpO_trace4_glue_final\` in \`GlueCorner.lean\` is the only concrete gluing trace theorem currently found. It is explicitly fourth-degree and returns \`glueRHS\`/\`cornerTerm\`; it cannot be applied at degree six.

### Exact missing milestone

The missing theorem is a degree-six gluing identity, schematically:

\`\`\`text
trace (pOpO (m+1) ^ 6)
  = sum over c : GCopy, trace (Hc m c ^ 6)
    + B6(m, ax, o)
\`\`\`

where \`B6\` must be the *fully ordered and multiplicity-weighted* sum of the r=2,4,6 terms, with r=6 retained as the sandwich trace unless its separate diagonal-collapse hypotheses are explicitly proved. The identity must also state the exact hypotheses on the axis periodicity and orientation, analogous to those of \`pOpO_trace4_glue_final\`.

This is the immediate algebraic bridge—not a claim that \(B_6\) cancels. Once this identity is proved, subtract its instantiation at \`faceAxis\` and at \`fun _ => 2\`. The copy sum then becomes the three subcopy defects with orientations \`o\`, \`oBo m o\`, and \`oCo m o\`. Only after this exact equation is in hand can the axis-difference of \(B_6\) be identified with the level residual and its stabilization studied.

### Deliberate proof order

1. Work in \`GlueCorner.lean\` to expose the degree-six glued trace as an ordered word sum. Reuse \`trace_orderedWordExpansion\`; do not change \`trace_blockK_pow\`.
2. Establish the word-to-glued-boundary correspondence with exact cyclic orbit multiplicities. Use the existing r=2,3,4,5,6 reductions; preserve the r=6 sandwich form.
3. Prove the copy-block term is exactly the three copy sixth-moment traces.
4. Package the result as the p=6 gluing identity, then instantiate for the two axis choices and subtract.
5. Record and prove any further cancellation as a separate theorem with explicit geometric hypotheses. Do not assert termwise axis independence or derive it from the word inventory.

The current research log's §4bj statement that the p=6 recursive bridge is missing is therefore confirmed, and is sharpened here: the next theorem should be the degree-six analogue of \`pOpO_trace4_glue_final\` in \`GlueCorner.lean\`, not a new corner-symmetry lemma in \`GlueTrace.lean\`. The higher-moment stabilization remains conjectural until the subsequent boundary-difference and level-transition arguments are proved.

## 4bl. Correction after inspecting the full pushforward bridge (2026-10-27)

A further source audit found that §4bk was too coarse in calling the entire p=6 glued trace identity absent. The exact positive-power pushforward/word bridge is **already proved**:

- \`trace_push_power\` and \`trace_push_ordered_words\` in \`GlueBridge.lean\`;
- concrete specialization \`pOpO_succ_trace_ordered_words\` in \`GlueK.lean\`.

For every positive p these give
\[
\operatorname{tr}(pOpO(m+1)^p)
=\sum_{w\in\operatorname{orderedWordExpansion}(K,K\,N,p)}
\operatorname{tr}(w),
\]
preserving word order and multiplicity. The generic algebraic bridge is not the missing theorem. Likewise, \`trace_blockK_pow\` already handles the three-copy trace for any p.

**Precisely narrowed next target:** at p=6, combine the existing ordered-word equality with the already proved word-stratum reductions and the needed odd-stratum zero results, then package the resulting equality as a trace split:
\[
\operatorname{tr}(pOpO(m+1)^6)
=\sum_{c:GCopy}\operatorname{tr}(H_c(m)^6)+\mathcal B_6(m,\mathrm{ax},o).
\]
Here \(\mathcal B_6\) is exactly the full even-stratum correction, with its r=6 diagonal-sandwich trace retained. This package must be proved by matching the actual ordered-word list and its cyclic multiplicities—not by assuming cancellation. Afterward instantiate at the two axis choices and subtract; only then can the subcopy defect terms be separated from the difference of boundary corrections.

This corrects the emphasis of §4bk: do not write a second generic pushforward theorem or change \`trace_orderedWordExpansion\`; focus on the concrete p=6 assembly theorem and verify every omitted odd stratum under the precise current hypotheses. The proposed split is still a proof target, not a theorem already established.

### CI recheck

The research-log-only commit \`bf6bf64d4bce448f3fc87308d95ee7c94f3dbf9a\` has completed both workflows successfully: Lean formalization passed, and Python tests passed (3.11 and 3.12). This green result validates the current source/log commit; it does not validate the unproved p=6 assembly target above.

## 4bm. Third source audit: distinguish the existing p=6 boundary theorem from the full trace assembly (2026-10-27)

I rechecked the current branch source after §4bl and searched for a degree-six gluing/split declaration. No \`pOpO_trace6_glue_final\`, \`trace6_split\`, or full p=6 assembly theorem is present. The following distinction is now explicit:

1. \`sg_trace_p6_all_even_strata_boundary\` in \`GlueTrace.lean\` **already exists**. Its LHS is precisely the sum of the seven even-stratum trace terms (three r=2, three r=4, one r=6), and its RHS is the exact weighted boundary formula. It is a boundary-reduction theorem for the concrete \`sgK\` operator under \`OAnti (m+1) o\`; it is not the expansion of the complete glued sixth moment.
2. \`pOpO_succ_trace_ordered_words\` in \`GlueK.lean\` and \`trace_push_ordered_words\` in \`GlueBridge.lean\` already express the full sixth moment as the trace-sum over the 64-element ordered list \`orderedWordExpansion K (K*N) 6\`.
3. \`trace_blockK_pow\` already gives the three-copy contribution at degree six.
4. The unresolved join is finite and specific: establish that the ordered-list trace-sum, after cyclic grouping, is exactly the K^6 term (r=0), the seven even terms consumed by \`sg_trace_p6_all_even_strata_boundary\`, and zero odd strata r=1,3,5 under their *actual* hypotheses. This must account for 64 words, 14 cyclic classes, and exact orbit weights; do not simply equate the list sum with the boundary RHS.

### Correct immediate proof target

Do not write another abstract trace-push theorem or another p=6 boundary lemma. First prove a small finite **p=6 ordered-list-to-strata partition lemma** for the exact recursive list definition. The proof should:
- classify each word by its number r of \`K*N\` factors;
- choose cyclic representatives and prove the orbit multiplicities (including non-full orbits);
- use \`trace_cyclic_list\` to justify rotating words without reordering their matrix factors;
- route the r=1,3,5 representatives through the corresponding zero lemmas only after discharging their stated corner/anti-orientation premises;
- route r=2,4,6 representatives through the already proved stratum formulas, preserving the r=6 sandwich trace;
- leave the r=0 term as \`trace (K^6)\`.

Then combine this partition lemma with \`pOpO_succ_trace_ordered_words\`, \`trace_blockK_pow\`, and \`sg_trace_p6_all_even_strata_boundary\` to state the concrete degree-six split. Only the resulting exact equation may be used for the two-axis subtraction. Boundary cancellation and level stabilization remain separate open proof obligations.

No Lean source changed during this audit. The verified CI state is commit \`4cd195ed72c5b3a8dd03c28100a6e09f0586687c\`: Lean succeeded; Python 3.11 and 3.12 succeeded. This confirms the repository baseline, not the new partition lemma, which is not yet implemented.

## 4bn. CI confirmation and proof-scope check (2026-10-27)

The audit commit \`c2e9cb456317ed71e3ee2a1fa8d4f5dacc4ba9f3\` has now completed both CI workflows successfully:
- Lean formalization run \`40446050874\`, build job succeeded.
- Python tests run \`40446050905\`, both Python 3.11 and 3.12 jobs succeeded.

This confirms the branch is still green after the §4bm research-log correction. It does not prove the ordered-list-to-strata partition lemma, which is still absent from Lean source.

A further source check confirms the safe boundary of the next implementation: the existing generic theorem \`trace_p6_lower_even_strata_boundary\` already handles the six r=2/r=4 trace representatives and their weights \(6,6,3\); \`sg_trace_p6_top_stratum_boundary\` handles the single r=6 word while preserving its diagonal-sandwich trace. Thus the p=6 finite assembly should not reprove these local formulas. The remaining code should handle the 64-list partition, cyclic rotations, and the odd-stratum hypotheses, then invoke these established reductions. Keep the full trace split and its two-axis difference as explicit theorem targets; no stabilization conclusion follows from this CI or inventory.

No Lean source changed in this pass. Next action remains to implement a proof-carrying finite partition of \`orderedWordExpansion ... 6\` (not merely cite the Python inventory), with orbit-size proof for periodic classes and exact connection to Lean's recursive list.


## 4bo. Independent p=6 cyclic-orbit census before the Lean partition (2026-10-27)

This is a finite combinatorial audit for the next proof target in §4bn. It is **not** a Lean theorem and does not establish any trace-stratum vanishing.

### Convention and calculation

Encode a choice in the recursive `orderedWordExpansion` by `0 = K` and `1 = K*N`. The recursion appends each choice on the right, so a length-six choice string records the order of the six factors. For each of the (2^6=64) strings, take the lexicographically least cyclic rotation as its representative. The coefficient of a representative in the cyclically grouped trace sum is the size of its rotation orbit. This uses only `trace_cyclic_list`; it does not commute or reorder matrix factors.

The full exhaustive census is:

| (r) (# of `K*N` choices) | Canonical representative | Orbit size / coefficient |
|---:|:---:|---:|
| 0 | `000000` | 1 |
| 1 | `000001` | 6 |
| 2 | `000011` | 6 |
| 2 | `000101` | 6 |
| 2 | `001001` | 3 |
| 3 | `000111` | 6 |
| 3 | `001011` | 6 |
| 3 | `001101` | 6 |
| 3 | `010101` | 2 |
| 4 | `001111` | 6 |
| 4 | `010111` | 6 |
| 4 | `011011` | 3 |
| 5 | `011111` | 6 |
| 6 | `111111` | 1 |

The orbit sizes sum by (r=0,ldots,6) to (1,6,15,20,15,6,1), respectively, exactly (inom 6r); their grand total is 64. There are 14 cyclic classes. The non-full orbits are precisely `001001` (period 3, (r=2)), `010101` (period 2, (r=3)), and `011011` (period 3, (r=4)); their coefficients are 3, 2, and 3, not 6.

### What this does and does not justify

- This table fixes the exact class representatives and multiplicities for the binary *choice words* in the six-step expansion.
- It does not yet prove that the recursive Lean matrix list has been partitioned by this census. The Lean proof must connect the choice-word encoding to `orderedWordExpansion` and establish each rotation relation with `trace_cyclic_list`.
- It does not make the (r=1,3,5) trace classes vanish. Their existing zero reductions can only be used after their hypotheses are proved for the actual representative.
- It does not replace the established (r=2,4,6) boundary reductions, nor does it prove the complete p=6 trace split or axis cancellation.

**Next code milestone:** formalize the finite choice-word/cyclic-orbit partition for this exact length-six recursion, with the above orbit sizes proved in Lean. Then combine it with the existing ordered-word trace equality and the established stratum lemmas. No further boundary cancellation or stabilization claim is licensed before that assembly theorem compiles.



## 4bp. Exact CI verification after the p=6 orbit inventory (2026-10-27)

Checked the workflows for the exact current head `abba363008e2234fc8cd458ddb134d72822f9a9d`, not an earlier green commit:

- Lean formalization run `40455615095`: job `build` passed; the `Build formalization` step completed successfully.
- Tests run `40455615167`: both `test (3.11)` and `test (3.12)` passed. In both jobs, `Fast tests` and `Slow tests (level 7 convergence)` completed successfully.

This validates the repository state at that SHA; it does not validate the absent p=6 ordered-list/cyclic-class Lean assembly. No source-level p=6 assembly theorem has been added in this verification pass.

### Immediate implementation target

Do not expand the existing boundary lemmas. First establish, for the actual recursive `orderedWordExpansion A B 6`, a finite trace-sum identity that groups the 64 ordered terms into the 14 cyclic representatives from §4bo, with the exact orbit weights. The proof must preserve matrix-factor order and use `trace_cyclic_list` only for cyclic rotations. Then connect each representative to the corresponding odd/even stratum theorem, discharging its hypotheses before invoking it. Keep the raw r=0 trace and the r=6 diagonal-sandwich trace explicit.

The current environment has no local `lean`/`lake` executable. Therefore any source edit must be narrowly scoped and its correctness confirmed by the actual PR workflow before the next edit; do not treat this CI audit as a substitute for that compilation.


## 4bq. CI recheck at the journal-update head (2026-10-27)

Re-read PR #9 metadata and the branch ref before proceeding. The PR remains open and mergeable; the exact head at the start of this check was `d3a96467cd9a2221c2c5d7afb96d808549820954`.

For this SHA, the workflows have completed successfully:
- Lean formalization run `40457242351`, build job `122033306533`: success.
- Tests run `40457242189`: Python 3.12 job `122033305924` and Python 3.11 job `122033306150`: success. Both jobs completed their fast and slow level-7 convergence tests.

This independently confirms the previous journal note's audit is not stale: the journal-only commit itself also passed Lean and both Python versions. This is baseline verification only; no new p=6 assembly theorem was validated.

### Proof strategy checkpoint

The next proof must be chosen from the exact current Lean source and research ledger—not from the Python word inventory alone. In particular:
1. Inspect existing representative lemmas in `GlueTrace.lean` and all prerequisites in `GlueK.lean` / `GlueBridge.lean`.
2. Select the smallest missing lemma that advances the aggregate p=6 ordered expansion, not another already-covered boundary case.
3. Work out its statement and matrix-word order explicitly; verify all multiplicity coefficients, especially periodic cyclic orbits.
4. Make one source change only after that audit. Require the actual Lean build and both Python jobs to pass before moving to the next obligation.

No Lean source was changed in this checkpoint. The current p=6 milestone remains the ordered-list-to-cyclic-strata assembly and the discharge of odd-stratum premises; CI success by itself does not close it.


### p=6 odd-stratum reduction lemmas (2026-10-27)

Two additional source-level reductions have now been added to `GlueTrace.lean` on the existing PR #9 branch:

- `sg_trace_p6_three_N_word_zero`: for a p=6 word with three `N` insertions, the middle `K^b` run is strictly below six; the proof applies `trace_three_N_powers` and the existing `sgK_pow_hkg_up_to_five_of_OAnti` support theorem.
- `sg_trace_p6_five_N_word_zero`: for five `N` insertions, both selected runs `K^b` and `K^d` are below six; the proof applies `trace_five_N_powers_zero` with the same geometric support theorem.

The earlier one-`N` class lemma is `sg_trace_p6_one_N_class_zero`. These are word-level vanishing reductions, not yet the complete p=6 cyclic-orbit aggregation: the ordered expansion still needs an explicit list partition/representative proof with multiplicities and an end-to-end trace theorem.

Verification status at the time of this note:
- Commit `866affa7f6b6212de6d9b15d845e88104b098a9e` passed the Lean formalization workflow and Python tests (3.11 and 3.12).
- Commit `094af60990896f09f0eb3d6b4482b40a05567e83` adds the five-`N` lemma; its Lean and Python checks were queued when inspected. Do not mark that commit verified until all three checks finish successfully.

Next: check the current commit's CI, then construct the p=6 ordered-list grouping from the exact expansion `A=K`, `B=K*N`, carefully distinguishing the choice-word length from the expanded K/N factor count.

### CI-confirmed p=6 odd-word reduction audit (2026-10-27)

The corrected five-N support bounds are now verified: commit `450ee15d9968f35829537a146f92baf4eaaf7baf` has successful Lean build and Python 3.11/3.12 workflows. The Lean failure at `094af60` was exactly a strict-vs-nonstrict bound mismatch (`b < 6` supplied where `b ≤ 5` was required); `by omega` resolves that conversion.

The actual p=6 expansion is a six-choice word expansion with A=K and B=K*N, not an arbitrary six-letter K/N word. The odd r counts below are numbers of B-choices (equivalently N-insertions after expansion), with K-runs between successive Ns:

- r=1: one necklace, representative `KKKKKN`, orbit weight 6.
- r=3: representatives `KKKNNN`, `KKNKNN`, `KKNNKN`, and `KNKNKN`, weights 6, 6, 6, and 2.
- r=5: one necklace, representative `KNNNNN`, orbit weight 6.

The weights sum to the binomial stratum sizes 6, 20, and 6. This census confirms the classes and periodic orbit but is still not a Lean proof that `orderedWordExpansion` maps into those representatives. The next formal obligation is to establish that bridge without replacing the list by a set (which would lose duplicate-word multiplicities), then apply the existing word-zero lemmas to each representative.

### p=6 three-N representative trace sum (2026-10-27)

Added `sg_trace_p6_three_N_representatives_zero` in `GlueTrace.lean`. It explicitly records the four cyclic representatives of the three-N choice stratum, with orbit weights 6, 6, 6, and 2. The representative products have K-run patterns (4,1,1), (3,2,1), (3,1,2), and (2,2,2), respectively. The proof instantiates the already established three-N word-zero lemma at those run lengths and closes the weighted sum algebraically. This is an explicit representative-level result; it does not yet prove that the ordered expansion list is partitioned by these cyclic representatives. Commit `ce276a2e2b118e99fbcdc8e2e43f859df9ded4f4`; await CI before treating this Lean addition as verified.


## 4br. Audit of the p=6 representative proof repair and current CI (2026-10-27)

This note records the source-level diagnosis for the recent p=6 odd-representative repair. It does **not** claim that the complete p=6 ordered-list assembly or the higher-moment stabilization theorem is proved.

### Commit-by-commit diagnosis

- `0a6a0e62b053e3222b9386c2c4b8fd53d051ac55` (`Normalize p6 representative trace proofs`) still failed at `GlueTrace.lean:425` with `Type mismatch: After simplification, term h3'`. Its three-N representative sum also left an unsolved goal.
- `5332cf624dce105b462b992d574b801686f04ed3` (`Use explicit rewrites for p6 representative sums`) improved the three-N sum proof by using explicit rewrites followed by `ring`. In the odd-N theorem, however, `rw [h1', h3', h5']` failed because the full aggregate `h3'` was not a syntactic subexpression of the target while the two endpoint terms were still present.
- `c6dd0bc7ec7777587aa7ac9c3f32810e92f29e69` (`Fix p6 odd representative proof by isolating endpoint traces`) made the appropriate structural change: rewrite only the one-N and five-N endpoint traces, then use the aggregate three-N result. But it used `zero_mul` in the simplifier.
- The endpoint terms have the form `6 * 0`, not `0 * 6`. Therefore `zero_mul` is the wrong identity for this goal; the needed identity is `mul_zero`. Commit `e7be77afa5fcb1a41355d3c30be6bfcfe2196f06` changes exactly this simplifier lemma and leaves the theorem statement, hypotheses, coefficients, and matrix-factor order unchanged. This is a justified local proof correction, not a weakening or masking of the statement.
- The current HEAD `44329cdf78c6b571b105987c7552ad0445690203` changes seven multiline applications of the p=10 support lemma to single-line `exact` applications. It does not alter the p=6 proof or the mathematical content of those applications.

### CI evidence and limitations

- Lean run `40489397074` for `0a6a0e62` reported the unsolved three-N goal and the `h3'` type mismatch in the odd-N theorem.
- Lean run `40490798447` for `5332cf62` reported the failed rewrite at `GlueTrace.lean:426` described above.
- The Lean run `40491483721` associated with `c6dd0bc7` failed during the Lean setup retry before the build step ran. It therefore supplies no compiler verdict for that commit's source.
- For `e7be77afa5fcb1a41355d3c30be6bfcfe2196f06`, Lean run `40493374405` and Python run `40493374314` both completed successfully.
- At the checked current HEAD `44329cdf78c6b571b105987c7552ad0445690203`, Lean run `40493873249` and Python run `40493873215` both completed successfully. The Lean build step passed; Python 3.11 and 3.12 both passed fast tests and slow level-7 convergence tests.

The green current CI confirms that this source state compiles and its configured tests pass. It does not prove the missing ordered-list-to-cyclic-strata assembly, the full p=6 trace split, boundary cancellation, the base transition, or induction. The immediate mathematical target remains the formal partition of the actual 64-element `orderedWordExpansion K (K*N) 6` list into its 14 cyclic classes with exact orbit weights, connected to the existing odd/even stratum lemmas under their actual hypotheses.


## 4bs. Diagnosis and removal of the failing p=6 strata bridge (2026-10-27)

### Confirmed failure

- Commit `ade662bb8df3f875ff5be2e9f3393e887c34955b` added `trace_orderedWordExpansion_six_cyclic_strata` in `formalization/EvgenyTheorem/TraceExpand.lean`.
- Lean run `40504931340` failed in that new theorem: at line 480, `simpa` on a `trace_cyclic_list` application produced a type mismatch with a heartbeat timeout; additional simplification and tactic execution timeouts followed at lines 486 and 495. The failure was in the attempted bridge from the generic 14-class expansion to the concrete stratum syntax, not in the earlier 64-word cyclic grouping.
- No increase to `maxHeartbeats` was appropriate: the bridge proof had not elaborated robustly and should not have been committed without a green full build.

### Minimal correction

- Commit `bac3d058a2b87fc184a042f223660442086c3827` removes only the unverified `trace_orderedWordExpansion_six_cyclic_strata` theorem.
- The previously verified `trace_orderedWordExpansion_six_cyclic` theorem remains. Comparing `TraceExpand.lean` at this commit with the known-green `0c3e8a0a81ec85d00319d4e106bd9590d0fc0364` shows the file is identical apart from extra blank lines; the failed theorem is absent.
- The PR-triggered Lean workflow for `bac3d058a2b87fc184a042f223660442086c3827`, run `40505598903`, completed successfully. The required `Build formalization` step passed, which runs `lake build EvgenyTheorem`.
- At the time of this log update, the Python workflow `40505598910` for the same SHA was still in progress; no Python result is recorded as passed here. The parallel push-triggered Lean workflow was also still running, so this note relies on the completed PR-triggered Lean run above.

### Next proof task

Do not restore the removed monolithic bridge. First develop and verify small local rotation/normalization lemmas for representatives grouped by the exact number of `K * N` choices. Then connect those lemmas to the existing p=6 odd-stratum zero results and even-stratum boundary formulas. Preserve the order of all factors and the orbit weights (including periodic classes); do not proceed to the full p=6 trace split until the bridge itself has a green full Lean build.

## 4bt. CI-confirmed two-N (5,1) representative bridge (2026-10-27)

### Source audit and exact word calculation

Commit `746e23f724b11e172d68f8559ae8fa8155d8017b` adds only the local theorem
`sg_trace_p6_ordered_two_N_5_1_representative` in `GlueTrace.lean`. The diff does
not modify other source files or the theorem's assumptions.

For the length-six choice representative `000011`, the ordered product is
`K K K K (K*N) (K*N)`. Expanding, without commuting factors, gives
`K^5 * N * K * N`. Split its list as
`[K,K,K,K,K,N] ++ [K,N]`; `trace_cyclic_list` rotates it to
`[K,N] ++ [K,K,K,K,K,N]`, i.e. the exact trace form
`K^1 * N * K^5 * N * K^0` already used by
`sg_trace_p6_lower_even_strata_boundary`. Its orbit weight is 6. This is
one of the three r=2 cyclic classes only; it is not the r=2 stratum sum or the
complete p=6 ordered-list assembly.

### Exact CI evidence for this commit

All four runs for the exact head SHA completed successfully:

- PR Lean run `40512309600`: `Build formalization` succeeded.
- Push Lean run `40512301650`: `Build formalization` succeeded.
- PR Tests run `40512309528`: Python 3.11 and 3.12 both passed the fast tests
  and slow level-7 convergence tests.
- Push Tests run `40512301593`: Python 3.11 and 3.12 both passed the fast tests
  and slow level-7 convergence tests.

Thus the local cyclic-rotation bridge compiles in the full configured Lean build
and the configured Python tests pass at this SHA. The full ordered-list-to-strata
partition, the two remaining r=2 representatives, the full p=6 trace split,
boundary cancellation, and level induction remain open.

### Next narrowly scoped representative

The next r=2 choice necklace is `000101`, orbit weight 6. Its ordered product
is `K^3 * (K*N) * K * (K*N)`, which expands in factor order to
`K^4 * N * K^2 * N`. A cyclic rotation gives
`K^2 * N * K^4 * N`, matching the second lower-even boundary representative.
The remaining periodic r=2 class is `001001`, with representative gap pattern
(3,3) and orbit weight 3. Prove and compile the (4,2) local bridge before
attempting any aggregate r=2 sum or any broader p=6 assembly.

## 4bu. CI-confirmed p=6 two-insertion representative sum (2026-10-27)

### Exact source result

Commit `78182c829501b2d6694cc449c152f97cca979b0b` adds
`sg_trace_p6_ordered_two_N_representatives_boundary` in
`formalization/EvgenyTheorem/GlueTrace.lean`. It combines the three local
cyclic-rotation bridges for the six-choice words with exactly two `K*N`
choices:

- gap pattern `(1,5)`, orbit weight 6;
- gap pattern `(2,4)`, orbit weight 6;
- periodic gap pattern `(3,3)`, orbit weight 3.

The weights sum to `6 + 6 + 3 = 15 = binomial(6, 2)`. The aggregate theorem
equates the weighted sum of those explicit ordered representatives to the
first three r=2 terms in `sg_trace_p6_lower_even_strata_boundary`. All
equalities preserve factor order and use the already-proved local
representative lemmas.

### Verification for the exact commit

The following runs for the exact SHA all completed successfully:

- PR Lean run `40530050862`: full `Build formalization` succeeded.
- Push Lean run `40530043083`: full `Build formalization` succeeded.
- PR Tests run `40530050767`: Python 3.11 and 3.12 passed both fast tests and
  slow level-7 convergence tests.
- Push Tests run `40530042965`: Python 3.11 and 3.12 passed both fast tests and
  slow level-7 convergence tests.

### Scope and next target

This closes the local representative bridge and weighted representative sum
for the r=2 stratum. It does **not** prove that the 64 entries of
`orderedWordExpansion K (K*N) 6` partition into the 14 cyclic classes, and
does not prove the complete p=6 trace split, cancellation between axes, or
induction in level.

The next even stratum to bridge is r=4. Its three cyclic gap patterns are
`(1,1,1,3)`, `(1,1,2,2)`, and periodic `(1,2,1,2)`, with respective orbit
weights 6, 6, and 3 (total `15 = binomial(6, 4)`). Before adding source code,
verify the representative products directly against the last three r=4
terms of `sg_trace_p6_lower_even_strata_boundary`, then add one local rotation
lemma at a time and require a green full Lean build and both Python versions
before proceeding.

## 4bv. CI-confirmed p=6 four-insertion representative sum (2026-10-27)

### Exact source result

Commit `7b29d9039b3503a97104e38a7e9a76cf06ce9362` adds
`sg_trace_p6_ordered_four_N_representatives_boundary` in
`formalization/EvgenyTheorem/GlueTrace.lean`. It combines the three local
representative bridges in the r=4 stratum:

- gap pattern `(1,1,1,3)`, orbit weight 6;
- gap pattern `(1,1,2,2)`, orbit weight 6;
- periodic gap pattern `(1,2,1,2)`, orbit weight 3.

The weights sum to `6 + 6 + 3 = 15 = binomial(6, 4)`. The aggregate theorem
equates the weighted sum of the three explicit ordered representatives to the
last three r=4 terms of `sg_trace_p6_lower_even_strata_boundary`. It does not
identify the complete 64-word expansion by itself.

### Verification for the exact commit

All four CI runs for this SHA completed successfully:

- PR Lean run `40547591032`: full `Build formalization` succeeded.
- Push Lean run `40547582536`: full `Build formalization` succeeded.
- PR Tests run `40547590787`: Python 3.11 and 3.12 passed fast tests and slow
  level-7 convergence tests.
- Push Tests run `40547582571`: Python 3.11 and 3.12 passed fast tests and slow
  level-7 convergence tests.

### Remaining assembly step

The source already has `trace_orderedWordExpansion_six_cyclic`, which groups
the 64 ordered words into 14 weighted cyclic representatives, as well as
`sg_trace_p6_three_N_representatives_zero`, which proves the four r=3
representatives vanish with orbit weights 6, 6, 6, and 2. The next narrow
bridge is to expand the four r=3 representatives from the generic cyclic
formula with `A = sgK` and `B = sgK * N`, preserve factor order, and connect
their weighted sum to that existing zero theorem. This will not yet be the
full p=6 split: the r=0/r=6 endpoints and the final assembly of all cyclic
classes must still be checked explicitly.

## 4bw. CI-confirmed ordered r=3 representative bridge (2026-10-27)

### Exact source result

Commit `3c09a6fc1b2923f2589a6e1a36d91836ff03998d` adds
`sg_trace_p6_ordered_three_N_representatives_zero` in
`formalization/EvgenyTheorem/GlueTrace.lean`. It instantiates the existing
three-N representative-zero theorem with the four ordered products from the
generic p=6 cyclic expansion after substituting `A = sgK` and `B = sgK * N).
The four orbit weights are 6, 6, 6, and 2; their sum is
`20 = binomial(6, 3)`. Factor order is retained, including the periodic
representative.

### Verification for the exact commit

All four CI runs for this exact SHA completed successfully:

- PR Lean run `40555669712`: full `Build formalization` succeeded.
- Push Lean run `40555653430`: full `Build formalization` succeeded.
- PR Tests run `40555668065`: Python 3.11 and 3.12 passed both fast tests and
  slow level-7 convergence tests.
- Push Tests run `40555653330`: Python 3.11 and 3.12 passed both fast tests and
  slow level-7 convergence tests.

### Remaining assembly target

The generic theorem `trace_orderedWordExpansion_six_cyclic` supplies all 14
weighted cyclic classes. The r=2 and r=4 representative sums now match their
corresponding boundary terms, and the weighted r=3 sum vanishes. The next
target is an end-to-end p=6 identity: rewrite the generic cyclic trace sum using
those bridges, kill the r=1 and r=5 classes with the existing vanishing lemmas,
retain the r=0 term `trace(K^6)` and the r=6 term `trace((K*N)^6)`, then use
`sg_trace_p6_all_even_strata_boundary` to express the complete even correction
as the existing diagonal-corner sums. This is not yet a p=8 or p=10 result and
does not assert level induction or axis invariance.


## 4bx. CI-confirmed exact sixth-moment defect recursion (2026-10-27)

### Source result

Commit `ea396025256674f84568bf9f50c2f356812c939c` adds
`defectO6` and `defectO6_succ` in
`formalization/EvgenyTheorem/GlueTrace.lean`.

The theorem is the exact sixth-moment analogue of the existing fourth-moment
recursion. With both axes satisfying the two level-`m` periodicity conditions
and `OAnti (m+1) o`, it proves

```text
D6_(m+1)(ax, ax', o)
  = D6_m(ax, ax', o)
  + D6_m(ax, ax', oBo m o)
  + D6_m(ax, ax', oCo m o)
  + glueRHS6(m, sgK(ax, o)) - glueRHS6(m, sgK(ax', o)).
```

The proof applies `pOpO_trace6_glue_final` at both axes, rewrites the
three-copy sums using `sum_gcopy` and the definitions of `Hc`, then closes
the scalar rearrangement. It preserves the boundary difference exactly; it
does **not** assume that this difference is zero and does not establish
sixth-moment stabilization.

### Verification for the exact commit

All four workflows completed successfully on this exact SHA:

- PR Lean run `40578160111`: full `Build formalization` succeeded.
- Push Lean run `40578152005`: full `Build formalization` succeeded.
- PR Tests run `40578162979`: Python 3.11 and 3.12 passed both fast tests and
  slow level-7 convergence tests.
- Push Tests run `40578151477`: Python 3.11 and 3.12 passed both fast tests and
  slow level-7 convergence tests.

### Next narrowly scoped proof obligation

The next target is to isolate exactly when the p=6 boundary correction
`glueRHS6` is axis-independent, without presuming cancellation. Its r=2
terms explicitly involve the diagonal entries of `K^4` and `K^5` at glued
partner vertices. The existing `sgK_diag`, `sgK_sq_diag`, and
`sgK_corner_data` establish axis-independence for diagonal powers one,
two, and three under their stated hypotheses; the top-stratum diagonal-cube
reduction `sg_trace_p6_top_stratum_diagonal_cube` handles the r=6 term.
The immediate algebraic lemma should therefore show that `glueRHS6` agrees
between axes **assuming** equality of the diagonal powers four and five on
the glued locus. This is only a conditional reduction. Then prove those
higher-power corner identities from the concrete geometry, or keep their
difference as part of the residual if they do not hold. No blanket
axis-invariance or level-stabilization claim follows from this entry.


## 4by. Conditional p=6 boundary axis congruence (2026-10-27)

### Exact source result

Commit `933d558159fafb747ddbd4207860cd601723ac6b` adds
`glueRHS6_sgK_axis_congr_of_diag45` in
`formalization/EvgenyTheorem/GlueCornerCube.lean`.

Under `OAnti (m+1) o`, the lemma proves
`glueRHS6 m (sgK m θ ax o) = glueRHS6 m (sgK m θ ax' o)`
assuming, for every glued state `a`,

- `(sgK m θ ax o ^ 4) a a = (sgK m θ ax' o ^ 4) a a`;
- `(sgK m θ ax o ^ 5) a a = (sgK m θ ax' o ^ 5) a a`.

The lower boundary sums are compared pointwise using the existing corner identities for powers one, two and three, plus these two explicit hypotheses. The top-stratum trace is compared only after applying the existing theorem `sg_trace_p6_top_stratum_diagonal_cube`, so the proof does not assume that `K * D` is diagonal.

### Verification for the exact source commit

All four CI workflows passed on commit `933d558159fafb747ddbd4207860cd601723ac6b`:

- Push Lean: run `40583936882`, full formalization build successful.
- PR Lean: run `40583945447`, full formalization build successful.
- Push Tests: run `40583936732`, Python 3.11 and 3.12 fast and slow tests successful.
- PR Tests: run `40583945518`, Python 3.11 and 3.12 fast and slow tests successful.

### Mathematical boundary and next obligation

This is a conditional comparison, not a proof that the fourth- and fifth-power diagonal hypotheses hold for arbitrary axis assignments. The next step is to test and then prove the exact `h4`/`h5` statements only for the intended axis pair, if they are true. If either statement fails, preserve the corresponding diagonal-power difference in the residual rather than claiming axis-independence or stabilization.


## 4bz. p=6 residual syntax correction and verified CI state (2026-10-28)

### Minimal source correction

Commit `b846d169201b3819bc1bcfa2b9f9d4f084c155e8` introduced
`glueRHS6_highPowerResidual` and
`glueRHS6_sgK_axis_residual_of_diag123`, but the final `Matrix.trace`
argument in the last `calc` step was missing one closing parenthesis.
Commit `3b3e3cf8ea52f21d5eb4634e9862be8f0e843157` changes only that
parenthesis in `formalization/EvgenyTheorem/GlueCornerCube.lean`.
It adds no new lemma and changes no mathematical assumptions.

### CI for the exact source SHA `3b3e3cf8ea52f21d5eb4634e9862be8f0e843157`

All four configured PR/push workflows completed successfully:

- PR Lean `40590688662`: `Build formalization` succeeded.
- Push Lean `40590678846`: `Build formalization` succeeded.
- PR Tests `40590688632`: Python 3.11 and 3.12 both passed fast tests and
  slow level-7 convergence tests.
- Push Tests `40590678827`: Python 3.11 and 3.12 both passed fast tests and
  slow level-7 convergence tests.

The repository workflow's configured Lean command is `lake build EvgenyTheorem`.
A separate local no-argument `lake build` was not run: this execution
container cannot resolve `github.com` to clone/install the checkout. Do not
describe that local command as verified.

### Mathematical scope after the fix

The repaired theorem proves the exact identity

`glueRHS6(K) - glueRHS6(K') = glueRHS6_highPowerResidual(K,K')`

under its stated hypotheses. The residual consists of the two weighted
boundary-sum differences with powers (1,5) and (2,4), each with coefficient
6. The terms using diagonal powers 1--3, and the top-stratum diagonal-cube
trace, are compared using existing proved identities. The residual is not
proved zero, and `defectO6_succ` still retains it explicitly.

### Numerical diagnostic and caution on the sufficient pointwise hypotheses

A scratch numerical diagnostic mirroring the repository Python SU(2) graph
and operator construction compared the current noncommuting-axis mode with
the commuting-axis mode at outer corners, levels 1--4. For `theta = pi/2`,
the diagonal blocks of powers 4 and 5 differed at two corners (differences
`-1` and `-16` per diagonal entry); at `theta = pi`, the corresponding
differences were `-2` and `-34`. The third corner showed no difference.
This is numerical evidence against assuming pointwise fourth-/fifth-power
diagonal equality without checking it.

It is **not** a Lean counterexample: the earlier convention audit in this log
still requires a finite, edge-by-edge confirmation that the Python's
index-canonicalized flux edge and Lean's point-order flux edge coincide for
the intended orientation/axis pair. Also, pointwise inequality alone does
not determine whether the two *weighted sums* in
`glueRHS6_highPowerResidual` cancel.

### Next p=6 proof obligation

Do not add hypotheses `h4`/`h5` as if established. First align the
edge/axis conventions for the intended pair (in particular `faceAxis`
versus the constant z-axis assignment) with the Lean orientation used by the
theorem. Then test/prove the actual weighted-sum identity needed to make the
residual vanish, or preserve a nonzero residual and identify the precise
remaining recurrence obstruction. No axis-independence or level stabilization
is claimed by this entry.


## 2026-10-28 — Exact p=6 numbering-orientation recursion

Verified source SHA: `49b8348813dec806ea54a36b45edbfdf0a7b39a8`.
The preceding source commit `f29d043560d864a18286c01754368a1558d6f961`
introduced `transfer_C6`; the source commit recorded here adds only
`defectO6_succ_num` in `FinalOrient.lean`.

### CI for source SHA `49b8348813dec806ea54a36b45edbfdf0a7b39a8`

All four workflows completed successfully on this exact SHA:

- Push Lean: run `40629658155`, success; `Build formalization` passed.
- PR Lean: run `40629662285`, success; `Build formalization` passed.
- Push Tests: run `40629658177`, success; Python 3.11 and 3.12 fast and slow level-7 tests passed.
- PR Tests: run `40629662414`, success; Python 3.11 and 3.12 fast and slow level-7 tests passed.

The workflow's configured Lean build is `lake build EvgenyTheorem`. A separate
local no-argument `lake build` was not verified because this execution
container cannot resolve `github.com` for a checkout; do not describe that
local command as passing.

### Mathematical result

The compiled theorem `defectO6_succ_num` states the exact recurrence:

`D6_num(m+1) = 2 * D6_num(m) + D6_til(m) + R6_num(m)`,

where the still-explicit boundary term is:

`R6_num(m) = glueRHS6(m, sgK(m, θ, faceAxis, oNum(m+1))) -`
`            glueRHS6(m, sgK(m, θ, (fun _ => 2), oNum(m+1)))`.

This follows from the generic `defectO6_succ` and the three already compiled
copy-orientation transfers `transfer_A6`, `transfer_B6`, and `transfer_C6`.
The exceptional corner clause in copy C remains intact.

This proves a recurrence with its exact boundary residual; it does **not**
prove that the residual is zero, that the two axis-dependent boundary
corrections agree, or that the sixth-moment defect is stabilized.

### Next p=6 obligation

Derive the matching exact recurrence for `oTil (m+1)`, carefully
transporting its A/B/C copies with the `cp1` corner conditions. Its
`glueRHS6` difference must also remain explicit. Then compare the two
recurrences; do not infer axis cancellation or level stabilization without
a separate proof of the weighted boundary identity.

## 2026-10-28 — Exact p=6 flipped-orientation recursion

Verified source SHA: `e5954cbc047812b44ea5d5d255e775b1d03edd8f`
(`Derive exact sixth-moment flipped-orientation recursion`).

All four workflow runs completed successfully on this exact source SHA:

- Push Lean: run `40631253169`, success (`Build formalization`).
- PR Lean: run `40631258976`, success (`Build formalization`).
- Push Tests: run `40631253045`, success.
- PR Tests: run `40631258955`, success.

The configured Lean command is `lake build EvgenyTheorem`. Python 3.11 and 3.12 passed the fast tests and slow level-7 convergence tests. A separate local no-argument `lake build` was not verified and must not be described as passing.

### Mathematical result

The newly compiled theorem `defectO6_succ_til` in `FinalTilde.lean` gives the exact recurrence, for `3 ≤ m`:

`D6_til(m+1) = D6_num(m) + 2 * D6_til(m) + R6_til(m)`,

where

`R6_til(m) = glueRHS6(m, sgK(m, θ, faceAxis, oTil(m+1))) -`
`            glueRHS6(m, sgK(m, θ, (fun _ => 2), oTil(m+1)))`.

Together with `defectO6_succ_num`, this completes the pair of exact orientation recurrences. Both retain their own explicit boundary correction. The copy-C corner conditions in the tilde proof remain explicit; neither recurrence assumes cancellation.

At this verified source state, the difference recurrence has not yet been formalized. No equality between `R6_num(m)` and `R6_til(m)`, no axis-independence, and no level stabilization is claimed.

### Next p=6 obligation

Subtract the two compiled recurrences in Lean to obtain the exact recurrence for the difference of orientation defects. Then investigate the actual weighted boundary-sum difference `R6_num(m) - R6_til(m)`; do not assume it is zero. Keep p=8 and p=10 out of scope until this p=6 obstruction is resolved.

## 2026-10-28 — Exact p=6 orientation-difference recurrence

Verified source SHA: `b94e37450275f0791bf48b223261273814c175e1`.

All four workflows succeeded on this exact SHA:

- PR Lean `40633583279`: success; the configured `Build formalization` step passed.
- Push Lean `40633578221`: success.
- PR Tests `40633583133`: success.
- Push Tests `40633578247`: success; the Python 3.11 and 3.12 fast and slow level-7 convergence tests passed in both test workflows.

The configured Lean command is `lake build EvgenyTheorem`. A separate local no-argument `lake build` was not verified.

### Mathematical result

The theorem `defectO6_orientation_difference_succ` has now been added to `FinalTilde.lean` and passed the Lean build. For `3 ≤ m`, it formally proves

`F(m+1) = F(m) + R6_num(m) - R6_til(m)`,

where `F(m) = D6_num(m) - D6_til(m)`; the two boundary residuals are exactly those in `defectO6_succ_num` and `defectO6_succ_til`. The proof rewrites by these two existing recurrences and closes the resulting complex-arithmetic identity with `ring`.

This is only the exact difference recurrence. It does not establish `R6_num(m) = R6_til(m)`, zero residual, axis-independence, or stabilization.

### Next p=6 obligation

Analyze `R6_num(m) - R6_til(m)` via the actual weighted boundary sums. Keep the powers `(1,5)` and `(2,4)` terms explicit until their equality/cancellation follows from proved hypotheses. Do not introduce unproved diagonal-equality assumptions `h4` or `h5`, and do not switch to p=8/p=10 before the p=6 obstruction is resolved.


## 4n. Exact finite-level p=6 orientation gap at level 3

**Verified source SHA:** 50129d9b78257b9f3b8cad0bdeeb4c7dcdae10c4  
**CI for that exact SHA:** all four configured workflows succeeded: PR Lean 40673620120, push Lean 40673612855, PR Tests 40673620977, push Tests 40673612869. The Python workflows passed fast and slow tests on both Python 3.11 and 3.12; Lean completed lake build EvgenyTheorem.

Let
\[
F(3,\theta)=D_6(3,\theta,o_{\rm num})-D_6(3,\theta,o_{\rm til}),
\]
where each D6 is the non-commuting trace Tr(H_C^6) minus the commuting-control trace Tr(H_C'^6), matching defectO6.

A new exact symbolic finite-level certificate, computational/p6_level3_orientation_certificate.py, represents each 2x2 block as a polynomial in
c = cos(theta/2) and s = sin(theta/2), with Gaussian-integer coefficients. It performs sparse exact matrix multiplication for level 3 and reverses only the exceptional flux-edge block corresponding to cp1 in oTil. The raw result is
\[
F(3,\theta)=-6192s^2-144c^2s^2-144s^4-864s^3.
\]
Using c^2+s^2=1, this simplifies to
\[
\boxed{F(3,\theta)=-6336s^2-864s^3.}
\]
In particular, F(3,pi) = -7200, so the finite-level orientation gap is not identically zero.

Validation is deliberately separated from the Lean theorem claim:
- at theta = pi, the unflipped traces agree with the pre-existing exact sparse Gaussian-integer certificate higher_moment_pi_certificate.py;
- the test suite records the exact level-3 traces for both orientations and both axis assignments;
- an independent dense-matrix regression test compares the symbolic formula with the production build_su2_bundle operator over positive and negative angles, including theta = pi, and explicitly checks that the exceptional edge is in the graph/flux-edge set and is ordered consistently with the Python vertex indices.

**Formal scope:** this is an exact computational certificate for the finite level-3 expression, not yet a Lean proof of the identity for all theta. The existing Lean theorem defectO6_orientation_difference_eq_level3 proves F(m,theta)=F(3,theta) for m>=3, but the polynomial evaluation of F(3,theta) has not yet been connected to that Lean development. Thus the orientation gap must not be assumed to vanish. The separate level-independence of the sixth-moment boundary residual in the numbering-oriented recurrence remains open.


## 4o. Lean base-case attempt rejected by the build

At source SHA 175f87256a9d6c9a6dbb2cd7f401f3ef8de7201b, the proposed theorem defectO6_orientation_difference_level3_pi was added by unfolding the full sixth-power trace, the point operator, graph enumeration, and SU(2) edge definitions in one norm_num call. The Lean build failed at FinalTilde.lean:741:2: deterministic timeout in the simplifier at the 200,000-heartbeat limit. The preceding commit had also shown that the first draft was outside namespace EvgenyTheorem; that namespace placement was corrected, but the brute-force expansion still timed out.

This attempt is removed in the follow-up cleanup. Do not work around the timeout by simply disabling the heartbeat limit or expanding every definition at once. The symbolic Python result remains a finite computational certificate only; no Lean theorem for the numeric level-three value was established by this attempt.

Next proof direction: construct a staged finite-level bridge with small intermediate statements (the level-three vertex/edge enumeration, the specialized edge blocks at theta = pi, and the trace/power computation), and verify each stage before combining them. Keep the existing all-level reduction and the independent boundary-residual obligation separate.


## 4p. Reject redundant pHeO_pi_edge attempt after parser failure

At source SHA 704a9e82cc922dea5b55e231119c7df6b0862c49, Lean failed at `FinalTilde.lean:764:37` with `expected token`. The failing addition was `pHeO_pi_edge`; the error points into the proposition's locally named matrix `U`/conjugate-transpose expression. The general edge-entry identity was already available as `pHeO_edge_eq`, so this helper duplicated an existing result while introducing additional syntax risk. It is removed in the cleanup rather than trying another unverified syntax variant. Keep `axisRotation_pi` and `edgeUnitaryWithAxis_pi`, which were added in the preceding green commit.

Next proof attempt must add a non-redundant bridge and be checked against the exact syntax and matrix conventions before commit. Do not claim that the level-three trace value has been proved in Lean.


## 4q. Repair after the p6 corner-edge tactic stopped making progress

On source SHA `f05145f7a8898d69c8d6646333f096a87133794a`, push and PR Lean both failed in `FinalTilde.lean:785:4` with `dsimp made no progress`. The fault was in the added `pHeO_corner_flip_swap` proof: the coordinate inequality had already reduced before `dsimp [p, q] at hx`, making the tactic invalid. The subsequent `hcpRev` branch used the same redundant simplification pattern, so both redundant `dsimp` calls are removed and the resulting arithmetic goals are left to `omega`. No new mathematical assumptions are added.

The correction is kept narrowly scoped to this one lemma. Its proof is not considered accepted until the full Lean build and both Python CI jobs pass on the resulting SHA. The local container does not have Lean/Lake installed, so no local Lean compilation is claimed.


## 4r. Level-stabilization of the p=6 boundary residual: exact remaining identity

**Audited source HEAD:** c520176fd62d7163af4e1fc98da416664535212b. The branch and PR head matched this SHA during the audit. Both Lean workflows passed (40695698377, 40695708138, with configured lake build EvgenyTheorem); both Tests workflows passed (40695698241, 40695708135, Python 3.11 and 3.12).

For \(m\ge3\), set
\[
K_m^{\mathrm{face}}=\operatorname{sgK}(m,\theta,\mathrm{faceAxis},oNum(m+1)),\quad
K_m^{(2)}=\operatorname{sgK}(m,\theta,(\lambda\_,2),oNum(m+1)),
\]
and write \(R_m=\operatorname{glueRHS6}(m,K_m^{\mathrm{face}})-\operatorname{glueRHS6}(m,K_m^{(2)})\).
The compiled theorem defectO6_succ_num_level3 gives
\[
D_{m+1}=3D_m-F_3(\theta)+R_m,\qquad
F_3(\theta)=D_3^{num}-D_3^{til}.
\]
Thus the level-independent affine recurrence sought in this branch requires the adjacent-level identity
\[
\boxed{R_{m+1}=R_m\quad(m\ge3)}
\]
(or an equally explicit proved formula for \(R_m\)); it does **not** require \(R_m=0\).

The existing theorem glueRHS6_sgK_axis_residual_of_diag123 reduces \(R_m\) to glueRHS6_highPowerResidual, which is exactly
\[
\begin{aligned}
Q_m(K,K')={}&6\Big(\sum_{g_m(x)}K_{xx}(K^5)_{\sigma x,\sigma x}
-\sum_{g_m(x)}K'_{xx}(K'^5)_{\sigma x,\sigma x}\Big)\\
&+6\Big(\sum_{g_m(x)}(K^2)_{xx}(K^4)_{\sigma x,\sigma x}
-\sum_{g_m(x)}(K'^2)_{xx}(K'^4)_{\sigma x,\sigma x}\Big).
\end{aligned}
\]
Here the sums use the exact glue predicate \(g_m\), and \(\sigma\) is the partner-corner involution from sgGlue m. Diagonal powers one and two on glued states are already axis-independent by sgK_corner_data; the remaining axis-sensitive data are the weighted fifth- and fourth-power diagonals.

**What is already proved and what it does not imply:**
- glueRHS6_highPowerResidual_num_eq_til proves the residual is invariant when oNum (m+1) is changed to oTil (m+1) at the **same fixed level m**, using locality for powers at most five. It does not compare level m with level m+1.
- defectO6_orientation_difference_succ_highPower rewrites the adjacent-level orientation-difference recurrence using Q_m; defectO6_orientation_difference_succ_invariant and defectO6_orientation_difference_eq_level3 follow because the two orientations' Q_m values agree at the same level. These statements do not establish R_{m+1}=R_m for the numbering-orientation axis residual.
- glueRHS6_sgK_axis_congr_of_diag45 is conditional on pointwise hypotheses h4 and h5. Those hypotheses have not been proved for faceAxis versus the constant axis 2, and they must not be introduced as assumptions.
- pHeO_entry_coord_dist and pOpO_pow_entry_coord_dist bound the coordinate support of nonzero entries by the power. They give a locality bound, not equality of matrix-power diagonal entries across different levels. faceAxis_shift_by_three_pow preserves axis labels under the recursive face-copy offsets, but by itself does not supply the required level-to-level rooted-neighborhood identification.

**Exact open step:** prove directly
\[
Q_{m+1}(K_{m+1}^{\mathrm{face}},K_{m+1}^{(2)})
=Q_m(K_m^{\mathrm{face}},K_m^{(2)}).
\]
A valid proof must map the six glue states between adjacent levels and preserve the **weighted sums** of the power-four and power-five corner diagonals for both axis assignments. It may be possible to derive this from a rooted, axis-labelled local graph isomorphism for walks of length at most five, with the orientation transport checked on each involved edge. No such comparison lemma is present in the audited source. A support-distance estimate alone is insufficient, and no equality of fourth- or fifth-power diagonals is assumed here.

**Disposition:** analysis only; no Lean theorem or source claim was added. The next mathematical action is to establish this finite-radius level-to-level comparison from the copy shifts and face/edge definitions, or to exhibit an exact counterexample for a specific weighted boundary sum. Do not advance the affine p=6 recurrence until this identity or an explicit alternative formula is proved.


## 4s. Exact symbolic finite-level check of the p=6 boundary residual

**Source audited before the check:** 21f3f093bbd6b021ee25e198055153594e4e8404; PR #9 head and branch moment-6-8-10 matched. On that SHA the PR Lean build and both Python test workflows completed successfully. The push Lean workflow did not run because that commit changed only Markdown files and its path filter excludes those changes. No Lean source was changed for this follow-up.

Define D_m(theta) as the existing face-axis minus constant-axis sixth-moment defect with numbering orientation, and F_3(theta) as the finite level-three orientation gap. The established recurrence has boundary correction
\[
R_m(\theta)=D_{m+1}(\theta)-3D_m(\theta)+F_3(\theta).
\]
Using the existing exact symbolic block-polynomial certificate (integer coefficients in c=cos(theta/2) and s=sin(theta/2)), the independently evaluated finite traces are
\[
\begin{aligned}
D_3={}&-38352s^2-384s^3-912s^4+4224cs^2-912c^2s^2,\\
D_4={}&-110640s^2-384s^3-2640s^4+12864cs^2-2640c^2s^2,\\
D_5={}&-327504s^2-384s^3-7824s^4+38784cs^2-7824c^2s^2,
\end{aligned}
\]
while F_3=-6192s^2-864s^3-144s^4-144c^2s^2 in raw form. Exact polynomial arithmetic gives
\[
R_3=R_4=-1776s^2-96s^3-48s^4+192cs^2-48c^2s^2.
\]
Using c^2+s^2=1, this is
\[
R_3=R_4=s^2(-1824+192c-96s).
\]
At theta=pi, the value is -1920, matching the exact Gaussian-integer trace calculation. A separate sparse-matrix angle sweep for levels 3, 4, and 5 also found R_3 approximately R_4 at tested angles; that sweep is numerical, whereas the displayed level-3/4 comparison is an exact polynomial identity.

**Scope:** this confirms only the adjacent finite-level identity R_3=R_4; it is not an induction on m, and no all-level Lean theorem is claimed. The new regression test test_exact_p6_boundary_residual_polynomial_levels_three_and_four keeps this finite algebra check reproducible.

**Remaining proof obligation:** establish R_{m+1}=R_m uniformly for m>=3. The concrete bridge needed is level-to-level stability of the corner diagonal blocks of powers 1, 2, 4, and 5 for the face-axis and constant-axis operators, with numbering orientation on the ordinary corners and the oTil-transported orientation on its exceptional corner. Existing support-distance bounds, copy entry identities, edge-order preservation and faceAxis periodicity are the inputs; what is still missing is the formal reindexing/equality of the length-at-most-five corner-walk sums. Do not infer the all-level statement from the finite calculation.


## 4t. Radius-two corner blocks: sharper local target for p=6

Exploratory exact sparse polynomial arithmetic in a local scratch implementation found that the full \(2\times2\) diagonal blocks of powers \(4\) and \(5\) at each outer corner \(O,X,Y\) agree between levels \(3\) and \(4\), separately for both axis assignments (cycling face axes and the constant \(z\)-axis) and with/without the exceptional edge flip. The comparison retains raw polynomial coefficients in \(c=\cos(\theta/2)\), \(s=\sin(\theta/2)\); it is not sampled-angle numerics.

This gives a sharper formal target than “identify the radius-five neighborhood”: for a closed length-\(n\) walk based at a root, an intermediate vertex at step \(k\) has graph distance at most \(\min(k,n-k)\). Therefore for diagonal powers \(n\le5\), every contributing walk stays within graph distance \(\lfloor n/2\rfloor\le2\). The matrix diagonal at each local vertex must still use its full graph degree, but edges leaving the radius-two ball do not contribute to those diagonal powers.

The certificate now exposes corner_diagonal_polynomials, which calculates these blocks using exact polynomial arithmetic on radius-two balls. The regression test test_outer_corner_power_blocks_stabilize_exactly_between_levels_three_and_four checks all corners, both axis assignments, both flip states, and powers four and five by exact coefficient equality.

**Formal implication:** this is a finite-level check and a candidate lemma interface, not yet an all-level proof. A Lean proof can aim to show that the radius-two, axis-labelled rooted neighborhoods (including degrees and the exceptional-edge orientation where relevant) are transported by the A/B/C copy embeddings. Existing faceAxis periodicity, copy-entry formulas, and orientation-order lemmas are relevant inputs. The remaining formal work is to establish the radius-two neighborhood equivalence uniformly for all m≥3, then reindex the closed matrix-product sums. Do not infer R_{m+1}=R_m for all levels from the finite comparison.


## 4u. p=6 high-power path-sum expansion (Lean, commit 0381bc8)

The PR now contains two generic exact identities:
\[
(K^4)_{xx}=\sum_y(K^2)_{xy}(K^2)_{yx},\qquad
(K^5)_{xx}=\sum_y(K^2)_{xy}(K^3)_{yx}.
\]
The theorem `glueRHS6_highPowerResidual_path_expansion` substitutes these identities into the exact residual `glueRHS6_highPowerResidual`, exposing the intermediate-state sums for the weighted fourth/fifth-power corner terms.

CI on `0381bc85ca617ecffe19d7107d1f5b384802dfe0` completed successfully: push Lean `40712822868`, PR Lean `40712833470`, push Python `40712822818`, PR Python `40712833222`. The PR Lean job initially failed while downloading Mathlib cache (`Broken pipe`, cache download incomplete); its rerun succeeded, including `Build formalization`. Both Python workflows passed on 3.11 and 3.12.

**Scope:** this is an algebraic path expansion only. It neither cuts off the intermediate-state sums to a radius-two ball nor identifies the rooted, axis-labelled local neighborhoods between levels. In particular, it proves neither the required adjacent-level equality \(R_{m+1}=R_m\) nor equality of the weighted \(K^4\)/\(K^5\) corner diagonals. The path-support estimate is available, but an explicit level-to-level local map and a proof that it preserves edge labels, full vertex degrees, and orientation are still required. No assumption that the fourth- and fifth-power diagonals agree was added.

## 4v. Uniform local transport — first outer corner (Lean, radius two)

The prior commit `7168a08dda3911840d9ad5694535529988f9d360` passed both Lean build workflows and all Python 3.11/3.12 push/PR test jobs. Its three `pHeO_succ_*_local_entry` results provide entrywise transfer for each copy when the local degree is unchanged.

The new lemma `corner_O_radius_two_transport` formalizes one geometric case: for (m\ge3), if (z\in V_{m+1}) and (z_1,z_2\le2), then (z\in V_m), and (z) is neither ((2^m,0)) nor ((0,2^m)). Thus the coordinate box containing the graph-radius-two neighborhood of the outer corner O lies inside copy A and avoids the two degree-exception corners. This makes the A-copy entrywise transport applicable throughout that local box.

**Scope:** only the O/A localization is formalized here. X/B and Y/C are still required, as is the reindexing of closed walks for powers four and five. No equality of high-power diagonal blocks or of (R_{m+1}) and (R_m) is claimed.

## 4w. Outer corners X/B and Y/C: radius-two localization lemmas

At commit `fd8bc0b6d71e5cb0213f02dd190989d435b3f44a`, all six Lean/Python checks passed. This change adds two structural Lean lemmas:

- `corner_X_radius_two_transport` identifies points in the coordinate box (2^{m+1}\le x+2, y\le2) as B-copy images, with the pulled-back point avoiding the two degree-exception corners for B.
- `corner_Y_radius_two_transport` identifies points in the coordinate box (x\le2, 2^{m+1}\le y+2) as C-copy images, with the pulled-back point avoiding the two degree-exception corners for C.

Combined with `corner_O_radius_two_transport`, this covers the three outer-corner radius-two coordinate boxes at the level of copy membership and local degree exceptions.

**Scope:** these lemmas do not yet give an edge-labelled graph isomorphism of the entire radius-two balls, do not compare walk weights, and do not prove (R_{m+1}=R_m). The remaining proof must use the copy entry transport and preserve edge axes, orientations, and full graph degrees while reindexing the closed-walk sums.

## 4x. Exact coordinate-box equivalences for X/B and Y/C

On `d7ea5df9cf24f5a244e0ebbd04b9407112403f34`, the prior six CI checks passed. This change adds `corner_X_radius_two_box_iff` and `corner_Y_radius_two_box_iff`, expressing both directions of the local reindexing:
[
x+2\ge 2^{m+1}, y\le2
\quad\Longleftrightarrow\quad
(x,y)\text{ is a B-copy image of }(u,v), u+2\ge2^m, v\le2,
]
and the coordinate-swapped C-copy statement for Y.

These equivalences remove a one-way membership gap before using the copy shift to reindex the intermediate states in the high-power path sums. They do not by themselves prove edge-axis preservation, equality of all walk weights, equality of high-power diagonal blocks, or (R_{m+1}=R_m). The O/A box is handled by the existing identity-map localization theorem.

## 4y. Entrywise transport with the actual recursive orientations

After all six CI jobs passed on 1b702877b8ab228228e1ae128f6bc7aff0fb258b, three one-step transport lemmas were added in FinalTilde.lean:
\[
K_{m+1}^{A}(p,q)=K_m^{\mathrm{num}}(p,q),\quad
K_{m+1}^{B}(p+2^m e_1,q+2^m e_1)=K_m^{\mathrm{num}}(p,q),\quad
K_{m+1}^{C}(p+2^m e_2,q+2^m e_2)=K_m^{\mathrm{til}}(p,q),
\]
under the stated local nonexceptional-corner hypotheses and the relevant axis periodicity. The C identity deliberately retains the oTil orientation rather than incorrectly simplifying it to oNum.

Scope: these prove preservation of a single matrix entry. They do not prove equality of sums over length-four/five closed walks, since that additionally requires a bijection of contributing intermediate-state indices and preservation of all diagonal degree factors. The all-level residual identity remains open.

## 4z. Corner-box entry interface for the high-power comparison

After all six CI jobs passed on eaefa7ebe5d3c1f86409be01d34f39514d88c484, this change adds three wrappers in FinalTilde.lean:
- O-box: identity transport into copy A, preserving oNum.
- X-box: transport through copy B, preserving oNum when the B axis labels are periodic.
- Y-box: transport through copy C, preserving oTil and therefore the exceptional corner-edge flip.

Each result is a pointwise equality of a single spin-matrix entry for endpoints inside the corresponding radius-two coordinate box. These are the local hypotheses intended for the intermediate-state sums in matrix_pow_four_diag_as_sum_sq and matrix_pow_five_diag_as_sum_two_three.

**Still open:** prove the support cutoff and reindex the sums of products of entries. No power-four/five diagonal equality, and no R_{m+1}=R_m identity, is claimed.

## 4aa. Two-step support cutoff at outer corners

Commit 47f93b1b52e9cafd1f92c2d3756b979eb739ab90 passed all six configured CI checks. This change specializes pOpO_pow_entry_coord_dist to n=2, proving:
- O-root: any nonzero (K^2)_{O,y} has y_1,y_2 ≤ 2.
- X-root: any nonzero (K^2)_{X,y} has y_1+2 ≥ 2^m and y_2 ≤ 2.
- Y-root: any nonzero (K^2)_{Y,y} has y_1 ≤ 2 and y_2+2 ≥ 2^m.

These coordinate cutoffs identify the supported intermediate-state boxes in (K^4)_{xx}=Σ_y(K^2)_{xy}(K^2)_{yx} and (K^5)_{xx}=Σ_y(K^2)_{xy}(K^3)_{yx}. They do not prove reindexing or high-power equality by themselves.


## 4ab. Correct orientation index for adjacent-level corner transport

The level-to-level residual target compares sgK (m+1) with orientation oNum (m+2) to sgK m with orientation oNum (m+1). The earlier corner-box wrappers with oNum (m+1) on the larger graph are not, by themselves, the interface for that recurrence. This change adds oNum_succ_restrict and three wrappers that use the correct orientation indices and retain the actual B/C pullbacks:
- O: oNum (m+2) at level m+1 to oNum (m+1) at parent level m.
- X/B: oNum (m+2) to oBo m (oNum (m+1)).
- Y/C: oNum (m+2) to oCo m (oNum (m+1)), preserving the exceptional C orientation.

These statements are entrywise and include only the coordinate boxes already localized in CornerLocality.lean. The missing theorem is still the weighted closed-walk sum comparison for powers 4 and 5, and hence the all-level identity R_{m+1}=R_m.


## 4ac. Restricting the p=6 weighted path sums to finite support sets

Added support-sensitive forms of the generic matrix identities for powers four and five. They are direct consequences of the existing path expansions: if (K²)_{x,y} vanishes outside a finite set S, the corresponding diagonal path sum is exactly the sum over S.

glueRHS6_highPowerResidual_local_path_expansion applies this restriction to each of the four weighted high-power sums in the p=6 residual, with an explicit family S (σ x) for the intermediate states at each glued partner. No geometric set or support assertion is assumed implicitly; both operator support obligations are function hypotheses.

Remaining step: choose the local radius-two sets in each copy, prove the support obligations and bijectively reindex them across adjacent levels using the O/X/Y copy maps. The theorem does not claim equality of the restricted sums or the all-level residual identity R_{m+1}=R_m.


## 4ad. Concrete radius-two support for the glued operator

After all six checks passed on commit 388ce8eab4bf9c4ab88ed237a5243074d1118b43, this change adds a concrete finite support family for sgK: states must remain in the same copy and within coordinate distance two of the root. The theorem sgK_pow_two_entry_mem_radius_two derives this from the existing power locality estimate and block-diagonal structure; sgK_pow_two_entry_zero_outside_radius_two gives the exact vanishing hypothesis for the finite-support residual expansion.

Still open: instantiate the generic finite-support expansion for both axis assignments, then prove a bijection of the support sets across adjacent levels and preservation of matrix-product weights under recursive-copy transport. No R_{m+1}=R_m theorem is claimed.


## 4ae. Concrete finite-support residual formula for sgK

The branch and PR head were rechecked at `de9268a7d07b7b5da57c46aa4ed87238e585f1a5` before this edit. That base SHA had four successful Actions runs: push Lean 40802879077, PR Lean 40802884135, push Tests 40802878968, and PR Tests 40802884578 (Python 3.11 and 3.12 included).

Added `glueRHS6_highPowerResidual_sgK_radius_two_path_expansion`, specializing `glueRHS6_highPowerResidual_local_path_expansion` to the real operators `sgK m θ ax o` and `sgK m θ ax' o`, with the finite set `sgK_radius_two_support m`. Both support hypotheses are discharged by `sgK_pow_two_entry_zero_outside_radius_two`; the result therefore gives the weighted fourth-/fifth-power sums as explicit finite sums rather than relying on a caller-supplied abstract support family.

This remains only Step A: it does not prove a bijection between the local sets at levels (m) and (m+1), equality of the weighted sums, or (R_{m+1}=R_m). The new SHA's own CI is pending at the time of this note.

Next: establish a rooted radius-two reindexing for O/A, X/B, and Y/C and prove preservation of edge axes, recursive orientations, full vertex degrees, and every spin-block factor before claiming any level-stability identity.



## 4af. Support-box reindexing for the p=6 corner residual

The previous commit `b040b29bc65417eebac65d983211c7309b1acad1` is fully verified on its exact SHA. Push and PR Lean builds succeeded (runs 40805240750 and 40805246864); both Python 3.11/3.12 workflows succeeded on push and PR (runs 40805240669 and 40805246921, including the slow tests).

Added `sgK_radius_two_support_O_box_iff`, `sgK_radius_two_support_X_box_iff`, and `sgK_radius_two_support_Y_box_iff` in `FinalTilde.lean`. These characterize the actual support predicate at level (m+1) for any root at O, X, or Y: O points are in the old A part, X points have the unique B-shift preimage in the parent radius-two box, and Y points have the unique C-shift preimage. The outer copy coordinate remains fixed; the spin component is not altered by the state index. The X/Y statements use the already-proved coordinate-box equivalences, and O uses `corner_O_radius_two_transport`.

This is the first, geometric part of Step B only. It does **not** prove an entrywise transport for the full `sgK` blocks under the nested copy orientations, does not yet build the finite-sum bijections for K²/K³, and does not prove equality of weighted sums or (R_{m+1}=R_m). Validation of the new commit is pending.

Next: use the finite-support characterizations to define the actual state reindexings and prove that every entry factor in the two- and three-step path products is preserved, including the C-copy orientation and all full-degree/axis data.



## 4ag. Correct the O/X/Y support-lemma elaboration failure

Lean CI for `8df96452409093943b23660986fbe9a80a6824e2` failed in `FinalTilde.lean`. The full build log isolated a malformed point type annotation in the O-root support theorem and a type mismatch between subtype membership in the finite-set `Pt` and the list-membership premises required by `corner_O_radius_two_transport` and the X/Y box equivalences.

The correction commit changes only the annotation and converts the three point-membership proofs via `List.mem_toFinset.mp`. The three support-characterization statements are unchanged. No entrywise transport or weighted-sum equality is claimed. The correction's own CI is pending.

Next after CI passes: define the concrete finite-state reindexings and prove that each K²/K³ product factor is preserved under the A/B/C corner transport, including vertex degree, axis index, and orientation.



## 4ah. Convert the final two vertexOrder membership proofs

The build for `d7638a84b4ff0e5f75869d0b832fc186d481b147` progressed past the pair annotation and O/X/Y box-lemma calls, then identified two remaining list-versus-Finset membership mismatches in `vertexOrder_sum_le`. Both calls now receive `List.mem_toFinset.mp z.2.1.2`. No theorem statement changed and no new mathematical claim was introduced; the new SHA's CI is pending.

## 2026-10-29 — Verified status of the radius-two support fix

- Verified that PR #9 remains open on branch `moment-6-8-10` at source SHA `10f0a24b562527070930e07f67c203caaae40e13`.
- The four workflows for this exact SHA are green: push Lean [40807729515](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40807729515), PR Lean [40807735639](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40807735639), push Tests [40807729529](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40807729529), and PR Tests [40807735615](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40807735615). Full configured Lean build passed; fast and slow Python tests passed on versions 3.11 and 3.12.
- The pending status recorded in the previous support-lemma entries is now corrected by this exact-SHA verification; the record of the earlier failed builds is intentionally unchanged.
- The current source establishes finite radius-two support sets and O/X/Y coordinate-box characterizations only. It does not yet establish a level-to-level bijection that preserves the matrix weights. In particular, the (K^2)/(K^3) path products and the exceptional orientation transport remain open, so (R_{m+1}=R_m) is not proved.
- Next target: construct the actual finite-state reindexing for the six glued states and prove entrywise preservation under that map. Use the explicit pairings in `sgGlue`; preserve the real orientation induced by `oCo` on the C copy rather than replacing it prematurely by `oNum`.

## 2026-10-29 — O-corner support reindexing

- Added a genuine finite-state equivalence for the O-corner radius-two support in `FinalTilde.lean`, named `sgK_radius_two_support_O_equiv`. It carries a state from level (m+1) to its parent coordinate in level (m), with the outer copy and spin preserved.
- The equivalence is derived from the existing O-box support characterization; it is not a claim about equality of `sgK` entries, powers, or weighted path sums. The X/B and Y/C correspondences remain to be formalized.
- CI for the new Lean source change is pending. The all-level residual identity (R_{m+1}=R_m) remains unproved.
- Next: formalize the X/B and Y/C reindexings, preserving their copy shifts and then prove the matrix-entry equalities needed for the path products. The C-copy orientation must remain explicit.

## 2026-10-29 — Diagnose and repair the O-corner support proof

- Diagnosis from both full Lean job logs at source SHA `16d3e702db22a9a6616c3827c9fb48deb9b09575`: the only Lean error reported is at `FinalTilde.lean:1225:4`, where `change` cannot reduce membership in the filtered finite set `sgK_radius_two_O_parent_support) to a conjunction by definitional equality.
- Corrected the proof by unfolding the support definition and simplifying `Finset.mem_filter` and `Finset.mem_univ` explicitly at `hparent`. This changes no theorem statement and makes no stronger mathematical claim.
- CI for this correction is pending. The O-corner finite-state equivalence is not yet considered compiled until the full build succeeds; the weighted path-sum identity and the all-level residual equality remain open.

## 2026-10-29 — X-corner support reindexing

- The previous O-corner proof correction at `f1e769c84767b1f22c6d9c57dee157cdfde08e5f` passed all four configured workflows, including the full Lean formalization build and Python fast/slow test stages under 3.11 and 3.12.
- Added an X-corner finite-state equivalence `sgK_radius_two_support_X_equiv` and parent support predicate `sgK_radius_two_X_parent_support`. The inverse is expressed using the coordinate inverse of `shiftPoint (2^m) 1 0`; the existing support-box theorem supplies the bounds and parent membership.
- This is not a claim that the (K^2)/(K^3) path weights are preserved, nor does it prove (R_{m+1}=R_m). The C/Y equivalence and all entrywise weight transport remain open. CI for the new source SHA is pending.

## 2026-10-29 — Fix existential elimination in the X-corner equivalence

- Full Lean logs for source SHA `6a4a6b31fccceb30d3450dc97fb74df24d7aab17` identify the first failure at `FinalTilde.lean:1296:27`: `Exists.casesOn` cannot eliminate an existential proof into a data-valued subtype. The failing construct was `rcases hz with ...` in the forward function of the X-corner equivalence.
- Replaced witness destructuring in the Type-valued branch with `Classical.choose` and `Classical.choose_spec`. This is an elaboration repair only; no mathematical assertion was strengthened.
- The corrected SHA must pass a full Lean build and push/PR Python 3.11/3.12 workflows before further work. The Y-corner support equivalence and all matrix-entry/weight preservation claims remain open.

## 2026-10-29 — Return to the last fully green Lean source

- Established a reproducible clean checkpoint: `f1e769c84767b1f22c6d9c57dee157cdfde08e5f` passed all four configured workflows (push/PR Lean and push/PR Python 3.11/3.12).
- The two subsequent commits added an X-corner finite-support equivalence and an attempted proof repair. Both full Lean workflows still failed, with the current source error in the X equivalence; the repair did not fix the complete elaboration. This is concrete evidence that this branch of work was not ready to continue.
- Restored `FinalTilde.lean` to its exact contents at the green checkpoint. This drops the X-corner equivalence experiment but keeps the already-compiled O-corner equivalence. Historical log entries are preserved.
- The next mathematical objective is the actual p=6 obstruction: prove equality of matrix-entry weights for the relevant short paths / powered entries before attempting to reindex the finite sums. Another coordinate-support equivalence alone is not sufficient. Verify the rollback CI before proceeding.

## 2026-10-29 — p=6 closure plan from the verified green checkpoint

**Verified starting point.** PR #9 remains open on `moment-6-8-10`, HEAD `e561dea2c14260be9a5baf69cc1f18c92b68b0a5`. All four workflows passed at this exact SHA: Lean Push [40832777791](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40832777791), Lean PR [40832786909](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40832786909), Python Push [40832777784](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40832777784), and Python PR [40832786910](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40832786910). The source file `FinalTilde.lean` is identical to the green source blob `ac2b244e9b4622e5ecb2fa292d178e2e13d1e805` from `f1e769c...`.

**Closure target (single central theorem).** Prove adjacent-level stability of the p=6 high-power boundary residual:
`glueRHS6_highPowerResidual (m+1) (sgK (m+1) θ faceAxis (oNum (m+2))) (sgK (m+1) θ (fun _ => 2) (oNum (m+2))) = glueRHS6_highPowerResidual m (sgK m θ faceAxis (oNum (m+1))) (sgK m θ (fun _ => 2) (oNum (m+1)))`
for `m ≥ 3`. This is the missing step after the already-compiled theorem `defectO6_succ_num_level3`; no general p=6 closure should be claimed until this identity is Lean-proved.

**Why this is the right target.** `defectO6_orientation_difference_eq_level3` already makes the orientation gap constant across levels. Therefore the numbering-orientation defect satisfies `D_{m+1}=3D_m-F_3(θ)+R_m(θ)`, where `R_m` is exactly the high-power residual above. Prove `R_{m+1}=R_m); then the recurrence has a fixed additive term and can be solved with the existing `affine_three_recurrence` in `FinalArith.lean`. The computational p=6 exact-polynomial test shows (R_3=R_4) at finite symbolic levels, but is only regression evidence, not the general theorem.

**Reusable components.**
- `glueRHS6_highPowerResidual_sgK_radius_two_path_expansion` in `GlueCornerCube.lean` rewrites the fifth-/fourth-power diagonal factors into finite radius-two sums of `K²` and `K³) path entries.
- `sgK_pow_two_entry_zero_outside_radius_two` proves the required finite support for the (K²) row.
- `pHeO_corner_O_box_entry_next_num`, `pHeO_corner_X_box_entry_next_num`, and `pHeO_corner_Y_box_entry_next_num` already transport the base operator entry across the O/A, X/B, and Y/C boxes. The C/Y case deliberately retains `oCo`/`oTil).
- `defectO6_orientation_difference_eq_level3`, `defectO6_succ_num_level3`, and `affine_three_recurrence` supply the algebraic endgame after residual stability.

**Proof construction plan.**
1. Show the 12 glued states (three copy-pairings times two spin states, with both endpoints in the sum) correspond bijectively at adjacent levels and that the partner map `sgGlue.σ` commutes with this correspondence.
2. Pull each radius-two support back by an explicit coordinate formula: O uses identity; X subtracts `2^m` from the x coordinate; Y subtracts `2^m` from the y coordinate. Preserve copy/spin coordinates. The support equivalence is a means to the end, not the target.
3. Lift base-entry preservation to the particular (K²) and (K³) entries in the residual path sum. Use the one-step coordinate locality and the fact that the full closed path has length at most five, so only the radius-two corner box is visited. Avoid claiming equality of arbitrary (K²/K³) entries for arbitrary pairs in the box; prove only the path entries actually used in the diagonal residual.
4. Apply `Finset.sum_bij` (or equivalent explicit finite-sum reindexing) first to intermediate states (y), then to glued states (x), to prove (R_{m+1}=R_m).
5. Substitute the residual identity in `defectO6_succ_num_level3`, then use `affine_three_recurrence` for the all-level recurrence. Separately decide whether an explicit trigonometric formula for the level-three constant is required; Python exact symbolic certificates alone do not discharge that Lean theorem.

**Failure guard.** The failed X-equivalence experiment at `6a4a6b31...` and its `Classical.choose` repair at `8ba29464...` showed that extracting an existential witness while constructing data in Type is invalid or brittle. Define the inverse point explicitly and eliminate existential facts only inside Prop-valued membership proofs, or avoid the Type-valued equivalence and prove the finite-sum bijection directly. No source-code change is allowed until its exact mathematical role in the residual proof is identified. Leave CI durations/configuration unchanged.

## 2026-10-29 — Explicit-coordinate X support equivalence for residual reindexing

- Implemented the X-corner support-set equivalence via an explicit inverse point coordinate `(x - 2^m, y)) and the existing `sgK_radius_two_support_X_box_iff`. The source is aimed specifically at the reindexing dependency in the single target theorem (R_{m+1}=R_m), not at expanding the list of support lemmas in isolation.
- Avoided the previous failure mode: all `rcases` over the support theorem's existential occur inside Prop-valued proof goals. The data-valued point `p) is computed directly from coordinates.
- CI for this source change is pending. Matrix-power weights and adjacent-level residual invariance have not yet been proved.
- If compilation succeeds, next prove partner-map compatibility and use this support correspondence in finite sums. Then establish local (K²/K³) entry transport for the exact paths contributing to (K⁴/K⁵) corner diagonals; do not claim all entries agree outside the radius-two box.

## 2026-10-29 — Fix product equality and reduce the X inverse composition

- Full build logs on `b70fd6677ab6b82c88135de9ea32c7a55340173e` gave two failures in the X support equivalence: line 1358 used `constructor` after the product equality had already been simplified, and line 1366 attempted a coordinate-level `change` before reducing the composite `toFun (invFun z)).
- Replaced the first with explicit product extensionality and inserted `dsimp` before the second coordinate-level change. These are narrowly targeted elaboration fixes; no definition or theorem statement changed.
- The next SHA must pass full Lean build and Python checks before extending the argument to matrix powers. Adjacent-level high-power residual stability remains unproved.

## 2026-10-29 — Reduce the shifted-coordinate expression in X right inverse

- After the prior correction, the only remaining Lean error was at line 1368: the `right_inv` goal contained the coordinates of `shiftPoint (2^m) 1 0 p`, so the proposed literal pair equality was not definitionally equal to the goal.
- Replaced the brittle `change` with direct simplification of `shiftPoint` and `Nat.add_sub_cancel_right`, matching the actual goal. This is an elaboration-only correction. Residual stability is not proved yet.

## 2026-10-29 — Y/C support equivalence on the verified X checkpoint

**Verified base:** SHA `0ce5f8f4d65e796e9b86d9a8bdb81062047f6860` passed both full Lean builds and both Python workflows (versions 3.11 and 3.12, fast and slow tests): push Lean [40836563072](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40836563072), PR Lean [40836569337](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40836569337), push Tests [40836562916](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40836562916), PR Tests [40836569344](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40836569344).

Added `sgK_radius_two_Y_parent_support` and `sgK_radius_two_support_Y_equiv` in `FinalTilde.lean`. This matches the existing O/A and X/B support mappings and uses the explicit C-shift inverse coordinate `(x, y - 2^m)). The result is a finite-state equivalence, not a matrix weight identity.

The all-level proof still requires showing that the high-level and parent-level base entries agree for all states in these supports under the nested orientations of `Hc), then transporting (K²/K³) factors and reindexing the outer `sgGlue` sum. The C orientation must remain `oCo`/`oTil`; no general (R_{m+1}=R_m) result is claimed. New-SHA CI is pending.



## 2026-10-29 — Algebraic corner-sum form of the p=6 residual

On every glued state the underlying vertex is one of the three outer corners O, X, Y. The corner degree is two at all levels (proved by recursion using the A/B/C local-degree lemmas), so `sgK_diag` gives `K_{xx}=2` and `sgK_sq_diag` gives `(K^2)_{xx}=2^2+2=6), independently of the axis assignment.

The new Lean theorem `glueRHS6_highPowerResidual_sgK_corner_reduce` therefore gives the exact identity
[
R_m=12left(sum_{g(x)}(K^5)_{sigma x,sigma x}-sum_{g(x)}(K'^5)_{sigma x,sigma x}ight)
+36left(sum_{g(x)}(K^4)_{sigma x,sigma x}-sum_{g(x)}(K'^4)_{sigma x,sigma x}ight).
]
This isolates the sole remaining dependence on the chosen axis assignment into the fourth- and fifth-power corner diagonal sums. Keeping `σ` explicit makes the already-proved root-map compatibility available for the next reindexing step.

This is a proved reduction, not an all-level stability theorem: `R_{m+1}=R_m` is still open. Next, compare the individual/cumulative fourth- and fifth-power corner diagonal contributions using radius-two path expansions and entry transports, taking special care with nested B/C copy orientation; do not promote the finite `R_3=R_4` certificate to a general proof.



## 2026-10-29 — Outer-sum transport separated from local corner-power transport

The next formal interface is now explicit. The existing glued-root equivalence and `sgK_root_pullback_sigma` suffice to reindex a sum of partner-root diagonal power entries from level (m+1) to level (m), provided those entries agree pointwise under root pullback. The new bridge theorem `glueRHS6_highPowerResidual_eq_of_corner_power_transport` then turns the four required local identities (powers 4 and 5, for face-axis and constant-axis operators) into (R_{m+1}=R_m), with the exact diagonal hypotheses for powers 1 and 2 made explicit.

No local power identity or all-level stability result is claimed by this commit. The next mathematical step is to establish those four pointwise identities using the radius-two path expansions, support correspondences, and entry/axis/orientation transport, while preserving the C-copy exceptional orientation.


## 2026-10-29 — Explicit finite-sum conversion after the outer-bridge Lean failure

The first implementation of the outer partner-sum bridge used `simp` to turn `∑ x, if p x then f x else 0` into a subtype sum. Lean 4.33.1 reported a type error while simplifying matrix-power summands at `FinalTilde.lean:2008` and `2025` on commit `3c336ea123d0a2f54045f7ca34d1a153e28c97ea`.

The correction isolates this index-set conversion in `glueRHS6_sum_ite_eq_subtype`, using `Fintype.sum_subtype_add_sum_subtype` and leaving the summand opaque. This is a proof-engineering repair only. The outer-root reindexing bridge still assumes pointwise transport of the fourth- and fifth-power diagonal entries; those local identities and the all-level equality (R_{m+1}=R_m) remain unproved.


## 2026-10-29 — Diagnose the subtype-sum `simp made no progress` failure

- Failure checkpoint: `8b6ce39ee047c5a10a51bfb331890eb9daf453ae`; both push Lean [40854423177](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40854423177) and PR Lean [40854431160](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40854431160) failed at `FinalTilde.lean:2000:16`.
- The failing step was the last `simp` in `glueRHS6_sum_ite_eq_subtype`. It did not use the dependent proof fields of the two subtypes to reduce the conditional summands, so no simplification progress was available.
- The correction explicitly uses the property field for each subtype: `if_pos x.2) on `{x // p x}`, and `if_neg x.2) with `Finset.sum_eq_zero` on `{x // ¬ p x}`. It then closes addition by zero directly. This is an index-set proof repair only.
- No fourth-/fifth-power entry transport has been established by this fix; the bridge remains conditional and adjacent-level residual stability `R_{m+1}=R_m` is still open.
- Verification status for the correction: pending new-SHA CI. Do not proceed to another source theorem until the full Lean build passes.


## 2026-10-29 — Preserve the exceptional orientation in X-corner entry transport

- The full Lean build passed at source SHA `7d98683340576aac241ac4b1d59a7f04595c8da4` (push and PR). Python workflows on that exact SHA were still in progress when analysis continued.
- Added a dedicated `pHeO_corner_X_box_entry_next_til` lemma. It transports a high-level matrix entry near X to the parent through the B coordinate shift while retaining `oTil) on both levels.
- The orientation step is justified on every relevant flux edge by `faceB) together with `cp1_shiftB), and the reverse direction uses antisymmetry. Thus the single flipped edge is explicitly carried to its parent counterpart rather than suppressed by a locality claim.
- This closes one local orientation dependency only. The adjacent-level `K^4)/`K^5) diagonal identities and `R_{m+1}=R_m) remain open.
- Verification of the new patch: pending current-SHA Lean CI. Continue with an actual `sgK) entry transport only after that build passes; do not wait for Python to begin analysis.


## 2026-10-29 — Index audit for the X-corner exceptional orientation

- The green checkpoint `07db1fb3a891b738429b4c08d4ccbcd6779dc99d` contains the X-corner `oTil) entry lemma for the pair `oTil (m+1)`/`oTil m`. The p=6 adjacent-level residual bridge instead asks for `oTil (m+2)` on level `m+1` and `oTil (m+1)` on level `m`.
- Added a separately named lemma with the exact residual indices, leaving the earlier proved lemma and its history intact. The orientation proof is based on the fact that the high-level flip lies outside `vertexOrder (m+1)), then uses the established B-copy orientation equivalence and the absence of the next flip on the parent vertex set. It does not silently identify the C/B copy orientation with ordinary numbering.
- This is still insufficient for high-power residual stability; the next step must compose the entry identities for the specific `K²/K³) factors in the finite radius-two path sums, corner by corner.
- Verification status for this source change: pending full Lean CI.


## 2026-10-29 — Local entries now suffice for both higher diagonal powers

A new abstract lemma, `matrix_pow_four_five_diag_transport_of_local_entries`, has been added in `FinalTilde.lean`. It proves both diagonal-power transports from a finite-support equivalence and pointwise one-step entry transport on the support. The finite path algebra is explicit: `K^4) is expanded as a product of two squares; `K^5) is expanded into `K^2) times `K^3), with `K^3) expanded as `K K^2). Root row/column support hypotheses justify each restriction to the finite set, while the support equivalence reindexes every resulting finite sum.

This reduces the next concrete step to a single clean interface: prove one-step `sgK) entry preservation inside the O/X/Y radius-two supports for the two axis/orientation choices, plus the first-/second-power support facts. It does not yet imply the four local power identities needed by the residual bridge or the all-level stability equation `R_{m+1}=R_m`. CI on the new SHA is pending.


## 2026-10-29 — Correct finite-subtype indexing in the power-transport lemma

The first compile attempt of `matrix_pow_four_five_diag_transport_of_local_entries` exposed a mismatch between the predicate-subtype Fintype and Mathlib's canonical `Finset.Subtype.fintype S`. The correction introduces a conversion lemma whose codomain is indexed by `S) itself, changes the support equivalence to `S ≃ T), and uses the same canonical subtype instances throughout the power-2, power-3, power-4, and power-5 sums. The `K^3=K K^2) step is also isolated as a named equality.

No concrete entry-transport theorem is claimed by this repair; full Lean verification on the new commit is pending.


## 2026-10-29 — Remove type mismatch in support-subtype path sums

The attempt to force finite-set subtypes through a locally defined equivalence failed because the type-level notation `S) did not elaborate as the intended subtype in that declaration. The fix removes the helper and consistently uses the proposition-indexed subtype `{x // x ∈ S}` at every stage, including the support equivalence, power-2/path sums, and fourth/fifth diagonal reindexings. This gives the sum conversion theorem and the matrix-power proof one uniform Fintype representation.

The previous full Lean run on SHA `969085624e95167efe13f5b45341f97c03b4acba` failed with this mismatch (push and PR). Verification of the correction is pending; no higher-moment transport is claimed yet.


## 2026-10-29 — Three-pass audit and removal of the unfinished path-transport abstraction

The last attempted block `matrix_pow_four_five_diag_transport_of_local_entries` was not yet connected to a concrete `sgK) entry-transport theorem. Lean failed because the proof alternated between `Subtype.fintype (fun x => x ∈ S)` and `Finset.Subtype.fintype S`, which are not definitionally equal. The attempted fix then treated a finite set `T` as a type in some `Equiv.sum_comp` lambdas. Push and PR Lean runs for SHA `3f269fde2703e8fa2af9b152375223f7e7910470` failed at the same ten sum-conversion sites.

The unfinished abstraction was removed from `FinalTilde.lean`; previously compiled O/X/Y support and orientation lemmas remain. This restores that source file to its last fully Lean-green version at `f388e6209c76900f442fd65b8146414bd0c2b719`, while keeping the chronology. It is not a branch reset and does not remove the earlier geometry lemmas.

Next mathematical work must start from the concrete high-root `sgK) support and its parent correspondence. O/A, X/B, and Y/C must preserve copy label, point, spin, exact `oNum/oTil/oBo/oCo) conventions, and axis periodicity. Then prove one-step entry equality on all support pairs and only afterwards derive the finite path sums. `R_{m+1}=R_m` remains unproved.


## 2026-10-29 — Exact O-box point-entry transport for the residual tilde orientations

The current green checkpoint already had `pHeO_corner_O_box_entry_next_num`, but it did not state the exact orientation pair required by the adjacent-level residual. Added `pHeO_corner_O_box_entry_next_til`: on the O radius-two box, the exceptional edge `cp1 n) has x-coordinate `2^n-1), which is strictly greater than 2 for the two relevant levels `n=m+1,m+2). Therefore both `oTil) relations coincide with `oNum) on the local pair, and the numbered transport gives the desired equality.

The proof keeps both levels and both orientations explicit. It transports point-operator entries only; it does not yet lift the result to `sgK) on glued-root states or imply equality of the fourth/fifth powers. The next concrete check is to use the root copy label to specialize this point-entry result to the A-block of `sgK), then handle the shifted B/C blocks separately. New-SHA Lean verification is pending.


## 2026-10-29 — O-box Lean failure diagnosis and correction

The failed SHA `3fec4bd1c1e02b1f2c16ab146c46b48b7c434e03` showed a too-weak arithmetic estimate and a missing imported theorem. Corrected on `1b99dc16f912bce2fe04cd65c6ee26fcbd7afc09`: use `4 ≤ 2^n` for `2 < 2^n-1), and prove the pointwise orientation congruence locally from already imported low-level lemmas. This remains a point-entry result only. Wait for both Lean workflows before making another mathematical change.


## 2026-10-29 — Revert O-box tilde entry attempt

The concrete O-box orientation lemma was reverted after CI exposed errors in the arithmetic calc chain and an unresolved congruence identifier. The source was restored to the exact `FinalTilde.lean` content at green checkpoint `2bf84fea6a42708a84f6d701075c17d64663d99c`. The local O-box strategy should be redesigned and checked against exact low-level theorem signatures before another commit; no B/C or power-transport work should be layered on top of the failed attempt.


## 2026-10-29 — A-block point-entry coverage extended to X

The corrected Y/C point-level transport and its A-block wrapper compile on the new source. Added `sgK_A_X_entry_next_til`, packaging the existing actual-tilde X-box transport into `WSG) states for the A block. This complements `sgK_O_A_entry_next_til` and `sgK_A_Y_entry_next_til`. It is still only a local matrix-entry equality: it does not establish equality of `sgK^4) or `sgK^5) diagonals. The next broad step is to assemble matching one-step transports for B/C blocks across the relevant root neighborhoods, then derive the two power-diagonal equalities using radius-two support and matrix multiplication.


## 2026-10-29 — Declaration-order issue in the A-block X wrapper

The failed build at `0bae1cddee6886964fb48b69cd4fb3220868df23` exposed a declaration-order mistake: the A-block state wrapper referenced the actual-tilde X point-entry theorem before that theorem was declared. The correction moves the wrapper to immediately after the X proof, preserving its proof and statement. Next step is to verify both Lean workflows on the new SHA before adding any further transport lemmas.


## 2026-10-29 — C outer-copy O-box entry transport

The C-copy at an O-local coordinate box has an orientation path already available in the source: `cp1_shiftC) removes the exceptional edge under the C shift, and `Hc_C_num_eq_parent_til` transfers the numbered C orientation to the parent `oTil). The new `sgK_C_O_entry_next_til` composes those facts with the ordinary O-box entry transport. This fills the third outer-copy entry case for the O corner; X/Y corner and power-sum assembly remain separate requirements.


## 2026-10-29 — Scope correction for exceptional orientation

The failed C/O attempt exposed the key constraint: `oTil n = oNum n` is not a global statement on the level-n graph because the exceptional edge `cp1 n` can be present. Therefore removed the global same-index entry lemma and converted orientations only locally inside the O box, using the proven coordinate-bound exclusion `cp1_not_O_radius_two`. At the C-shift level, `cp1_shiftC` remains the correct tool because the shifted points exclude the exceptional edge at the next level. New Lean CI is required before proceeding.


## 2026-10-29 — C/X block entry transport

The C/X entry bridge now composes the verified point-level X-box tilde transport with `Hc_C_num_eq_parent_til`. At the high and low levels, the C-copy pullback means orientation changes can be justified using `cp1_shiftC` only; this preserves the exceptional-edge semantics. The companion B/Y bridge is still required before assembling the cross-level fourth/fifth-power diagonal equalities.


## 2026-10-29 — Make the C/X parent bound explicit

The parent `Hc_C_num_eq_parent_til` invocation now discharges its `1 ≤ m` bound from `3 ≤ m` via `by omega`. This prevents the same predicate mismatch previously found in the C/O attempt. No mathematical statement changed; full Lean CI on the new commit is required before continuing.


## 2026-10-29 — C/X theorem declaration order

CI for `acd33bc3465cc21367034412e852b662d74a5272` reported that `pHeO_corner_X_box_entry_next_til` was unavailable at the point where the new C/X wrapper was written. The point-level theorem is declared later in the file, so the wrapper is relocated immediately after that dependency. Verify the full build before continuing to B/Y.


## 2026-10-29 — C/X wrapper endpoint substitution bug

The source error was caused by the two `rfl) patterns in the existential elimination, which eliminated the original endpoint names used by the subsequent orientation conversion proof. The fix keeps the equalities as named hypotheses and uses them as the output coordinate witnesses. This removes the cascade of unknown-identifier errors without changing any mathematical claim.


## 2026-10-29 — B/Y state transport closes local corner coverage

The B/Y case completes the six local entry transports around the three glued-root pairs. It composes the established `pHeO_corner_Y_box_entry_next_til` with the B-copy orientation reduction. The high B pullback becomes the high-level `oTil) relation using the no-corner bound after B shift and the restriction lemma; the parent B pullback reduces to `oNum m), which matches parent `oTil(m+1)) on this Y-local box because `cp1(m+1)) is excluded there. Only after Lean confirms this local bridge should the proof lift these entry equalities to fourth/fifth powers.


## 2026-10-29 — B/Y side-condition correction

The sole Lean error in the B/Y wrapper was the known predicate-strength mismatch for `cp1_not_A` at the parent level. Discharged the required `1 ≤ m` from `3 ≤ m` via `by omega`. Recheck both push and PR Lean builds before adding the power-sum proof.


## 2026-10-29 — General algebraic transport lemma for powers four and five

The new `matrix_pow_four_five_diag_eq_of_local_equiv` isolates the finite algebra needed for the p=6 residual. Given a state equivalence between two finite local supports, entry equality for `K) and `L) on those supports, and vanishing of first/second powers outside, it proves that fourth- and fifth-power diagonal entries agree. For power five, the proof uses `K^3 = K K^2); the intermediate state in the `K^2) column is kept in the radius-two support. Next, instantiate this theorem for each glued-root copy/corner case using `sgK_radius_two_support_{O,X,Y}_equiv` and the six one-step transport lemmas, then supply the resulting `h4/h5) to `glueRHS6_highPowerResidual_eq_of_corner_power_transport`.


## 2026-10-29 — Compile repair for the conditional fourth/fifth-power transport

On parent SHA `373773bcc96773381f5d712d503338f98c0ab027`, the PR and push Lean builds both failed in `FinalTilde.lean` for two source-level reasons: a detached doc-comment before the new support-sum helper, and an incompatibility between the generic predicate-subtype enumeration `Subtype.fintype` and the finite-set subtype enumeration `Finset.Subtype.fintype S`. The doc-comment is now attached to the theorem it documents. The support-sum helper explicitly proves equality of the two corresponding `Finset.univ` finsets before invoking `glueRHS6_sum_ite_eq_subtype`.

This change only repairs the generic finite-index conversion. The lemma `matrix_pow_four_five_diag_eq_of_local_equiv` remains conditional on local entry matching and one-/two-step row/column vanishing. No concrete (K^4/K^5) diagonal equality for `sgK`, no equality of sixth-moment residuals, and no completed sixth-moment theorem is claimed. The next gate is a successful full Lean build in both push and PR workflows on the new SHA. After that, instantiate the already available radius-two support equivalences and local corner-entry bridges to obtain the actual `h4/h5` obligations.


## 2026-10-29 — Concrete A/X instance of fourth/fifth diagonal transport

The generic finite-neighborhood algebra helper has now been specialized to a root in copy A at corner X. The specialization is intended to obtain the (K^4) and (K^5) diagonal equalities by combining the existing X radius-two state equivalence with `sgK_A_X_entry_next_til`. The one-step and two-step row/column vanishing obligations are separately discharged using `sgK_entry_coord_dist`, the symmetric radius-two support, and `sgK_pow_two_entry_zero_outside_radius_two`.

This is a single corner/copy case only. It does not yet provide the uniform `h4/h5` hypotheses for all six endpoints of the glued pairs or establish stability of the sixth-moment residual. The current SHA must pass full Lean push and PR builds before the remaining five cases are added.


## 2026-10-29 — Common support wrapper and B/O fourth/fifth diagonal case

The shared support-equivalence wrapper now assembles the one-step and two-step zero-outside obligations from the symmetric radius-two support and the existing `sgK_pow_two_entry_zero_outside_radius_two` theorem. The B-copy O-corner specialization uses the previously established `sgK_B_O_entry_next_til` entry transport and `sgK_radius_two_support_O_equiv`. This handles the B/O glued endpoint paired with A/X, but it is not yet a uniform theorem for all glued roots. Full Lean push and PR builds on the new SHA are required before adding the remaining corner cases.


## 2026-10-29 — B/O failed build: normalize the O-corner pullback explicitly

The first B/O specialization failed because `simp [sgK_root_pullback_pt, hwPoint]` left conditional point definitions unresolved. The fix explicitly uses `sgK_root_pullback_pt_O` to prove the pulled-back point is O, then derives its first and second coordinates as zero. Those facts support the finite-parent membership, root-equivalence equality, and radius-two subset inclusion. No new hypotheses were introduced. The B/O specialization remains unaccepted until both full Lean push and PR workflows pass on the corrected SHA.


## 2026-10-29 — C/O fourth/fifth diagonal transport

The C-copy O-corner case instantiates the same finite-support power-transport wrapper used in the compiled B/O case, now with `sgK_C_O_entry_next_til`. It relies on the existing O-corner radius-two equivalence and explicit O root-pullback lemma. This provides a third endpoint specialization (A/X, B/O, C/O), not yet the uniform `h4/h5` statement for all glued partner roots. Full Lean push and PR builds are required before implementing A/Y, B/Y and C/X.


## 2026-10-29 — A/Y fourth/fifth diagonal transport

The A-copy Y-corner specialization uses `sgK_radius_two_support_Y_equiv` together with `sgK_A_Y_entry_next_til`. The inverse state map subtracts `2^m` in the y-coordinate, while the Y support bounds are (x\le2) and (2^{m+1}\le y+2). The proof then uses the existing finite path-sum matrix-power lemma with explicit row/column zero-outside-support premises. This does not yet close the uniform glued-root transport or the sixth-moment residual. Require green push and PR full Lean builds before adding another endpoint.


## 2026-10-29 — B/Y fourth/fifth diagonal transport

The B-copy Y-corner case is now added using `sgK_radius_two_support_Y_equiv` and `sgK_B_Y_entry_next_til`. Like A/Y, it uses the inverse Y shift `(x,y)\mapsto(x,y-2^m)`, with support bounds (x\le2) and (2^{m+1}\le y+2). The shared finite-neighborhood power lemma reduces the (K^4/K^5) diagonal equality to the checked local bridge plus first-/second-power zero-outside-support conditions. This remains an endpoint specialization, not yet a uniform glued-root statement or a closed sixth-moment residual.


## 2026-10-29 — Remove duplicated declarations from the B/Y insertion

The Lean failure on `ca06a7b4b8d37c1696fcbe927d720d34a7f9996b` came from copying past the end of A/Y and duplicating the generic support-equivalence wrapper plus the existing B/O and C/O specializations. Removed that repeated tail while preserving the new B/Y specialization and the original declarations. The reported failure was duplicate declarations, not a type error in the B/Y theorem. Do not proceed to C/X until both full Lean builds pass on the cleaned SHA.


## 2026-10-29 — C/X fourth/fifth diagonal transport

The C-copy X-corner specialization uses `sgK_radius_two_support_X_equiv` and `sgK_C_X_entry_next_til`. It mirrors A/X because both use the X support bounds and the inverse coordinate map `(x,y)\mapsto(x-2^m,y)`; the copy label and local entry bridge are the only endpoint-specific changes. It still needs a green full Lean build and has not yet been applied to obtain the uniform high-power residual hypotheses.


## 2026-10-29 — Remove the orphaned generic-wrapper doc-comment

The C/X build failed syntactically at the duplicate generic-wrapper doc-comment immediately preceding `glueRHS6_highPowerResidual_eq_of_corner_power_transport`. The generic wrapper is already defined above, so this stray documentation block was removed without changing any theorem body or assumption. The next checkpoint is a successful full Lean build on both push and PR events.


## 2026-10-29 — Six endpoint cases now feed the concrete p=6 residual transport

The generic glued-partner proof splits the six disjuncts of `gl` and dispatches partner endpoints to B/O, A/X, C/O, A/Y, C/X, or B/Y, respectively. It then gives a concrete adjacent-level equality for `glueRHS6_highPowerResidual` with the tilde orientation, comparing `faceAxis` against the constant axis. The high/low diagonal conditions use `sgK_diag`, `sgK_sq_diag`, and the existing fact that glued states have degree two; the fourth/fifth diagonal hypotheses are supplied by the six local endpoint transport theorems. This is the bridge needed to make the sixth-moment recurrence's boundary residual independent of level.


## 2026-10-29 — Constant boundary term in the p=6 recurrence

The six endpoint transport cases imply adjacent-level stability of the concrete tilde high-power residual. Induction reduces that residual to its level-three value; the existing same-level num/til equivalence transfers the result to numbering orientation. This yields an affine recurrence whose boundary contribution is explicitly a fixed level-three residual, rather than a level-dependent term. The base residual is not assumed to vanish.


## 2026-10-29 — Clean up completed constant-boundary proof

The new constant-boundary recurrence proof's two rewrite steps already solved the goal, so the trailing `ring` caused a no-goals error. Removed that redundant tactic. All level-three reductions and theorem statements are unchanged. The next checkpoint is successful full Lean push and PR builds.


## 2026-10-29 — Closed form from the stabilized sixth-moment recurrence

The fixed boundary term plus `affine_three_recurrence` now yields an exact formula for `defectO6 m θ faceAxis (fun _ => 2) (oNum m)` as an affine function of (3^{m-3}). The constant is expressed using the actual level-three defect, level-three orientation difference, and level-three `glueRHS6_highPowerResidual`; no base value is assumed to vanish. The remaining closure question is whether those finite-level quantities already have exact symbolic evaluations in the repository.


## 2026-10-29 — Sixth-moment growth law has a direct named interface

The proof now exposes the exact all-angle result in the form
`D_m(θ) = 3^{m-3} A_6(θ) + B_6(θ)` for every `m ≥ 3`, where `A_6` and `B_6` are explicit definitions in terms of the level-three defect, orientation gap, and high-power boundary residual. It also states the equivalent recurrence `D_{m+1}=3D_m+C_6(θ)`. This is a formal all-level growth law, not an elementary trigonometric simplification of `C_6(θ)`; the latter is still not claimed.


## 2026-10-29 — Public status synchronized after the H6 proof

The README and higher-moments status now reflect the verified theorem
`D_{m+1}=3D_m+C_6(θ)` and `D_m=3^{m-3}A_6(θ)+B_6(θ)` for every
angle and `m ≥ 3`. They explicitly preserve the two remaining H6 limitations:
the general-angle level-2-to-3 transition and simplification of the finite
level-three coefficient. The H8/H10 all-angle results remain open.


## 2026-10-29 — H6 base transition closed by exact symbolic polynomial certificate

Define `D_m(θ)` as the numbering-orientation sixth-moment defect,
`c=cos(θ/2)`, and `s=sin(θ/2)`. The Lean development proves
`D_(m+1)=3D_m+C₆(θ)` for every `m≥3`, with its level-independent
constant originally expressed through finite level-three operator data.

The exact polynomial certificate now computes
`D₂=-14592s²+1344cs²-384s³` and verifies the finite base-transition
identity `D₃-3D₂=C₆(θ)` for all angles, with
`C₆(θ)=4512s²+192cs²+768s³`. The verification works with exact integer
coefficients in the polynomial basis `c^a s^b`, then normalizes by
`c²+s²=1`. It does not sample floating-point angle grids.

Consequently the recurrence extends from `m≥3` to all `m≥2`, with closed
form `D_m=3^(m-2)D₂+(3^(m-2)-1)C₆/2`, equivalently
`D_m=-(12336·3^(m-2)+2256)s²+(1440·3^(m-2)-96)cs²-384s³`.
In particular, `C₆(π)=5280`, matching the exact sparse arithmetic
certificates.

**Formalization boundary:** the induction/boundary transport and recurrence
for `m≥3` remain checked by Lean. The exceptional finite level-2 transition
is checked by exact symbolic Python arithmetic and regression tests; a
Lean-kernel proof of that finite symbolic identity remains future hardening,
not an open mathematical claim in the combined certificate.



## 2026-10-29 — Full verification of the exact H6 base certificate

The source/test checkpoint `772b521afd6befcb80af0d590f6742e488a6ea76` passed all four required workflows:
- Lean push `40926915630` — success;
- Lean pull request `40926931506` — success;
- Python push `40926915594` — success for Python 3.11 and 3.12;
- Python pull request `40926930923` — success for Python 3.11 and 3.12.

The exact test also pins the raw level-two polynomial and its reduction by (c^2+s^2=1). The result is a closed H6 recurrence and explicit formula for all (m\ge2) by combining the Lean-proved (m\ge3) recurrence with an exact symbolic finite base identity. The finite identity is not represented as Lean-kernel checked.


## 2026-10-30 — H8 r=3 class audit and exact proof-state correction

For the p=8 ordered expansion, the cyclic inventory has 36 classes in total.
The r=3 stratum consists of seven cyclic classes, each with orbit weight 8;
their total contribution accounts for 56 of the 256 ordered factor words.
The seven representatives in `sg_trace_p8_three_N_stratum_zero` are
rotated only by `trace_cyclic_list`, which applies cyclic invariance of the
matrix trace and does not permute the relative order of factors.

The seven resulting applications of
`trace_three_N_word_zero_of_OAnti` use exponent tuples (a,b,c,d)
`(1,1,1,5)`, `(1,1,5,1)`, `(1,1,2,4)`, `(1,1,4,2)`,
`(1,2,2,3)`, `(1,1,3,3)`, and `(1,2,3,2)`.
The helper requires the glued-corner hypothesis only for the selected middle
power (K^b); here (bin\{1,2\}). Since (m\ge3), we have
(2<2^m), so each concrete helper call meets its strict degree bound.
The helper derives the corner condition from `OAnti (m + 1) o`, block
diagonality of (K), and the geometric support estimate. No reversal,
complex-conjugation, or arbitrary factor reordering is used.

The final failure on the audited source SHA was not a failed corner lemma.
The theorem body performed `dsimp` on the goal before introducing fresh local
names `K` and `N`; this exposed the lets in the target, so the closing
`simp [hzero_r3_1, …, hzero_r3_7]` no longer saw the exact local expressions.
The correction leaves the goal definitionally equal but explicitly changes
it back to the seven-term expression in the local `K` and `N`. This does
not change any representative or mathematical hypothesis. Its acceptance
still depends on the fresh full Lean build.

The p=8 reduction ledger continues to distinguish all strata:
- r=0: one separate `trace(K^8)` term;
- r=1: one cyclic class (weight 8), covered by
  `sg_trace_p8_one_N_stratum_zero`;
- r=2: 4 cyclic classes, total weight 28, reduced to a two-N boundary sum;
- r=3: 7 cyclic classes, total weight 56, represented by the theorem above;
- r=4: 10 cyclic classes, total weight 70, reduced to a four-N boundary sum;
- r=5: 7 cyclic classes, total weight 56, not yet assembled into a concrete
  H8 theorem; the existing five-N OAnti helper requires two selected
  middle-power corner bounds, which must be checked class by class;
- r=6: 4 cyclic classes, total weight 28, reduced to a six-N boundary sum;
- r=7: 1 cyclic class, total weight 8, not yet assembled into a concrete
  H8 theorem; the seven-N OAnti helper requires three selected
  middle-power corner bounds;
- r=8: one top class, weight 1, retained as a boundary/diagonal contribution.

The positive even-stratum assembly is not a full trace split and is not a
cancellation theorem. The next H8 work is to formalize and verify r=5 and r=7,
then assemble the complete ordered split with the separate r=0 term and all
exact orbit weights. Only after that can the joint comparison of
(B_{8,2}+B_{8,4}+B_{8,6}+B_{8,8}) be attempted. In particular, do not
assert that each boundary stratum vanishes: the top r=8 term may be nonzero
and may cancel only under matching support and degree hypotheses for the two
operators. No H8 level recurrence or closed formula has yet been proved.
H10 remains deferred until the H8 chain is complete.
