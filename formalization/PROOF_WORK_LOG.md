# Lean Proof Work Log

Scope: existing PR #9, branch `moment-6-8-10`. Do not create branches, PRs, or issues.

## Incident log

### 2026-10-25 — p=10 supported fifth-power trace lemma

- Commit `066d9de480bb2efa5fa142adca35c25df1103057`: first version of `trace_alternating_five_supported_diagonal`.
- CI result: Lean build failed in `formalization/EvgenyTheorem/GlueTrace.lean` at line 796 with a typeclass inference error for `Matrix.trace_mul_comm _ _`.
- Commit `caf246c50841c98e6d24bfbc078495424330dc05`: attempted to make the cyclic trace rewrite explicit.
- CI result: Lean formalization failed again. The log showed the unresolved goal at `GlueTrace.lean:795:56`; the proposed rewrite did not close the goal.
- Commit `e130160427d90faa329f83ab4fa48a79df648110`: split the cyclic trace rewrite into explicit steps. CI: Lean formalization and tests passed.
- Commit `30c98f303f58980ea2a764b51883e5c9f8203e1d`: added `sg_trace_p10_top_stratum_diagonal_fifth`, applying the supported fifth-power lemma to the concrete Sierpinski-gasket top-stratum boundary contribution.
- CI on `30c98f3`: **Lean formalization success; Python 3.11 success; Python 3.12 success.**
- Verified mathematical scope: the p=10 top-stratum contribution equals the pointwise fifth-power sum. This does **not** prove cancellation with lower strata or axis-independence of the full moment defect.

## Next mathematical blocker

The existing p=6 development has `sg_trace_p6_all_even_strata_boundary`, an explicit expansion of the lower even strata plus the top stratum. For p=10, the current file has only the concrete top-stratum boundary reduction, its fifth-power trace bridge, and its pointwise fifth-power form. The next substantive task is to derive the **full p=10 even-strata boundary expansion** from the ordered-word expansion, preserving the exact word multiplicities, and only then compare/cancel terms across orientations. Do not infer coefficients by analogy with p=6.


## p=10 even-strata multiplicity audit (combinatorial, not yet Lean-formalized)

For a word with exactly r occurrences of the boundary letter B = K*N in the expansion of (K + K*N)^10, the cyclic trace can be written with r positive K-run lengths (a₁,…,aᵣ) summing to 10. Cyclic rotations have the same trace. For a cyclic composition with orbit size s, its total multiplicity among the original length-10 words is 10s/r. This is the same counting rule that reproduces the existing p=6 coefficients (for r=2: 6, 6, 3; for r=4: 6, 6, 3).

A direct exhaustive enumeration of positive compositions, grouped by cyclic rotation, gives:

| Number r of N factors | Number of positive compositions | Cyclic classes | Sum of class multiplicities | Check against binomial coefficient |
|---:|---:|---:|---:|---:|
| 2 | 9 | 5 | 45 | C(10,2) = 45 |
| 4 | 84 | 22 | 210 | C(10,4) = 210 |
| 6 | 126 | 22 | 210 | C(10,6) = 210 |
| 8 | 36 | 5 | 45 | C(10,8) = 45 |
| 10 | 1 | 1 | 1 | C(10,10) = 1 |

The multiplicity checksum is 45 + 210 + 210 + 45 + 1 = 511, equal to the number of even-cardinality subsets of a 10-letter word excluding the empty subset (sum of the five even binomial coefficients). The full p=10 even-strata expansion therefore has 55 cyclic composition classes before any further identifications from reversal, Hermiticity, or vanishing lemmas. The odd-N word classes are not included here: their vanishing must be justified by the existing trace/support lemmas in the formal proof, not merely assumed from this count.

**Status:** combinatorial audit only. These counts are not yet encoded as a Lean theorem and do not establish cancellation between orientations. The next code change should formalize a small generic cyclic-composition/multiplicity lemma or introduce the p=10 boundary-expansion theorem in controlled groups, validating each coefficient against the checksum before adding axis-comparison claims.


## Full cyclic-composition representatives for p=10

This table records the complete output of an exhaustive positive-composition enumeration. Each representative is the lexicographically least cyclic rotation (entries are positive integers summing to 10). The coefficient is (10s/r), where (s) is the number of distinct cyclic rotations. This is a combinatorial ledger for the later trace expansion, **not** a claim that different representatives have different matrix values or that any class vanishes.

| r | Canonical run lengths | Rotation orbit size s | Word coefficient 10s/r |
|---:|---|---:|---:|
| 2 | (1,9) | 2 | 10 |
| 2 | (2,8) | 2 | 10 |
| 2 | (3,7) | 2 | 10 |
| 2 | (4,6) | 2 | 10 |
| 2 | (5,5) | 1 | 5 |
| 4 | (1,1,1,7) | 4 | 10 |
| 4 | (1,1,2,6) | 4 | 10 |
| 4 | (1,1,3,5) | 4 | 10 |
| 4 | (1,1,4,4) | 4 | 10 |
| 4 | (1,1,5,3) | 4 | 10 |
| 4 | (1,1,6,2) | 4 | 10 |
| 4 | (1,2,1,6) | 4 | 10 |
| 4 | (1,2,2,5) | 4 | 10 |
| 4 | (1,2,3,4) | 4 | 10 |
| 4 | (1,2,4,3) | 4 | 10 |
| 4 | (1,2,5,2) | 4 | 10 |
| 4 | (1,3,1,5) | 4 | 10 |
| 4 | (1,3,2,4) | 4 | 10 |
| 4 | (1,3,3,3) | 4 | 10 |
| 4 | (1,3,4,2) | 4 | 10 |
| 4 | (1,4,1,4) | 2 | 5 |
| 4 | (1,4,2,3) | 4 | 10 |
| 4 | (1,4,3,2) | 4 | 10 |
| 4 | (1,5,2,2) | 4 | 10 |
| 4 | (2,2,2,4) | 4 | 10 |
| 4 | (2,2,3,3) | 4 | 10 |
| 4 | (2,3,2,3) | 2 | 5 |
| 6 | (1,1,1,1,1,5) | 6 | 10 |
| 6 | (1,1,1,1,2,4) | 6 | 10 |
| 6 | (1,1,1,1,3,3) | 6 | 10 |
| 6 | (1,1,1,1,4,2) | 6 | 10 |
| 6 | (1,1,1,2,1,4) | 6 | 10 |
| 6 | (1,1,1,2,2,3) | 6 | 10 |
| 6 | (1,1,1,2,3,2) | 6 | 10 |
| 6 | (1,1,1,3,1,3) | 6 | 10 |
| 6 | (1,1,1,3,2,2) | 6 | 10 |
| 6 | (1,1,1,4,1,2) | 6 | 10 |
| 6 | (1,1,2,1,1,4) | 6 | 10 |
| 6 | (1,1,2,1,2,3) | 6 | 10 |
| 6 | (1,1,2,1,3,2) | 6 | 10 |
| 6 | (1,1,2,2,1,3) | 6 | 10 |
| 6 | (1,1,2,2,2,2) | 6 | 10 |
| 6 | (1,1,2,3,1,2) | 6 | 10 |
| 6 | (1,1,3,1,1,3) | 3 | 5 |
| 6 | (1,1,3,1,2,2) | 6 | 10 |
| 6 | (1,1,3,2,1,2) | 6 | 10 |
| 6 | (1,2,1,2,1,3) | 6 | 10 |
| 6 | (1,2,1,2,2,2) | 6 | 10 |
| 6 | (1,2,2,1,2,2) | 3 | 5 |
| 8 | (1,1,1,1,1,1,1,3) | 8 | 10 |
| 8 | (1,1,1,1,1,1,2,2) | 8 | 10 |
| 8 | (1,1,1,1,1,2,1,2) | 8 | 10 |
| 8 | (1,1,1,1,2,1,1,2) | 8 | 10 |
| 8 | (1,1,1,2,1,1,1,2) | 4 | 5 |
| 10 | (1,1,1,1,1,1,1,1,1,1) | 1 | 1 |

**Enumeration checks:** the table has 5 + 22 + 22 + 5 + 1 = 55 rows. The coefficient sums by stratum are 45, 210, 210, 45, 1, respectively, matching \\(\binom{10}{r}\\). The representatives with coefficient 5 are the periodic cyclic words whose rotation orbit is smaller than r. This is why assigning coefficient 10 to every representative would overcount.

**Next proof step:** match each row to a generic boundary-reduction lemma and then establish any additional equivalences/vanishing by Lean proofs. In particular, the existing concrete p=10 four-N specializations are not yet a complete 22-class r=4 expansion, and this table alone does not close the p=10 theorem.

## Required procedure for each next change

1. Read the latest PR head and the complete failing Lean log before editing.
2. Inspect the exact source around the target and compare with already compiling lemmas.
3. Calculate the word/orbit multiplicities before writing a coefficient-bearing theorem.
4. Make one narrowly scoped correction or theorem only; no speculative follow-on lemmas.
5. Wait for Lean formalization to finish and inspect its result. A green unrelated test workflow is not evidence that Lean compiles.
6. Record commit SHA, exact error or passing result, and next action here.
7. If the proof strategy or multiplicities cannot be justified from the definitions, stop and report the blocker rather than guessing.

## Current verified status

- PR: https://github.com/RFT-SIRM/Evgeny-Theorem/pull/9
- Working branch: `moment-6-8-10`
- Pre-change PR head: `bac1376571066cd3fa0f92ee6b5043a7fe83bdb9`.
- Pre-change CI at that head: **Lean formalization success; Tests success** (workflow runs 40285722762 and 40285722806).
- The cyclic-composition table above is a checked combinatorial audit only; it is not a Lean proof and does not claim the p=10 cancellation theorem.


## Session handoff — 2026-10-26 (PR #9)

### Latest source state
- PR #9, branch `moment-6-8-10`.
- Current source commit: `0f5b0b59cabae276a633f365c31c39e1310d845e` (`Correct periodic p10 six-N cyclic representative`).
- This commit corrects the cyclic representative previously mislabeled as `(1,1,1,3,1,3)`; the intended periodic representative is `(1,1,3,1,1,3)`, with orbit size 3 and coefficient 5.
- Lean workflow run `40344545561`: **completed successfully**.
- Tests workflow run `40344545618`: **in progress at handoff**. Do not call the whole commit green until this finishes successfully.
- The previous commit `8b5fa80` had both Lean formalization and Tests successful, but its class label/run-length sequence was subsequently found incorrect and corrected in `0f5b0b5`.
- Do not use a raised `maxHeartbeats 800000` workaround. The unsupported class theorem that used it was removed earlier; current class theorem has no such local option.

### Important correction / avoid repeating
- Do not call the class `(1,1,1,3,1,3)` the periodic class. The periodic class in the ledger is `(1,1,3,1,1,3)`.
- Verify the literal sequence in both the source trace word and the boundary-diagonal powers; do not rely on theorem names or comments alone.
- The six-N class theorem added in `0f5b0b5` is a single boundary reduction. It is not an aggregate six-N stratum and does not prove p=10 cancellation or the full theorem.

### Next actions
1. Poll Tests workflow `40344545618` for the current head `0f5b0b59cabae276a633f365c31c39e1310d845e`; inspect logs if it fails. Lean is already green for this exact commit.
2. If Tests passes, continue only on this same branch/PR. Before adding another class, compare the next unimplemented representative against the complete table above and existing theorem bodies; compute orbit size/coefficient independently.
3. The six-N representatives already present are: `111115`, `111124`, `111133`, `111142`, `111214`, `111223`, `111232`, and `113113` (the last is the corrected `(1,1,3,1,1,3))). Check remaining table entries before choosing the next.
4. Make one small change at a time; no heartbeat inflation, no speculative batches, no new branch/PR/issue. Require both full Lean formalization and Python 3.11/3.12 test jobs green before continuing.
5. Keep the end goal explicit: formalize the complete p=10 even-strata boundary expansion with exact multiplicities, then prove the necessary orientation comparison/cancellation. The current per-class boundary lemmas and the combinatorial table alone do not finish the theorem. The four-N stratum also remains incomplete (22 classes).
