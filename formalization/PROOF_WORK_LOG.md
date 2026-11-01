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


## 2026-10-28 — p=6 residual syntax fix and CI verification

- Source correction: commit `3b3e3cf8ea52f21d5eb4634e9862be8f0e843157`
  adds the missing closing parenthesis to the final `Matrix.trace` argument
  in `GlueCornerCube.lean`. No other Lean source was changed.
- At that exact SHA, PR Lean run `40590688662` and push Lean run
  `40590678846` both passed `Build formalization`.
- PR Tests run `40590688632` and push Tests run `40590678827` both passed
  the fast and slow test suites on Python 3.11 and 3.12.
- CI's configured build command is `lake build EvgenyTheorem`; a separate
  local no-argument `lake build` could not be run because the container
  could not resolve `github.com`.
- The theorem now compiles and records the exact difference of the p=6
  boundary corrections as `glueRHS6_highPowerResidual`. It does not prove
  that residual zero. The axis-independent p=6 recurrence remains blocked by
  the weighted (1,5) and (2,4) sums. A Python-only corner-power diagnostic
  cautions against assuming pointwise equality of powers 4 and 5, but is not
  a formal counterexample because the finite Python/Lean edge-axis convention
  match is not yet machine-checked.
- Next: resolve that convention match for the intended axis pair, then test
  the weighted residual identity under the actual hypotheses. Do not add a
  speculative lemma or switch to p=8/p=10 before this p=6 barrier is clear.


## 2026-10-28 — Exact p=6 numbering-orientation recursion

- Source commit: `49b8348813dec806ea54a36b45edbfdf0a7b39a8` adds
  `defectO6_succ_num`; the preceding source commits completed the p=6
  A/B/C orientation-transfer lemmas.
- CI at that exact SHA: Push Lean `40629658155` passed; PR Lean
  `40629662285` passed; Push Tests `40629658177` passed; PR Tests
  `40629662414` passed. Both Python 3.11 and 3.12 passed fast and slow
  level-7 convergence tests.
- Exact result: `D6_num(m+1) = 2 * D6_num(m) + D6_til(m) + R6_num(m)`,
  where `R6_num(m)` is the difference of `glueRHS6` for `faceAxis` and
  the constant axis 2. The boundary term has not been shown to vanish.
- CI's configured Lean command is `lake build EvgenyTheorem`; a separate
  local no-argument `lake build` was not verified in this network-restricted
  container.
- Next: prove the parallel recurrence for `oTil` with its special corner
  cases, retaining its own boundary residual, then compare the recurrences.
  No axis-independence or stabilization claim is made here.

## 2026-10-28 — Exact p=6 flipped-orientation recursion

- Verified source SHA: `e5954cbc047812b44ea5d5d255e775b1d03edd8f`.
- The new `FinalTilde.lean` theorem `defectO6_succ_til` compiles and proves, for `3 ≤ m`,
  `D6_til(m+1) = D6_num(m) + 2 * D6_til(m) + R6_til(m)`.
- The residual remains explicit:
  `R6_til(m) = glueRHS6(m, sgK(m, θ, faceAxis, oTil(m+1))) -`
  `            glueRHS6(m, sgK(m, θ, (fun _ => 2), oTil(m+1)))`.
  The earlier `defectO6_succ_num` has the matching form with coefficients 2 and 1 and its own residual.
- All four CI workflows succeeded on this exact source SHA: Push Lean `40631253169`; PR Lean `40631258976`; Push Tests `40631253045`; PR Tests `40631258955`. Lean's configured `lake build EvgenyTheorem` passed; Python 3.11/3.12 fast and slow level-7 tests passed. A separate local no-argument `lake build` was not verified.
- No residual equality, boundary cancellation, axis-independence, or stabilization is established by these recurrences.

**Next:** formally subtract the two recurrences under their shared hypothesis `3 ≤ m`, keeping `R6_num(m) - R6_til(m)` explicit. Then analyze that weighted boundary difference without assuming it vanishes; remain focused on p=6.

## 2026-10-28 — Exact p=6 orientation-difference recurrence

- Verified source SHA: `b94e37450275f0791bf48b223261273814c175e1`.
- All four workflows passed on that exact SHA: PR Lean `40633583279`; Push Lean `40633578221`; PR Tests `40633583133`; Push Tests `40633578247`. Both Python 3.11 and 3.12 passed fast tests and slow level-7 convergence. The configured Lean build is `lake build EvgenyTheorem`; a separate local no-argument `lake build` was not verified.
- `FinalTilde.lean` now contains `defectO6_orientation_difference_succ`. For `3 ≤ m`, it proves
  `F(m+1) = F(m) + R6_num(m) - R6_til(m)`,
  where `F(m) = D6_num(m) - D6_til(m)). It is derived directly from the two compiled recurrences; no equality of residuals is assumed.
- Remaining obstruction: no proof that `R6_num(m) - R6_til(m) = 0`; no axis-independence or stabilization is established.

**Next:** expand the two residuals using `glueRHS6_sgK_axis_residual_of_diag123` and study the actual weighted sums involving powers `(1,5)` and `(2,4)`. Do not assume diagonal equalities for powers 4 and 5 and do not move to p=8/p=10.


## 2026-10-28 — Exact finite-level p=6 orientation gap

- Audited PR #9 on branch moment-6-8-10; the parent before this follow-up was 50129d9b78257b9f3b8cad0bdeeb4c7dcdae10c4. No new branch, PR, or issue was created.
- The symbolic certificate computational/p6_level3_orientation_certificate.py yields
  F(3, theta) = -6192 s^2 - 144 c^2 s^2 - 144 s^4 - 864 s^3,
  with s = sin(theta/2), hence F(3, theta) = -6336 s^2 - 864 s^3 using cos^2(theta/2) + sin^2(theta/2) = 1.
- At theta = pi, F(3, pi) = -7200, which rules out treating the two orientation defects as equal by default.
- The exact sparse certificate's unflipped traces are checked against the previously existing exact certificate at theta = pi. An additional regression test compares the symbolic level-3 formula against direct dense matrix powers from build_su2_bundle on a signed angle grid and verifies the exceptional edge orientation/index assumptions.
- All four workflows passed on parent SHA 50129d9: PR Lean 40673620120, push Lean 40673612855, PR Tests 40673620977, push Tests 40673612869. The configured Lean check was lake build EvgenyTheorem; Python fast and slow tests passed under 3.11 and 3.12.

**Scope and remaining obligation:** the result is an exact finite-level computational certificate, not yet a Lean theorem connecting F(3, theta) to -6336 sin^2(theta/2) - 864 sin^3(theta/2). defectO6_orientation_difference_eq_level3 still only reduces the all-level orientation gap to F(3, theta); no zero claim is valid. The separate boundary residual in defectO6_succ_num_level3 still needs its own level-independence analysis. Keep p=8 and p=10 out of scope.

**Next:** pursue a Lean bridge for the finite-level identity (or a proved explicit finite expression equivalent to it) before attempting to close the all-level p=6 recurrence. Do not replace F(3, theta) or the boundary residual by zero.


## 2026-10-28 — Remove timed-out p=6 base-case proof attempt

- Audited source SHA 175f87256a9d6c9a6dbb2cd7f401f3ef8de7201b.
- Lean failed in formalization/EvgenyTheorem/FinalTilde.lean:741:2: simp/norm_num hit the deterministic 200,000-heartbeat limit while expanding all definitions for the level-three sixth-power trace at theta = pi.
- The original draft also placed the declaration outside namespace EvgenyTheorem; although that placement was fixed, the all-at-once finite expansion remained too expensive. The failed theorem is removed rather than hidden behind an unlimited heartbeat setting.
- The parent SHA bf4fa6f7d306f6fc5a5a738b55bdaa6e5be76bcc had all four CI workflows green. The all-angle symbolic result and its Python regression test remain in the computational layer, but they are not claimed as a Lean theorem.
- Next: stage a finite-level Lean bridge through explicit graph/edge facts and specialized matrix-block computations; do not unfold the full graph/operator power in one tactic call. Keep p=6 as the sole target and keep the boundary residual as a separate open obligation.


## 2026-10-28 — Remove failing redundant oriented-entry helper

- Audited CI on `704a9e82cc922dea5b55e231119c7df6b0862c49`: push Lean failed in `FinalTilde.lean:764:37` with `expected token`; this was a Lean parser failure, not a Python failure. The PR Lean run was additionally interrupted during Mathlib cache download, but the push build gave the source error.
- Removed only `pHeO_pi_edge`, which restated the already-existing `pHeO_edge_eq` with a local `U` expression. Preserved `axisRotation_pi` and `edgeUnitaryWithAxis_pi` from the preceding all-green SHA `3d6a161db3e88993379a083af593ac38a6ab9b64`.
- No all-level or numeric-base-case theorem is claimed. After cleanup, run the full Lean build and Python 3.11/3.12 tests for the new exact SHA before proceeding.


## 2026-10-28 — Fix no-progress `dsimp` in corner-edge lemma

- Source SHA `f05145f7a8898d69c8d6646333f096a87133794a` failed both push and PR Lean at `FinalTilde.lean:785:4` with `dsimp made no progress`.
- Removed the redundant `dsimp [p, q] at hx` tactic from the `hnle` block and the same pattern from `hcpRev`; retained `omega` to close the arithmetic contradictions. No hypotheses or mathematical statements changed.
- The correction needs full CI confirmation on its own SHA before further proof work.


## 2026-10-28 — Restore last green Lean source after failed corner lemma

Both Lean workflows for `e6233009fa4531cc7943a29ae8dcd6e3b6234519` failed in `FinalTilde.lean:800:4`: `omega could not prove the goal` inside the newly added `pHeO_corner_flip_swap`. This shows the attempted proof lacks a justified arithmetic fact about `vIdx`; it must not be patched with more guessed tactics. The Lean source is restored byte-for-byte to the known-green version at `421875e543039e25c1273d958d0595858aec74bb` (blob `a04830a861a3220cee3e8ffce0e9a4323aefc200`), removing the entire failed lemma. This restores the previously passing proof state; the mathematical bridge remains open. Research log keeps the failed-attempt history.


## 2026-10-28 — Exact remaining equality for p=6 boundary residual stabilization

- Rechecked PR #9 HEAD and moment-6-8-10: both were exactly c520176fd62d7163af4e1fc98da416664535212b; no concurrent branch movement was observed.
- All four CI runs for this SHA completed successfully: Push Lean 40695698377, PR Lean 40695708138, Push Tests 40695698241, PR Tests 40695708135. The configured Lean command was lake build EvgenyTheorem; Tests passed on Python 3.11 and 3.12.
- Inspected defectO6_succ_num_level3, defectO6_orientation_difference_succ_highPower, glueRHS6_highPowerResidual, glueRHS6_sgK_axis_residual_of_diag123, glueRHS6_highPowerResidual_num_eq_til, and glueRHS6_sgK_axis_congr_of_diag45.
- The exact target for the closed affine recurrence is R_{m+1}=R_m, where R_m=glueRHS6(m,K_m^face)-glueRHS6(m,K_m^(2)). By the existing residual reduction, this is equality of the corresponding weighted fourth/fifth-power sums Q_{m+1}=Q_m, not the same-level orientation equality already proved.
- Existing locality lemmas bound support of powers but do not prove level-to-level equality of the weighted corner diagonal sums. The general axis-congruence lemma requires h4 and h5, which are not available; no pointwise fourth/fifth-power diagonal equality is assumed.
- No Lean source was changed. The mathematical blocker is now stated precisely: construct and prove a level-to-level map of the six glue states that preserves the weighted p=6 corner sums for powers 4 and 5, using the recursive copy geometry, face-axis periodicity, and orientation transport—or find an exact counterexample. Do not assume R_m=0 or that the orientation gap vanishes.


## 2026-10-28 — Exact p=6 boundary-residual polynomial at levels 3 and 4

- Before editing, rechecked that PR #9 and moment-6-8-10 both pointed to 21f3f093bbd6b021ee25e198055153594e4e8404. The PR Lean run and both Python test runs on that SHA were completed successfully.
- Recomputed the finite-level trace polynomials with exact sparse 2x2-block arithmetic. The residual in the current recurrence is R_m=D_{m+1}-3D_m+F_3.
- Exact symbolic calculation gives R_3=R_4=-1776s^2-96s^3-48s^4+192cs^2-48c^2s^2=s^2(-1824+192c-96s), where c=cos(theta/2), s=sin(theta/2). At theta=pi, this evaluates to -1920 and agrees with the existing exact integer trace certificate.
- Added test_exact_p6_boundary_residual_polynomial_levels_three_and_four to guard that specific finite-level calculation. It explicitly makes no all-level claim.
- This still does not prove R_{m+1}=R_m for arbitrary m. The next formal lemma must show level-to-level equality of the weighted corner diagonal contributions from powers 4 and 5 by reindexing walks of length at most five in the rooted, axis-labelled local neighborhoods. Existing support and copy/axis lemmas are ingredients, not a substitute for that map.
- No Lean source was changed; this step records and tests a finite exact calculation rather than asserting the theorem is closed.


## 2026-10-28 — Radius-two local block check for p=6

- Rechecked the prior SHA 2039b0e259fe688b7eb1e23129458c5209cc825d; its Lean build and both push/PR Python suites had completed successfully before this change.
- Exact local sparse-polynomial calculations compare the full 2x2 corner diagonal blocks (H^4)vv and (H^5)vv for outer corners O, X, Y at levels 3 and 4, with cycling axes / constant axis and normal / flipped corner-edge orientation. All raw coefficient dictionaries agree.
- Added corner_diagonal_polynomials, using only the graph-radius-two ball and full graph degrees, plus test_outer_corner_power_blocks_stabilize_exactly_between_levels_three_and_four.
- Justification for radius two: every term in a diagonal entry of H^n is a closed walk; at the k-th step its graph distance to the base is at most min(k,n-k) <= floor(n/2). Hence powers 4 and 5 cannot use vertices beyond graph distance two.
- No Lean source was changed. The level-3/4 exact comparison identifies a smaller candidate interface for the all-level theorem; uniform transport of these rooted, axis-labelled radius-two neighborhoods is still to be proved.


## 2026-10-28 — Exact p=6 residual path expansion

- Audited PR #9 and branch `moment-6-8-10` before editing; both pointed to `0381bc85ca617ecffe19d7107d1f5b384802dfe0`.
- Added in `GlueCornerCube.lean` the generic diagonal expansions `matrix_pow_four_diag_as_sum_sq` and `matrix_pow_five_diag_as_sum_two_three`, and the concrete residual expansion `glueRHS6_highPowerResidual_path_expansion`.
- Exact content: expose the (K^4) and (K^5) terms as sums over intermediate states. This is a valid algebraic rewrite; no support cutoff or level comparison is built into it.
- CI for the code commit: push Lean 40712822868 and PR Lean 40712833470 succeeded (the PR Lean cache-download attempt was retried after an infrastructure Broken pipe); push Tests 40712822818 and PR Tests 40712833222 succeeded, including Python 3.11 and 3.12.
- **Still open:** prove that the weighted fourth/fifth-power corner sums are preserved between adjacent levels for the face-axis versus constant-axis operators. The support-distance bound alone does not supply a rooted, axis-labelled neighborhood map; no h4/h5 equality has been assumed.
- Next mathematical task: construct the explicit radius-two corner-neighborhood transport, including full graph degrees and orientation labels, and use it to reindex the closed-walk sums. If this map cannot be established from the copy/face definitions, stop rather than add a speculative lemma.

## 2026-10-28 — Verified copy-entry transport; start radius-two localization

- The repair commit `7168a08dda3911840d9ad5694535529988f9d360` passed all six checks: both configured Lean builds, plus Python 3.11 and 3.12 in push and pull-request workflows.
- The three compiled entrywise lemmas `pHeO_succ_A_local_entry`, `pHeO_succ_B_local_entry`, and `pHeO_succ_C_local_entry` combine the existing off-diagonal copy-entry identities with the already proved local degree equalities.
- Added `corner_O_radius_two_transport` in `CornerLocality.lean`: for (m\ge3), a level-(m+1) vertex with coordinates at most two lies in copy A and is not either far corner where the A-copy degree could change.
- This is only the O/A geometric localization step. It proves no equality for powers four or five and no claim that (R_{m+1}=R_m).
- **Next after CI:** prove the analogous X/B and Y/C localization statements. Then use those maps, entry transport, and the closed-walk radius-two bound to formalize the weighted power-four/five diagonal-sum comparison. Stop at any failed hypothesis or counterexample; do not infer all-level stability from finite checks.

## 2026-10-28 — Outer-corner X/B and Y/C radius-two localization

- Rechecked that PR #9 and `moment-6-8-10` were at `fd8bc0b6d71e5cb0213f02dd190989d435b3f44a`; both Lean build workflows and all push/PR Python 3.11/3.12 jobs passed.
- Added `corner_X_radius_two_transport`: points in (V_{m+1}) satisfying (2^{m+1}\le x+2) and (y\le2) are in copy B, and the pulled-back point avoids ((0,0)) and ((0,2^m)).
- Added `corner_Y_radius_two_transport`: points in (V_{m+1}) satisfying (x\le2) and (2^{m+1}\le y+2) are in copy C, and the pulled-back point avoids ((0,0)) and ((2^m,0)).
- Together with `corner_O_radius_two_transport`, these are geometric localization statements only. They do not establish equality of fourth/fifth-power diagonal sums or (R_{m+1}=R_m).
- Next after CI: use the three localizations with the copy entry lemmas to formulate the induced reindexing on local closed walks; keep full degrees and orientation labels explicit, and stop if the copy map fails to preserve any needed datum.

## 2026-10-28 — Exact coordinate-box reindexing for X/B and Y/C

- Rechecked that PR #9 and `moment-6-8-10` were at `d7ea5df9cf24f5a244e0ebbd04b9407112403f34`; both Lean builds and Python 3.11/3.12 jobs in push and PR workflows passed.
- Added `corner_X_radius_two_box_iff` and `corner_Y_radius_two_box_iff`. Each proves that the corresponding level-(m+1) coordinate box is exactly the image of its parent-level box under the relevant copy shift, with the inequalities transported both ways.
- These iff lemmas are the set-reindexing interface needed before reindexing intermediate states in the power-four/five path expansions. They concern coordinate boxes derived from support bounds, not an assertion that these boxes equal graph-metric balls.
- **Still open:** show that the copy-entry transport preserves all entries needed along every contributing closed walk and reindex the weighted fourth/fifth-power sums. No (R_{m+1}=R_m) claim is made.

## 2026-10-28 — Actual matrix-entry transport with recursive orientations

- Rechecked the branch and confirmed all six CI jobs on 1b702877b8ab228228e1ae128f6bc7aff0fb258b passed before editing.
- Added pHeO_succ_A_num_entry: on the old A copy, entries at level m+1 with oNum (m+1) agree with parent entries using oNum m.
- Added pHeO_succ_B_num_entry: on the B copy, the same entry equality holds after the B shift, using axis periodicity and pulling the orientation back to oNum m.
- Added pHeO_succ_C_num_entry_til: on the C copy, transported entries use oTil m, explicitly retaining the exceptional corner flip.
- These are one-step entry identities, not yet power-four/five diagonal identities. The next proof must apply them to every factor in the closed-walk expansion and prove that the summation domains are bijectively reindexed by the coordinate-box equivalences.

## 2026-10-28 — Corner-box matrix-entry interface

- Rechecked that all six CI jobs on eaefa7ebe5d3c1f86409be01d34f39514d88c484 passed.
- Added pHeO_corner_O_box_entry: in the O-corner coordinate box, level-(m+1) entries equal the parent entries with ordinary numbering orientation.
- Added pHeO_corner_X_box_entry: the X-box entries are transported to copy B and parent oNum, under the explicit axis-periodicity hypothesis.
- Added pHeO_corner_Y_box_entry: the Y-box entries are transported to copy C and parent oTil, under explicit axis periodicity; the exceptional orientation flip is retained.
- These wrappers compose the previously proved geometric box lemmas with the entrywise copy lemmas. They are a local interface only; they do not yet compare any matrix-power diagonal or the high-power residual.
- Next: prove that the sums over intermediate states in the K^4/K^5 diagonal expansions can be restricted to these boxes and reindexed via the coordinate-box equivalences.

## 2026-10-28 — Two-step support cutoffs at the three outer corners

- Rechecked commit 47f93b1b52e9cafd1f92c2d3756b979eb739ab90: both Lean build jobs and all Python 3.11/3.12 push/PR tests passed.
- Added pOpO_pow_two_corner_O_support, pOpO_pow_two_corner_X_support, and pOpO_pow_two_corner_Y_support.
- Each follows from pOpO_pow_entry_coord_dist by specializing to n=2. It proves that a nonzero (K^2) corner-to-intermediate-state entry lies in its corresponding radius-two coordinate box.
- These are support facts needed for the first factor in the fourth-/fifth-power diagonal expansions. They do not yet reindex the sums or establish high-power diagonal equality.
- Next: combine the support cutoffs with the corner-box entry equalities and compare the two-step entries, before attempting the fourth-/fifth-power sums.


## 2026-10-28 — Recursive-orientation index for level-to-level corner transport

- Rechecked HEAD d8b39f489bd2d9c4c78a755c4953454442fe6126: all six configured Lean/Python checks passed in push and PR workflows.
- Added oNum_succ_restrict, showing that oNum (m+2) restricts to oNum (m+1) on the entire level-(m+1) vertex set.
- Added three corner-box entry transports for the actual adjacent-level residual comparison: the larger-level operator uses oNum (m+2), while the parent copy entries use oNum (m+1), oBo m (oNum (m+1)), and oCo m (oNum (m+1)), respectively.
- The C-copy conclusion intentionally keeps oCo rather than replacing it prematurely by oNum; its exceptional orientation flip remains explicit.
- This repairs the orientation index needed by the residual recurrence. These remain single-entry transport lemmas; no equality of fourth/fifth-power diagonal sums or R_{m+1}=R_m is claimed.
- Next: use these entries and the radius-two support argument to prove the weighted local closed-walk sum comparison for powers four and five.


## 2026-10-29 — Finite-support form of the p=6 path sums

- Rechecked that commit 46206a87114cee7bf995958d20da2068ac56178f passed both Lean build jobs and all four Python 3.11/3.12 push/PR jobs.
- Added support-restricted versions of the generic K^4 and K^5 diagonal path-sum identities. The proof uses the existing factorization formulas and Finset.sum_subset: when (K^2)_{x,y}=0 outside a finite set S, the intermediate-state sum can be restricted to S.
- Added glueRHS6_highPowerResidual_local_path_expansion, which rewrites each weighted K^4/K^5 contribution to a finite support set S (σ x) supplied by the caller.
- The new theorem deliberately takes the support property as an explicit hypothesis; it does not yet construct the three geometric box sets or compare their sums across adjacent levels.
- Next: instantiate S with the appropriate same-copy radius-two boxes, prove the support hypotheses from sgK_pow_entry_zero_of_coord_gap and the block structure, and then transport the restricted sums using the orientation-aligned corner entry lemmas.


## 2026-10-29 — Concrete radius-two support for the p=6 residual

- Rechecked commit 388ce8eab4bf9c4ab88ed237a5243074d1118b43: both Lean builds and all four Python 3.11/3.12 push/PR jobs succeeded.
- Added sgK_radius_two_support, a finite coordinate box of radius two that preserves the copy index of the block-diagonal sgK operator.
- Proved that every nonzero entry of sgK ^ 2 lies in this set: coordinate bounds follow from sgK_pow_entry_coord_dist, and copy preservation follows from blockK_pow_local.
- Added the exact vanishing corollary outside this set. This supplies the concrete support hypothesis needed to instantiate glueRHS6_highPowerResidual_local_path_expansion for the face-axis and constant-axis operators.
- The weighted sums have not yet been compared across adjacent levels; the next proof must reindex these finite sets and compare matrix-product weights under the O/X/Y transports.


## 2026-10-29 — Instantiate the p=6 finite-support formula for actual operators

- Rechecked PR #9 and branch `moment-6-8-10` before editing: both matched `de9268a7d07b7b5da57c46aa4ed87238e585f1a5`.
- The base SHA had all four configured workflows green: push Lean build [40802879077](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40802879077), PR Lean build [40802884135](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40802884135), push tests [40802878968](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40802878968), and PR tests [40802884578](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40802884578), with Python 3.11 and 3.12.
- Added `glueRHS6_highPowerResidual_sgK_radius_two_path_expansion` in `GlueCornerCube.lean`. It instantiates the generic finite-support expansion for the two concrete `sgK` operators using `sgK_radius_two_support`; the required vanishing hypotheses follow from `sgK_pow_two_entry_zero_outside_radius_two`.
- This makes the residual's weighted fourth/fifth-power terms explicit finite sums over the actual radius-two support. It does not compare those sums across levels and does not prove (R_{m+1}=R_m). Validation for the new source SHA is pending until its own CI runs finish.
- Next: prove the required local-copy reindexing and preservation of every matrix-product factor under the O/X/Y transports. Do not proceed to p=8 or p=10.



## 2026-10-29 — Verified finite-support expansion; characterize O/X/Y support boxes

- Verified commit `b040b29bc65417eebac65d983211c7309b1acad1` on the exact PR head. All four workflows succeeded: push Lean [40805240750](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40805240750), PR Lean [40805246864](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40805246864), push Python 3.11/3.12 [40805240669](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40805240669), and PR Python 3.11/3.12 [40805246921](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40805246921). Both fast and slow test stages passed.
- Added in `FinalTilde.lean` three support-characterization theorems: `sgK_radius_two_support_O_box_iff`, `sgK_radius_two_support_X_box_iff`, and `sgK_radius_two_support_Y_box_iff`. They express membership in the actual `sgK_radius_two_support` at level `m+1` by the corresponding parent vertex in the A/B/C corner box at level `m), while preserving the outer copy label and the individual spin index.
- This is the geometric support-reindexing interface only. It does not establish equality of any matrix entry, equality of the weights in the K²/K³ path sums, or `R_(m+1)=R_m`. CI for the new source SHA is pending.
- Next: use these characterizations to construct actual finite-state reindexing maps, then prove preservation of all entries along the two- and three-step paths. For outer copy C, keep the `oCo` / `oTil` orientation explicit; verify the full vertex-degree and face-axis factors. Do not move to p=8/p=10.



## 2026-10-29 — Fix Lean typing in the O/X/Y support characterization

- Lean CI for `8df96452409093943b23660986fbe9a80a6824e2` failed in `FinalTilde.lean`. The full PR build log identified a malformed pair type annotation in the O theorem and a membership-type mismatch at calls to the O/X/Y coordinate-box lemmas.
- Corrected the point annotation to `((0, 0) : Point)` and explicitly converted subtype membership in `(vertexOrder (m+1)).toFinset` to list membership using `List.mem_toFinset.mp` before calling `corner_O_radius_two_transport`, `corner_X_radius_two_box_iff`, and `corner_Y_radius_two_box_iff`.
- This commit only repairs parser/elaboration errors in the three existing support-characterization proofs. No statement or mathematical target was added or strengthened.
- CI for the correction is pending. Once the full Lean build and Python 3.11/3.12 push and PR workflows are green, continue with entrywise K²/K³ path-weight transport. Do not claim `R_(m+1)=R_m` yet.



## 2026-10-29 — Finish Finset-to-list conversion in the support bounds

- The next Lean build after the prior correction still failed at two `vertexOrder_sum_le` calls. The log showed that these lemmas also expect list membership, whereas the `Pt` subtype stores membership in `(vertexOrder (m+1)).toFinset`.
- Converted the two remaining premises with `List.mem_toFinset.mp`; this is a typing repair only, with no change to any theorem statement.
- CI for this fix is pending. No additional mathematical result is claimed.

## 2026-10-29 — Verified status of the radius-two support fix

- Rechecked PR #9 and branch `moment-6-8-10`; the source head was `10f0a24b562527070930e07f67c203caaae40e13` and PR #9 remained open against `main`.
- At this exact source SHA, all four configured Actions workflows completed successfully: push Lean [40807729515](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40807729515), PR Lean [40807735639](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40807735639), push Tests [40807729529](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40807729529), and PR Tests [40807735615](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40807735615). Both Lean jobs passed `Build formalization`; Python 3.11 and 3.12 passed both `Fast tests` and `Slow tests (level 7 convergence, ~1-4 min)`.
- This validates the two final Finset-to-list typing repairs in commit `10f0a24b562527070930e07f67c203caaae40e13`. Earlier entries saying that CI was pending describe the state at their respective handoff points; they are retained as history and are superseded by this verified result.
- No new mathematical claim was added: the support characterization is still only geometric. It does not prove entrywise weight preservation, equality of the finite weighted path sums, or (R_{m+1}=R_m).
- Next: derive and prove the concrete corner-dependent correspondence for the supported intermediate states, then establish preservation of each matrix-entry factor before reindexing any weighted sum. Keep the actual `sgGlue` pairings and the `oNum`/`oTil` orientation distinctions explicit; do not infer residual stability from support membership alone.

## 2026-10-29 — O-corner support reindexing

- Added `sgK_radius_two_O_parent_support` and `sgK_radius_two_support_O_equiv` in `FinalTilde.lean`. The equivalence maps the finite radius-two support about an O corner at level (m+1) to the parent-level O coordinate box, keeping the outer copy and spin state fixed.
- The forward map uses the existing `sgK_radius_two_support_O_box_iff`; the inverse uses membership of the old coordinate in `vertexOrder m) and the A-copy inclusion into `vertexOrder (m+1)`. This is an actual finite-state reindexing, not merely a support predicate.
- Scope: O corner only. No matrix-entry or powered-matrix weight preservation is asserted, and this does not prove (R_{m+1}=R_m). CI for this source change is pending.
- Next: build the corresponding X/B and Y/C state-set equivalences; then prove preservation of each entry factor under the appropriate A/B/C orientation transport before reindexing weighted path sums.

## 2026-10-29 — Diagnose and repair the O-corner support proof

- The full logs for both Lean failures on `16d3e702db22a9a6616c3827c9fb48deb9b09575` point to the same first error: `FinalTilde.lean:1225:4`. The `change` tactic tried to replace membership in `sgK_radius_two_O_parent_support` by its defining conjunction, but that membership is not definitionally equal to the conjunction until the filtered-Finset membership is simplified.
- Replaced that brittle `change` with the explicit simplification `simp only [sgK_radius_two_O_parent_support, Finset.mem_filter, Finset.mem_univ, true_and] at hparent`. This is a proof-elaboration correction; theorem statements and the intended finite-state equivalence are unchanged.
- Failed runs: push Lean [40813572235](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40813572235) and PR Lean [40813578252](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40813578252). Both report the same line-1225 error. CI for this correction is pending.
- Do not continue to X/B or Y/C until the corrected full Lean build and the Python 3.11/3.12 push/PR workflows have been inspected. No matrix-weight preservation or (R_{m+1}=R_m) claim is made.

## 2026-10-29 — Verify O-corner fix and add the X-corner support equivalence

- Verified the correction commit `f1e769c84767b1f22c6d9c57dee157cdfde08e5f`: all four workflow runs passed. Full Lean build: push [40814012354](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40814012354), PR [40814017964](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40814017964). Python 3.11/3.12 fast and slow tests: push [40814012438](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40814012438), PR [40814017942](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40814017942).
- Added `sgK_radius_two_X_parent_support` and `sgK_radius_two_support_X_equiv` to `FinalTilde.lean`. The map uses the explicit inverse of the B-copy shift, and the existing X-box characterization to prove the parent coordinate belongs to `vertexOrder m`; the inverse uses the existing B-copy map into `vertexOrder (m+1)`.
- Scope is still geometric: the equivalence preserves the copy label and spin, but does not establish any `sgK` matrix-entry equality or weighted path-sum equality. CI for the new source SHA is pending; do not continue to the Y/C case until the exact-SHA Lean and Python results are checked.

## 2026-10-29 — Fix existential elimination in the X-corner equivalence

- The current PR-head Lean logs failed at `FinalTilde.lean:1296:27` inside `sgK_radius_two_support_X_equiv`. The proof used `rcases` to extract the witness from an existential proposition while constructing a value in a subtype (Type). Lean correctly rejects eliminating `Exists` into data.
- Replaced that extraction by `Classical.choose hz.2` for the witness and `Classical.choose_spec hz.2` for its proof, then destructured only the resulting proposition. The X-equivalence statement and its intended witness are unchanged.
- Failing Lean runs on the inspected head: push [40831707714](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40831707714), PR [40831712607](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40831712607). This is the only reported Lean error in those logs; new-SHA CI is pending.
- Do not extend to Y or matrix-weight transport until the full Lean build passes on the corrected SHA. No level-stability claim is made.

## 2026-10-29 — Return to the last fully green Lean source

- Rechecked the exact CI records before proceeding. The last source checkpoint with all four workflows green is `f1e769c84767b1f22c6d9c57dee157cdfde08e5f`: push Lean [40814012354](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40814012354), PR Lean [40814017964](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40814017964), push Python [40814012438](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40814012438), and PR Python [40814017942](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40814017942) all succeeded.
- The subsequent X-corner support-equivalence experiment added 92 lines in `FinalTilde.lean`; the full Lean build failed on the Type-valued witness construction, and the follow-up `Classical.choose` change was not sufficient to make the build pass (PR Lean [40832302467](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40832302467), push Lean [40832296890](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40832296890)).
- Removed that unverified X-corner equivalence from the source, restoring `FinalTilde.lean` to the exact green-checkpoint content at `f1e769c...`. The O-corner equivalence remains because it compiled at that checkpoint. The log history is retained; this entry records why the X experiment was rolled back.
- Next work must start from this known-green source and target matrix-entry/weight preservation needed by the p=6 residual. Do not add another support-only equivalence before specifying the concrete matrix-weight identity it is intended to enable. CI for the rollback commit must be checked before any further Lean edits.

## 2026-10-29 — p=6 closure plan from the verified green checkpoint

- Verified rollback checkpoint `e561dea2c14260be9a5baf69cc1f18c92b68b0a5`: push/PR Lean and push/PR Python all succeeded. `FinalTilde.lean` is byte-identical to the successfully compiled `f1e769c...` source.
- Freeze the mathematical target: prove adjacent-level invariance of `glueRHS6_highPowerResidual` for `sgK m θ faceAxis (oNum (m+1))` versus the constant-axis operator. Do not start another stand-alone geometry/support lemma unless it directly supplies one of the finite-sum reindexing obligations below.
- The following steps are already established and must be reused: `defectO6_orientation_difference_eq_level3`; `defectO6_succ_num_level3`; `glueRHS6_highPowerResidual_sgK_radius_two_path_expansion`; `sgK_pow_two_entry_zero_outside_radius_two`; and `pHeO_corner_O/X/Y_box_entry_next_num`. The p=6 residual is the only remaining level-dependent term in the affine recurrence.
- Planned dependency order: (1) prove a correct correspondence between the glued states at levels (m+1) and (m), preserving copy, spin, and the partner map `sgGlue.σ`; (2) explicitly pull radius-two support states back using identity at O and inverse B/C coordinate shifts at X/Y; (3) lift the existing entrywise corner transport to the `K²` and `K³` factors in the finite path sums; (4) use the explicit path expansion and finite-sum reindexing to prove `R_{m+1}=R_m); (5) combine with `defectO6_succ_num_level3` and `affine_three_recurrence` to close the all-level p=6 recurrence.
- The earlier X-equivalence attempt failed because it eliminated an existential proposition into Type while building a subtype. Do not repeat that pattern: define the pullback coordinates explicitly and do witness elimination only inside Prop-valued membership goals, or prove the required sum identity directly without constructing a Type-valued equivalence.
- Keep C's `oCo` orientation explicit. The existing corner entry theorem maps Y/C to `oTil`, not to `oNum`; do not erase that distinction.
- The Python exact polynomial check of the p=6 residual at levels 3 and 4 is a finite computational certificate, not an all-level Lean proof. Keep separate the (a) all-level residual-stability theorem and (b) optional explicit trigonometric evaluation of its finite base value.

## 2026-10-29 — Explicit-coordinate X support equivalence for residual reindexing

- Added `sgK_radius_two_X_parent_support` and `sgK_radius_two_support_X_equiv` to support the planned finite-sum reindexing of the p=6 high-power residual. The inverse uses the explicit coordinate `(x - 2^m, y)), and the forward map is the B shift `shiftPoint (2^m) 1 0`.
- Unlike the failed experiment, no existential witness is eliminated into a value in `Type`. The existential from `sgK_radius_two_support_X_box_iff` is unpacked only inside proofs of propositions (parent vertex membership, coordinate bounds, and point equality); the point used to construct the subtype is computed directly.
- This is a proof-planned prerequisite for applying a finite-sum bijection to the inner radius-two path sums. It does not assert entrywise equality of (K^2/K^3), residual stability, or p=6 closure. CI for the new source SHA is pending.
- Next after a clean build: prove the matching state map commutes with the glued partner `sgGlue.σ`, and lift the existing corner entry equalities to the specific powers in the two residual sums. The Y/C map must keep `oCo`/`oTil` explicit.

## 2026-10-29 — Fix product equality and reduce the X inverse composition

- Inspected both full Lean logs for `b70fd6677ab6b82c88135de9ea32c7a55340173e`. The first failure at `FinalTilde.lean:1358` followed simplification of a pair equality; `constructor` was not a valid tactic for the remaining goal. It is now decomposed explicitly with `Prod.ext`, proving the x-coordinate with `omega` and the y-coordinate by reflexivity.
- The second error at line 1366 occurred in `right_inv`: the proposed `change` did not match the unreduced composition `toFun (invFun z)`. Added `dsimp` after descending to the point subtype equality, before the coordinate-level `change`. The inverse coordinate arithmetic itself remains unchanged.
- Failed runs reviewed: push Lean [40835853136](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40835853136), PR Lean [40835863641](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40835863641). No matrix-weight or residual-stability theorem was claimed. CI for this repair is pending.

## 2026-10-29 — Reduce the shifted-coordinate expression in X right inverse

- The next full Lean build isolated the remaining X-equivalence issue to `FinalTilde.lean:1368`. After `dsimp`, the goal retained projections of `shiftPoint (2^m) 1 0 p`; the coordinate-level `change` incorrectly assumed those projections had already reduced.
- Replaced the mismatched `change` with `simp [shiftPoint, Nat.add_sub_cancel_right]` on the actual goal. This directly unfolds the shifted coordinates and cancels the added/subtracted (2^m); no definition or mathematical claim changed.
- Failing runs reviewed: push Lean [40836229850](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40836229850), PR Lean [40836234409](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40836234409). CI for this correction is pending.

## 2026-10-29 — Y/C support equivalence on the verified X checkpoint

- Before this change, all four workflows were green on the exact source SHA `0ce5f8f4d65e796e9b86d9a8bdb81062047f6860`: push Lean [40836563072](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40836563072), PR Lean [40836569337](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40836569337), push Python [40836562916](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40836562916), and PR Python [40836569344](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40836569344), including fast and slow tests on both Python versions.
- Added `sgK_radius_two_Y_parent_support` and `sgK_radius_two_support_Y_equiv`, the C-shift counterpart to the compiled X/B equivalence. The inverse point is explicit: `(x, y - 2^m)); the forward map is `shiftPoint (2^m) 0 1). Existence witnesses are unpacked only in Prop-valued goals.
- Scope: geometrical support correspondence only. It does not identify `sgK` entries or powers and does not prove (R_{m+1}=R_m). The new SHA's full Lean build and Python push/PR workflows must pass before the next change.
- Next: make the three O/X/Y support equivalences serve one concrete purpose: reindex the finite (K^2/K^3) path sums, proving the entrywise transfer needed for (R_{m+1}=R_m). Preserve the actual C-copy `oCo`/`oTil` orientation.

## 2026-10-29 — Verify Y/C support reindexing and select the next p=6 proof obligation

- Verified PR #9 head `e72f4634fb59d88555eaa279e606012dbd495979` (commit: `Add explicit Y-corner support reindexing`). The PR remains open on `moment-6-8-10`; no new branch, PR, or issue was created.
- At this exact SHA, PR Lean run [40838416882](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40838416882) passed its complete configured `Build formalization` step. PR Tests run [40838416691](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40838416691) passed fast and slow tests on Python 3.11 and 3.12.
- The Y/C support equivalence now compiles alongside the O/A and X/B support correspondences. These are finite-state/support reindexings only. They do not establish preservation of the `sgK` matrix weights, the `K^2/K^3` path factors, or adjacent-level residual stability.
- Next proof obligation remains the p=6 residual identity, not another support lemma: transport the exact short-path matrix-entry products across the three corner copies, keeping the C-copy orientation `oCo` explicit, and then reindex the inner path sums and outer `sgGlue` sum. Only after that identity is proved may the affine recurrence be closed. Do not claim p=6 closure, and do not switch to p=8/p=10.


## 2026-10-29 — Reduce the p=6 residual to corner-power sums

- Starting source SHA `94f86686314b7d1d9fbb1780f477b9fc09dc3ea8` has a successful full PR Lean build (run [40848277996](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40848277996)) and successful Tests workflow (run [40848278170](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40848278170), Python 3.11 and 3.12).
- Added uniform degree-two lemmas for the O/X/Y outer corners and derived that every state in `sgGlue m` has underlying point degree two.
- Added a generic algebraic reduction under the exact diagonal hypotheses `K x x = 2` and `(K^2) x x = 6` on glued states. The concrete `sgK` corollary proves those hypotheses from `sgK_diag` and `sgK_sq_diag`.
- The residual is now expressed exactly as `12 * (Σ_g K^5(σx,σx) - Σ_g K'^5(σx,σx)) + 36 * (Σ_g K^4(σx,σx) - Σ_g K'^4(σx,σx))`. The partner map is deliberately retained, ready for the existing `sgK_root_pullback_sigma) compatibility theorem.
- Scope: this is an exact algebraic reduction, not the all-level identity `R_{m+1}=R_m`. The remaining proof must compare these power-4 and power-5 diagonal sums across the rooted radius-two corner maps, including recursive axis labels and the C-copy exceptional orientation. New-SHA CI is pending.



## 2026-10-29 — Prove the outer glued-root reindexing interface for p=6

- Starting SHA `db3d626ca21012bf9ade7d60df47d8b4fafbdcc2` had successful Lean push/PR builds and successful Python push/PR test workflows.
- Added `glueRHS6_glued_partner_power_sum_transport`: a finite-sum reindexing lemma on the subtype of glued states, using the existing equivalence `sgK_glued_root_equiv` and the crucial compatibility theorem `sgK_root_pullback_sigma`.
- Added `glueRHS6_highPowerResidual_eq_of_corner_power_transport`. It combines the already-proved diagonal reduction with four pointwise transport hypotheses (powers 4 and 5 for each of the two operators) to derive the exact adjacent-level residual equality. It deliberately does not assert these local power equalities.
- This isolates the remaining mathematical core: prove the fourth- and fifth-power diagonal entries agree under the explicit root pullback on every glued partner root, for the concrete face-axis and constant-axis operators. The theorem is a sum-reindexing bridge, not yet the all-level p=6 closure.
- New commit CI must finish its full Lean build; Python results are checked but do not gate further mathematical analysis.


## 2026-10-29 — Fix the first outer-sum bridge elaboration failure

- Commit `3c336ea123d0a2f54045f7ca34d1a153e28c97ea` failed both Lean builds at the conversion between a conditional sum and a glued-state subtype sum, at `FinalTilde.lean:2008` and `2025`. The diagnostic was `simp made no progress` with an ill-typed intermediate involving `(Ahi ^ n) ((sgGlue ...).σ w)`; the same error appeared for `Alo).
- Replaced the two broad `simp` conversions with the dedicated lemma `glueRHS6_sum_ite_eq_subtype`, proved directly from `Fintype.sum_subtype_add_sum_subtype`. The summand is passed as an opaque function, so this step only converts the index set and does not unfold matrix powers.
- This correction does not change the residual theorem, power-entry hypotheses, or mathematical scope. The next CI result must confirm that the entire Lean formalization builds; no further theorem expansion is justified before that result.


## 2026-10-29 — Repair subtype-sum proof after the 8b6ce39e Lean failure

- Source checkpoint: `8b6ce39ee047c5a10a51bfb331890eb9daf453ae`.
- Both full Lean workflows failed on that exact checkpoint: push run [40854423177](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40854423177) and PR run [40854431160](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40854431160). The first compiler error was `FinalTilde.lean:2000:16: simp made no progress`.
- Replaced the generic final `simp` in `glueRHS6_sum_ite_eq_subtype` with explicit `Finset.sum_congr` and `if_pos x.2` on the positive subtype, plus `Finset.sum_eq_zero` and `if_neg x.2` on the negative subtype. The remaining `+ 0) is closed by `add_zero`.
- The theorem statement and mathematical scope are unchanged. This only proves the finite index-set conversion; it does not prove the fourth-/fifth-power transport or `R_{m+1}=R_m`.
- CI for the correction is pending; no success is claimed before inspecting the new SHA's full Lean build and the four push/PR workflows.
- Next: first verify this patch with the complete configured Lean build. If Lean passes, continue with the already identified local matrix-power-entry transport; if it fails, repair the first new Lean error before further source changes.


## 2026-10-29 — Green Lean checkpoint and exceptional X-corner orientation transport

- Verified checkpoint `7d98683340576aac241ac4b1d59a7f04595c8da4`: full configured Lean builds succeeded on push [40855695124](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40855695124) and PR [40855702564](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40855702564). Python push/PR workflows for this SHA were still running when work continued; no Python success is claimed here.
- Continued immediately after the green Lean result, without waiting for Python. Added `pHeO_corner_X_box_entry_next_til` in `FinalTilde.lean): the same geometric B-corner transport as the existing numbering-orientation lemma, but with the exceptional `oTil` orientation preserved explicitly.
- The proof uses the existing local B-entry identity and the already-established `faceB` / `cp1_shiftB` transport to show the flipped edge maps to the flipped parent edge; reverse edge orientation is handled via `OAnti). It does not assume `oTil = oNum) at X.
- This is a necessary local entry lemma for the C/Y-copy exceptional-orientation case, not yet a power-4/power-5 identity. The new SHA's full Lean build is pending.
- Next: if Lean passes, lift the per-edge transport to the concrete `sgK) base-entry identity under the O/A, X/B, and Y/C support equivalences, then use finite path sums to transport powers 4 and 5. If it fails, fix the first real Lean error before extending the proof.


## 2026-10-29 — Correctly indexed X-corner transport for the tilde recurrence

- Verified that commit `07db1fb3a891b738429b4c08d4ccbcd6779dc99d` passed both full Lean builds: push [40856810849](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40856810849) and PR [40856818445](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40856818445). Python push/PR were still in progress; they did not gate continued analysis.
- Inspection of the residual theorem's actual indices shows the adjacent-level comparison needs the high entry at orientation `oTil (m+2)` and the parent entry at `oTil (m+1)`. The previously added local lemma `pHeO_corner_X_box_entry_next_til` concerns the unshifted sequence `oTil (m+1)` to `oTil m`; it is valid but does not itself match the residual theorem's indices.
- Added `pHeO_corner_X_box_entry_next_til_num` for the correctly indexed pair. It first restricts the high `oTil (m+2)) orientation to `oNum (m+2)) on vertices of level `m+1), transports the X box through the B shift, then explicitly identifies the pulled-back B orientation with `oTil (m+1)) on the parent graph.
- This repairs an index alignment dependency only. It is still a local entry theorem, not an equality of powers four/five or a proof of residual stability. Current-SHA Lean CI is pending.


## 2026-10-29 — Formalize the exact local-entry-to-power-4/5 transport

- Verified SHA `f388e6209c76900f442fd65b8146414bd0c2b719`: both full Lean builds passed, push [40858042644](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40858042644) and PR [40858050896](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40858050896). Python push/PR remained in progress and was not awaited.
- Added `matrix_pow_four_five_diag_transport_of_local_entries`, an abstract finite-matrix lemma that derives equality of the fourth- and fifth-power diagonal entries from: (i) a bijection of finite supports around the two roots, (ii) one-step entry equality on all support pairs, and (iii) first- and second-power root row/column vanishing outside those supports.
- Power four is handled through `K^4=K^2K^2); power five uses `K^5=K^2K^3) and `K^3=K K^2). Every reindexing is via the supplied support equivalence; no matrix entry outside a proved support is silently discarded.
- This is a generic path-transport mechanism, not yet an instantiation for `sgK). The remaining concrete obligation is to establish the one-step `sgK) entry equality for all pairs in each corner support under the relevant orientations/axis periodicity, and discharge the support hypotheses with the existing locality lemmas.
- New-SHA full Lean CI is pending. If it fails, fix the first error before applying this theorem or adding further proof steps.


## 2026-10-29 — Fix first Lean failure in local power-4/5 transport abstraction

- Commit `df4ae643b6944d91b983e3c1ee1435069f5e03c8` failed full Lean push build [40859099659](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40859099659); the PR Lean run [40859108178](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40859108178) was still running at first inspection.
- The concrete errors were Fintype-instance mismatches: the generic helper emitted sums over predicate subtypes using `Subtype.fintype`, while the theorem's finite-support sums were elaborated using `Finset.Subtype.fintype S`. Subsequent `K^3) rewrite failures came from the same type instability in the surrounding goals.
- Added `glueRHS6_sum_ite_eq_finset_subtype`, explicitly bridging to the canonical finite-set subtype `S), changed the support equivalence to `S ≃ T), and changed every path sum to use those canonical finite-set subtypes. Replaced the brittle inline `rw) for `K^3=K*K^2) with a named matrix-power equality.
- This is a proof-engineering correction to the generic path transport only. The concrete `sgK) local-entry hypotheses and all-level residual stability remain open. CI for the correction is pending.


## 2026-10-29 — Repair second Lean failure in the abstract path-transport theorem

- Full Lean push [40859648802](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40859648802) and PR [40859654599](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40859654599) failed on `969085624e95167efe13f5b45341f97c03b4acba`.
- The first errors were in the newly added helper for finite-set subtypes: `S) cannot be used as a type in the locally constructed equivalence, because the intended subtype instances were not definitionally aligned. This cascaded into the unknown helper constant and multiple sum-type mismatches.
- Removed that helper and restored a single consistent representation for each support throughout the generic power-transport theorem: predicate subtypes `{x // x ∈ S}` and `{y // y ∈ T}`, with the corresponding `Equiv). Every restricted power sum and each `Equiv.sum_comp) now use those same predicate-subtype types as `glueRHS6_sum_ite_eq_subtype`.
- Kept the `K^3 = K * K^2) equality as a named rewrite to avoid the prior malformed inline rewrite. This patch only repairs the abstract matrix proof and does not yet instantiate concrete `sgK) entry transport. New Lean verification pending.


## 2026-10-29 — Audit correction: remove the uncompiled, uninstantiated K^4/K^5 abstraction

- Audited HEAD `3f269fde2703e8fa2af9b152375223f7e7910470` against full Lean push [40860870487](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40860870487) and PR [40860879153](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40860879153). Both failed at the newly added `matrix_pow_four_five_diag_transport_of_local_entries` block (lines 2211, 2225, 2239, 2253, 2300, 2314, 2343, 2360, 2391, and 2405).
- Root cause: the generic sum-conversion theorem uses the predicate-subtype Fintype instance, while sums in the local goals resolve the canonical `Finset.Subtype.fintype S`; these terms are not definitionally equal. The attempted replacement did not solve that instance mismatch and additionally left `Equiv.sum_comp e (fun z : T => ...)` forms where `T` is a Finset, not a type.
- The audit confirmed this private block was not used to prove any concrete `sgK) power entry or the residual bridge. It was infrastructure with unproved concrete hypotheses, not progress on `R_{m+1}=R_m`.
- Removed only the new generic block; preserved the previously compiled corner/support/orientation lemmas and retained the earlier failed attempts in this log. This returns `FinalTilde.lean` to the last known green source state at checkpoint `f388e6209c76900f442fd65b8146414bd0c2b719` while preserving chronological journal history.
- Next step after green Lean verification: formulate the concrete map between each glued partner root's high-level and parent-level `sgK) support. Prove one-step entry preservation for same-copy state pairs for O/A, X/B, and Y/C with axis periodicity and exact orientations; only then derive the two path sums. Do not reintroduce a generic power lemma until its finite-sum types have been validated and its concrete hypotheses can be instantiated immediately.


## 2026-10-29 — Add the actual-tilde O-box entry transport after green Lean

- Starting checkpoint `2bf84fea6a42708a84f6d701075c17d64663d99c` was verified green in full Lean push [40861768230](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40861768230) and Lean PR [40861775093](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40861775093).
- Added `pHeO_corner_O_box_entry_next_til` immediately before the existing X-box entry transport. Its statement matches the adjacent-level residual indices: high operator level `m+1) with orientation `oTil (m+2)), low operator level `m) with orientation `oTil (m+1)).
- The proof explicitly excludes `cp1) in both directions from the O box bounds `x≤2), first at level `m+2) and then `m+1). Thus `oTil) is equivalent to `oNum) at both levels; it composes the existing `pHeO_corner_O_box_entry_next_num` equality with `pHeO_rel_congr`. It adds no assumptions and does not claim any power-entry equality.
- This is a local O/A point-entry result only. The one-step `sgK) equality for the paired whole state spaces, the B/C cases, and powers 4/5 remain open. Full Lean CI on the new SHA is pending.


## 2026-10-29 — Fix failed O-box tilde transport proof

The Lean build for `3fec4bd1c1e02b1f2c16ab146c46b48b7c434e03` failed at the new O-box lemma for two concrete reasons: the power bound was too weak, and the higher-level `pHeO_rel_congr` was unavailable in this module's imports. The follow-up commit `1b99dc16f912bce2fe04cd65c6ee26fcbd7afc09` changes the bound to `4 ≤ 2^n` and adds a private local congruence proof using the low-level diagonal, edge, and non-edge lemmas already in the dependency chain. New SHA CI is pending; do not proceed to other transport cases until the Lean build is green.


## 2026-10-29 — Revert unverified O-box tilde entry lemma

The O-box `pHeO_corner_O_box_entry_next_til` was removed after the full Lean build failed on the follow-up SHA. The fresh CI log showed two invalid `calc` steps (the proof stated `4 ≤ 2^n` but started its chain at `3 ≤ 2^3`) and a remaining reference to unavailable `pHeO_rel_congr`. Rather than continue layering unverified patches, `FinalTilde.lean` was restored exactly to the verified source blob from green checkpoint `2bf84fea6a42708a84f6d701075c17d64663d99c`. This does not solve the transport problem; it restores the known-good geometry checkpoint before a redesigned proof attempt.


## 2026-10-29 — Y-corner transport compiles; add A-block X wrapper

- Full Lean push and PR builds passed on `3f4dd54e0278f95b44f093eb59f64467a304e5b4` after correcting the Y/C transport's `cp1_not_A` side-condition and packing parent witnesses into `Pt m`. Python tests on that SHA were still running at the time of this update.
- Added `sgK_A_X_entry_next_til`, a state-index wrapper around the already-proved `pHeO_corner_X_box_entry_next_til_num`. Parent states are bundled as `Pt m`, avoiding a dangling membership proof in the result type. The lemma applies to the A block and does not claim power-diagonal transport.
- The next proof target remains the equality of fourth/fifth-power diagonal entries at glued partner states; all pointwise one-step entries needed across every outer copy and corner still have to be assembled before the power reindexing can be justified.


## 2026-10-29 — Fix X-wrapper declaration order after CI failure

- CI for `0bae1cddee6886964fb48b69cd4fb3220868df23` failed because `sgK_A_X_entry_next_til` appeared before `pHeO_corner_X_box_entry_next_til_num`, the theorem it calls. The theorem is present later in the same file; Lean processes declarations sequentially, so this was a source-order error, not a failed mathematical premise. The subsequent `rcases` error was cascading from the unresolved identifier.
- Moved the state wrapper below the complete X point-entry theorem. No proof term or theorem statement was changed; only declaration order changed. The exact failing SHA is preserved in commit history. New full Lean CI is pending.


## 2026-10-29 — Add C-block O-corner entry transport

- Previous green checkpoint: `577d627912f51e5030a4827cd6e0afcb8efeb1c2` passed both full Lean workflows. The C-block was the remaining outer-copy case at the O coordinate box.
- Added `pHeO_til_eq_num_same_index`, the same-level counterpart of the existing `pHeO_til_eq_num_of_level_domain`. It follows directly from `cp1_not_A) on every edge in the level-n graph.
- Added `sgK_C_O_entry_next_til`. Its high and low C-copy orientations are converted using `cp1_shiftC) and the already-proved `Hc_C_num_eq_parent_til`; the O-box entry transport then handles the level change. This proves only a one-entry transport in the C block, not yet any fourth/fifth power equality.
- Full Lean verification on this new SHA is pending; do not add power-sum claims until it passes.


## 2026-10-29 — Correct the C/O transfer's orientation scope

- The full Lean build for `5432adb45c528017f44921820a74a4de66000fb4` failed at three places in the newly added C/O lemma. Source review found a genuine logical overgeneralization: the helper `pHeO_til_eq_num_same_index` asserted global agreement of `oTil n` and `oNum n) on level-n entries, but `cp1 n` can be an actual edge at that level, so the statement is not justified.
- Removed that false global helper. The C/O proof now changes `oTil) to `oNum) only for endpoints inside the O radius-two box, invoking `cp1_not_O_radius_two` at levels `m) and `m+1). Also supplied `by omega` where `Hc_C_num_eq_parent_til` requires `1 ≤ m`, rather than incorrectly passing `3 ≤ m`.
- The proof still uses the existing shifted-C exclusion `cp1_shiftC` for the copy wrapper and `Hc_C_num_eq_parent_til` for the actual C orientation. This is narrower and mathematically correct; new SHA full Lean verification is pending.


## 2026-10-29 — Add C/X entry transport after green checkpoint

- Checkpoint `7cbfc568d479708a59dd8bbde6d9349c76fb7be4` has both Lean workflow runs and both test workflow runs green.
- Added `sgK_C_X_entry_next_til` for the C-copy at the X corner. It uses the existing X-box tilde transport for the point-level operator and the existing `Hc_C_num_eq_parent_til` theorem on both levels. The only `oTil)-to-`oNum) changes are across a C-shift, justified by `cp1_shiftC`, so this does not assume the exceptional edge is absent globally.
- This fills the C/X side of the glued B/Y–C/X pair; the B/Y state transport is still missing. The proof is local to the radius-two X box and does not yet prove the fourth/fifth-power diagonal transport. New-SHA full Lean CI pending.


## 2026-10-29 — Pre-empt lower-level C/X bound mismatch

The C/X transport uses `Hc_C_num_eq_parent_til` at the parent level `m). Its precondition is `1 ≤ m`, while the theorem's available bound is `3 ≤ m`; these propositions are mathematically compatible but not accepted as a direct argument by Lean. Replaced the argument by `by omega` before relying on a failed build. This is a proof-typing correction; the orientation argument remains restricted to C-shifted points via `cp1_shiftC`. New SHA CI is pending.


## 2026-10-29 — Fix C/X wrapper declaration order

The full Lean build for `acd33bc3465cc21367034412e852b662d74a5272` failed because `sgK_C_X_entry_next_til` referenced `pHeO_corner_X_box_entry_next_til` before it was declared. Moved the state wrapper after its point-level dependency, without changing the theorem statement or proof term. The failure was declaration order, not an orientation mismatch. Re-running both full Lean workflows on the new SHA before the B/Y step.


## 2026-10-29 — Preserve X-box endpoints in the C/X wrapper context

The CI log for `b32e3c7f26282933f6894044a13821c1aa09ce21` showed the C/X wrapper using `p) and `q` after an `rcases ... with ... rfl, rfl` pattern had substituted those variables away. Changed the destructuring to retain the equalities as `hpEq) and `hqEq), and returned those equalities with the parent-state witnesses. The underlying point-entry theorem and orientation argument are unchanged. Re-run full Lean CI on the new SHA.


## 2026-10-29 — Add B/Y state transport for the third glued-root pair

- Added `sgK_B_Y_entry_next_til` using the green-checkpoint point-level Y/C transport together with the B-copy orientation facts `oBo_num_iff_oNum`, `oNum_succ_restrict`, `cp1_shift`/radius-two edge exclusions.
- The proof converts orientations only where the exceptional edge is excluded by the local coordinate bound or B-shift geometry; it does not assert global equivalence of `oTil) and `oNum).
- This is the final missing one-entry bridge among the six sides of the three gluing pairs (A/X↔B/O, A/Y↔C/O, B/Y↔C/X). After full Lean verification, the next step is to use the six bridges on radius-two neighborhoods to prove the fourth/fifth-power diagonal transports required by `glueRHS6_highPowerResidual_eq_of_corner_power_transport`. New SHA CI pending.


## 2026-10-29 — Correct the parent-level bound in B/Y transport

The Lean log for `4eb6890bc027c1498b2d97cdfc7b7cb9da8a3698` reported one error: `cp1_not_A` expects `1 ≤ m), but `sgK_B_Y_entry_next_til` passed `hm : 3 ≤ m` directly. Replaced the argument with `by omega`; no other Lean errors were reported in this run. Full Lean CI is restarted on the new SHA.


## 2026-10-29 — Generic finite-neighborhood transport for fourth/fifth diagonals

- The full Lean push and PR builds passed on `b146f3f5d40c9760390dd5961d8492921dc391f6`; Python tests were still running.
- Added `finset_sum_eq_subtype_of_zero_outside` and `matrix_pow_four_five_diag_eq_of_local_equiv`. The latter is the planned algebraic bridge: it expands `K^4) as `K^2 K^2) and `K^5) as `K^2 K^3), restricts sums to the radius-two supports, compares `K^2) rows/columns and `K^3) columns from one-step entry equality, and reindexes with the given finite equivalence.
- The theorem assumes explicit zero-outside bounds for one- and two-step rows/columns on both levels. These can be discharged from the existing glued-operator locality lemmas once the six corner-specific equivalences and entry transports are assembled. No cross-level power equality is claimed yet; this is a generic algebraic lemma. New SHA Lean verification pending.


## 2026-10-29 — Repair the generic p=6 power-transport helper's compile errors

- Parent SHA checked: `373773bcc96773381f5d712d503338f98c0ab027`.
- Both Lean workflows failed on that SHA: PR run [40884582419](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40884582419) and push run [40884571671](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40884571671). Both test workflows passed: PR [40884582469](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40884582469) and push [40884571466](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40884571466).
- Fixed the detached p=6 residual doc-comment by attaching it to `glueRHS6_highPowerResidual_eq_of_corner_power_transport`, rather than placing a second doc-comment immediately after it.
- Addressed the exact `Fintype` mismatch: `glueRHS6_sum_ite_eq_subtype` enumerates the predicate subtype with `Subtype.fintype`, while the finite-support target uses `Finset.Subtype.fintype S`. The helper now proves the two `Finset.univ` enumerations equal extensionally before applying the generic conversion; no matrix-entry assumption is changed.
- This is a compile repair for a conditional algebraic lemma. It does not yet instantiate the radius-two supports, prove concrete fourth/fifth-power transport for `sgK`, or close the sixth-moment residual.
- **Next:** inspect both Lean workflows on the resulting SHA. Do not proceed to support instantiation until both full Lean builds pass; then derive and verify the concrete `h4/h5` hypotheses.


## 2026-10-29 — First concrete fourth/fifth-power diagonal transport specialization

- On SHA `65a7bab622bb6f726cd2dff8cd48f6cf39d5532f), both full Lean workflows succeeded: [push](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40888848540) and [PR](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40888859164). At log update time, the Python suites were still running; Python 3.12 had completed successfully in both push and PR runs.
- Added a concrete specialization of `matrix_pow_four_five_diag_eq_of_local_equiv` for the A-copy X corner. It assembles the existing X support equivalence, the checked `sgK_A_X_entry_next_til` bridge, and explicit first-/second-power zero-outside-support conditions. The proof does not assume arbitrary local matrix equality and does not infer power equality from entry equality without finite path-sum expansions.
- This is only the A/X case, not yet a theorem for every glued partner root. The analogous B/O, A/Y, C/O, B/Y, and C/X cases still need to be assembled, after which the result must be applied to `σ w` in the residual transport theorem.
- New push/PR Lean and Python workflows are pending on the current SHA.


## 2026-10-29 — Factor finite-support obligations and add the B/O endpoint

- Parent SHA: `1c54b6d076bee75a137e996172ea46c362eb9083`; both full Lean builds passed on that SHA: [push](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40891063250) and [PR](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40891073341). Python push/PR workflows were still running at the last status check.
- Added a common support-equivalence wrapper that discharges the one-step and two-step row/column vanishing conditions required by the already-proved finite matrix-power lemma. Its only extra premise is the explicit inclusion of the low-level radius-two support into the chosen parent support.
- Added the B/O endpoint specialization using `sgK_radius_two_support_O_equiv` and the existing `sgK_B_O_entry_next_til` local entry bridge. This is the partner side of the previously compiled A/X case.
- No arbitrary matrix equality or new graph/orientation assumption is introduced. The new endpoint is conditional on the existing local bridge and explicit support inclusion; the current SHA must pass both full Lean workflows before proceeding to A/Y and C/O.


## 2026-10-29 — Fix the B/O root normalization failures from Lean CI

- Failed PR Lean build: [run 40892622118](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/40892622118), on parent SHA `9ad7ea9007fb2a79d5ba5914abff09c3f3d97267`. The reported failures were all in `sgK_B_O_diag_four_five_transport`: the support membership proof, the root equality under the equivalence, and the two coordinate bounds for support inclusion.
- Cause: simplification did not discharge the conditional definition of `sgK_root_pullback_pt` at the O corner; it left `if 0 = 2^(m+1) then ...` expressions. The proof now invokes the existing `sgK_root_pullback_pt_O` lemma explicitly and derives the two zero-coordinate facts from it.
- Rebuilt `hwT`, `hroot`, and `hsubset` using those concrete coordinate equalities. This changes no mathematical assumptions and does not replace the local-entry bridge.
- **Gate:** check full Lean builds on the corrected SHA (push and PR) before adding any more corner cases. Then check the test workflow statuses. If Lean fails again, fix that failure first.


## 2026-10-29 — Add the C/O fourth/fifth diagonal transport case

- Parent SHA `c3428e6d7bf9bc7b4126e0185284b3a5b41e9cef` was verified green: full Lean build and Python 3.11/3.12 tests passed for both push and PR workflows.
- Added `sgK_C_O_diag_four_five_transport`, following the already-compiled B/O specialization but using the existing `sgK_C_O_entry_next_til` local entry bridge. The proof reuses the O-corner support equivalence, explicit `sgK_root_pullback_pt_O` normalization, and the shared finite-support power-transport wrapper.
- This is one endpoint case only. The remaining cases are A/Y, B/Y, and C/X. Both full Lean builds must pass on the new SHA before proceeding.


## 2026-10-29 — A/Y fourth/fifth diagonal transport specialization

- Parent SHA `aa66fdf8889e02c912f2b427e7ecac38d30ed5c2` passed the full Lean build and all Python 3.11/3.12 fast+slow tests for both push and PR workflows.
- Added `sgK_A_Y_diag_four_five_transport` using the already-proved Y-radius-two support equivalence and `sgK_A_Y_entry_next_til`. The proof explicitly inverts the Y shift by subtracting `2^m` from the y-coordinate, preserves x and spin, and supplies the finite-support one-/two-step vanishing obligations to the matrix-power identity.
- The endpoint keeps the existing axis-periodicity hypothesis `ax (2 * 3^m + k) = ax k`; no new matrix-entry assumption is introduced. This does not yet establish uniform `h4/h5`. Both full Lean builds on the new SHA must pass before proceeding to B/Y or C/X.


## 2026-10-29 — Add the B/Y fourth/fifth diagonal transport case

- Parent SHA `9b4fe9d98b749ed1de38bb8424d602ff42c3e03f` passed both full Lean builds (push and PR). The Python workflows were still running at the last check; they were not used as a gate for this Lean-focused step.
- Added `sgK_B_Y_diag_four_five_transport`, reusing the Y-radius-two support equivalence and the existing `sgK_B_Y_entry_next_til` bridge. The coordinate pullback subtracts `2^m` from y, preserving x and spin; the proof supplies the finite-support first-/second-power vanishing premises needed by the matrix-power lemma.
- No new mathematical assumptions were introduced. This handles B/Y only; C/X and applying the endpoint cases to the residual hypotheses remain.
- **Next gate:** inspect both full Lean build results on this SHA before adding C/X or wiring the `h4/h5` assumptions into `glueRHS6_highPowerResidual_eq_of_corner_power_transport`.


## 2026-10-29 — Correct the B/Y insertion boundary found by Lean CI

- The first B/Y commit `ca06a7b4b8d37c1696fcbe927d720d34a7f9996b` failed push Lean build because the insertion accidentally copied the trailing generic wrapper and B/O/C/O theorems a second time. CI reported only duplicate declaration errors for those three existing declarations; it did not report a type error in the B/Y proof.
- Removed only that duplicate tail. The original wrapper, B/O, and C/O declarations remain, as do both A/Y and B/Y specializations and the main high-power residual theorem.
- The current SHA must pass both full Lean builds before moving to C/X.


## 2026-10-29 — Add the C/X fourth/fifth diagonal transport case

- Parent SHA `22fd4b3eb77c4eb1bbe63eea23342c1cd00d4bb4` removes the duplicate declarations found in the first B/Y build. The earlier compiler log had reported only duplicate declarations after B/Y; the full build on the cleaned SHA was still running at the time of this edit.
- Added `sgK_C_X_diag_four_five_transport` using the existing `sgK_radius_two_support_X_equiv` and `sgK_C_X_entry_next_til`. It follows the already checked A/X construction, with the inverse X shift subtracting `2^m` from x, and keeps the same radius-two first-/second-power vanishing arguments.
- No new mathematical assumptions are added. This endpoint is not yet wired into the uniform `h4/h5` obligations of the residual theorem.
- **Gate:** require successful full Lean push and PR builds on the new SHA before using the six endpoint cases in the residual proof.


## 2026-10-29 — Remove orphaned wrapper documentation after C/X insertion

- Lean failed on commit `973fe2a4d690ae0e75431984078fa47841745156` at `FinalTilde.lean:4212`: `unexpected token '/--'; expected 'lemma'`.
- Cause: after the original support-equivalence wrapper and all six endpoint specializations, an orphaned duplicate doc-comment for the wrapper remained immediately before the documented residual theorem. The wrapper itself is already declared earlier and remains unchanged.
- Removed only that orphaned comment. All six endpoint specializations (A/X, B/O, C/O, A/Y, B/Y, C/X) and the high-power residual theorem are preserved exactly.
- Require successful full Lean push and PR builds on the new SHA before proceeding to instantiate the endpoint lemmas in the residual theorem.


## 2026-10-29 — Assemble all six endpoints into actual high-power residual stability

- Parent SHA `52efcacc5779d8676fb57c7d10e6160f1495ee45` passed both full Lean builds.
- Added `sgK_glued_partner_diag_four_five_transport`, which splits the existing `gl` relation into its six corner/copy clauses and dispatches to the already compiled A/X, B/O, C/O, A/Y, B/Y, and C/X specializations. It introduces no new geometric or matrix-entry assumptions beyond the existing axis-periodicity hypotheses.
- Added `glueRHS6_highPowerResidual_sgK_til_succ`: applies the abstract residual transport theorem to actual `sgK` matrices for `faceAxis` and the fixed axis `fun _ => 2`, proving the eight diagonal conditions from the existing glued-state degree lemmas and all four `h4/h5` obligations from the six-case wrapper.
- **Next:** require both full Lean builds to pass on the new SHA. If green, connect this adjacent-level residual stability to `defectO6_succ_num_level3` to replace the explicit level-dependent boundary term by its base-level value.


## 2026-10-29 — Reduce the sixth-moment recurrence's high-power boundary term to level three

- Parent SHA `28afa58176c7e8c64a01529cc221c37bc0fb4137` passed both full Lean builds after assembling the six endpoint cases.
- Added an induction showing the concrete tilde-oriented high-power residual is level-independent for every (m\ge3), using the now-proved adjacent-level residual stability.
- Transferred the result to numbering orientation via the existing `glueRHS6_highPowerResidual_num_eq_til`.
- Recast the sixth-moment recurrence as `defectO6_succ_num_level3_constant_boundary`, where the high-power boundary contribution is explicitly the value at level three. No claim that this base residual is zero is made.
- **Next:** solve the resulting affine recurrence in m exactly, keeping the base-level orientation gap and residual explicit, then determine whether the remaining finite base term has a separate exact evaluation.


## 2026-10-29 — Remove redundant final tactic in constant-boundary recurrence

- Lean push build on `02e223f3376342107e30e6e31ef54b72e5f983a5` reached the end of `defectO6_succ_num_level3_constant_boundary` and reported `No goals to be solved` at the final `ring`.
- The preceding rewrites already close the goal; removed only that redundant tactic. No theorem statement or mathematical argument changed.
- Recheck both full Lean builds on the corrected SHA before continuing to the explicit affine solution.


## 2026-10-29 — Derive the explicit affine closed form for the sixth-moment defect

- Parent SHA `20cfb844d552f23aa9b0c109a2b31c36c5dd9ee8` passed both full Lean builds after reducing the boundary term to its level-three value.
- Added `defectO6_num_closed_form`, applying the pre-existing `affine_three_recurrence` arithmetic lemma to the now-proved constant-boundary recurrence.
- The formula is explicit in (3^{m-3}), the level-three numbering defect, the level-three orientation gap, and the level-three high-power boundary residual. It does not silently set either finite base contribution to zero.
- **Next:** check both full Lean builds. If green, inspect whether the level-three residual/gap have exact existing evaluations that can finish the target theorem without assumptions.


## 2026-10-29 — Expose the sixth-moment affine growth law as a named theorem

- Parent SHA `9f04c0c8520fcaaf0b9879bdc79023e962b0dbf9` has successful full Lean builds on both push and PR workflows.
- Added named definitions for the exact residual constant, growth coefficient, and constant offset, each expressed through actual finite level-three quantities.
- Added `defectO6_num_affine_growth`, stating the all-angle law `D_m = 3^(m-3) A(θ) + B(θ)` for every `m ≥ 3`; and `defectO6_num_growth_recurrence`, stating the equivalent one-step recurrence with a single explicit constant.
- These are consequences of the previously proved endpoint transport and residual stabilization; no assumption that the level-three gap or residual vanishes was introduced.
- **Verification gate:** both full Lean builds must pass on the new SHA. The residual constant's simplified elementary expression at arbitrary `θ` remains a separate finite-level evaluation question.


## 2026-10-29 — Verification of the named H6 growth-law API

- Commit `7ce1e9d687ce8b20d61bb6c5da39b0975f41519c` passed both full Lean formalization workflows: PR run `40914856804` and push run `40914846902`.
- The named recurrence and affine-growth theorems compile without changing the six endpoint proofs.
- Updated public status text to separate the proved all-angle recurrence for `m ≥ 3` from the unsimplified finite coefficient and the level-2-to-3 base transition. H8/H10 remain open.


## 2026-10-29 — Exact symbolic base transition and explicit H6 closed form

- Mathematical source checkpoint: `0dc6bb98573050003d94ab83fa20b8894e61294a`; the Lean recurrence is `defectO6_num_growth_recurrence` in `FinalTilde.lean`, proved for `m ≥ 3`.
- The exact polynomial test pins the raw level-two defect polynomial `-14256 s^2 - 384 s^3 - 336 s^4 + 1344 c s^2 - 336 c^2 s^2`; using `c^2+s^2=1`, this is `D₂=-14592 s²+1344 c s²-384 s³`.
- The certificate verifies `D₃-3D₂=C₆(θ)`, with `C₆(θ)=4512 s²+192 c s²+768 s³`, and equality of the adjusted residual polynomials at levels 2 and 3. The calculation uses exact integer/Gaussian-integer polynomial arithmetic, not floating-point fitting.
- Combined with the Lean recurrence for `m ≥ 3`, the finite identity yields for all `m ≥ 2`: `D_m=3^(m-2)D₂+(3^(m-2)-1)C₆/2`, equivalently `D_m=-(12336·3^(m-2)+2256)s²+(1440·3^(m-2)-96)c s²-384s³`.
- Proof boundary: the structural recurrence is Lean-kernel checked; the exceptional finite level-2-to-3 trace identity is an exact reproducible Python polynomial certificate and is not yet formalized in Lean.
- Metadata: the repository owner supplied the name Evgeny Zaprudnov. The supplied dissertation PDF labels its author “Архитектор (Papka)” and contains no verifiable email address; no email has been guessed or added.
- Final verification gate: complete Lean and Python push/PR workflows on the final commit before merge.



## 2026-10-29 — Final-source verification before PR merge

- Source/test commit `772b521afd6befcb80af0d590f6742e488a6ea76` passed the complete Lean build and Python suites on both push and pull-request workflows.
- Lean push: `40926915630` (success); Lean PR: `40926931506` (success).
- Python push: `40926915594` (success); Python PR: `40926930923` (success), with Python 3.11 and 3.12 jobs successful.
- The exact base-transition test includes assertions for the raw and normalized level-two polynomial, (D_3-3D_2=C_6(\theta)), and (C_6(\pi)=5280). The formulas are documented as a combined Lean recurrence plus exact Python symbolic certificate, not as a fully Lean-kernel proof of the finite base step.
- The PR is being prepared for merge; the branch merge state is recorded by the PR itself after the merge operation.


## 2026-10-30 — Formalize the H8 two-N boundary stratum

- Added the theorem sg_trace_p8_two_N_stratum_boundary in GlueTrace.lean.
- The theorem groups the four cyclic two-N classes (1,7), (2,6), (3,5), and periodic (4,4) with exact word multiplicities 8, 8, 8, and 4.
- Each trace is reduced through the existing generic trace_two_N_powers; the corner-off-diagonal premises are derived from sgK_pow_hkg_of_OAnti using the geometric bound 7 < 2^m for m >= 3.
- Scope is deliberately limited to the r=2 boundary stratum. This does not establish the full H8 even-stratum expansion, axis cancellation, or an all-level H8 recurrence. Require the full Lean workflow to pass before proceeding to the r=4 stratum.


## 2026-10-30 — Formalize the H8 four-N boundary stratum

- Added a reusable concrete corner-power reduction for four-N words with terminal K^0.
- Added sg_trace_p8_four_N_stratum_boundary for all ten p=8 cyclic r=4 classes.
- The orbit weights are eight for eight classes, four for (1,3,1,3), and two for (2,2,2,2), summing to C(8,4)=70.
- Each of the two diagonalized middle powers is at most five; sgK_pow_hkg_up_to_five_of_OAnti discharges the required corner hypotheses for m >= 3.
- Scope remains a single even boundary stratum. It does not prove cancellation, the H8 trace split, or the all-level H8 recurrence.


## 2026-10-30 — Formalize the H8 six-N boundary stratum

- Added sg_trace_p8_six_N_stratum_boundary for all four cyclic r=6 classes.
- Exact orbit multiplicities are 8, 8, 8, and 4; their sum is C(8,6)=28.
- Each class is reduced by trace_six_N_powers_boundary, retaining the three ordered diagonal corner insertions. All required exponents are at most three, covered by sgK_pow_hkg_up_to_five_of_OAnti for m >= 3.
- This is only the r=6 boundary reduction; it makes no cancellation or H8 recurrence claim.

## 2026-10-30 — Imported H8 positive-even boundary checkpoint

- Source checkpoint: `54392a2b8100b40aa0b9589907adef1cd9f1cac6`.
- The H8 boundary statements are now in the imported module
  `formalization/EvgenyTheorem/GlueTrace.lean`, not only in the legacy,
  unimported `formalization/Evgeny-Theorem/GlueTrace.lean` copy.
- The imported module proves the concrete p=8 boundary reductions for
  `r=2`, `r=4`, and `r=6` separately. The existing top-stratum
  `r=8` boundary/diagonal theorem is retained. Their exact ordered-word
  weights are respectively 28, 70, 28, and 1; the empty-insertion
  `r=0` term remains the separate `trace(K^8)` contribution.
- Full Lean formalization build passed on this exact source checkpoint:
  run `41094123297` (success).
- Python 3.11 and 3.12 fast and slow suites passed on the immediate parent
  `d777e53b85eee87d1ed02b99f63fcb2ec6bc684a`, run `41091825697`
  (both jobs success). The only file changed between that parent and this
  checkpoint is `formalization/EvgenyTheorem/GlueTrace.lean`; no Python
  source, tests, or fixtures changed. The exact-checkpoint Python run
  `41094123151` had not reported completion when this entry was written.
- Deliberately removed the unfinished p=8 aggregate/odd/full-split proof
  block. This checkpoint does **not** claim the combined even-stratum
  identity, odd-stratum cancellation, the full p=8 ordered trace split,
  an all-level H8 recurrence, or any H10 result.
- Next mathematical gate: assemble the already-proved even strata without
  expanding giant nested sums, then prove the odd cyclic classes with
  exact pivots and their OAnti/corner hypotheses. Only after the complete
  H8 split and its level-transport recurrence are independently checked
  may H10 work resume.



## 2026-10-30 — Align the H8 three-N proof goal with local K/N expressions

- Audited branch head before editing: `da9eec53cf679337109819f21604214a68715b61`; the only source failure on that
  commit was `GlueTrace.lean:2861:2`, `simp made no progress`.
- In `sg_trace_p8_three_N_stratum_zero`, removed the initial unrestricted
  `dsimp`. The local matrices `K` and `N` are now introduced first, and an
  explicit `change` presents the unchanged seven-term target using those
  exact local names. The seven cyclic-rotation identities and all seven
  individual `hzero_r3_*` proofs are unchanged.
- This is a definitional/proof-state alignment only: the theorem statement,
  `OAnti (m + 1) o` hypothesis, bound `m ≥ 3`, cyclic representatives,
  and multiplicities are unchanged. No new mathematical claim is added.
- Full Lean build and Python 3.11/3.12 status for the resulting source commit
  are pending; the exact commit SHA and run links will be added in the
  verification follow-up.
- H8 remains open: concrete r=5/r=7 aggregation and the complete ordered
  trace split are still required, followed by the weighted even-boundary
  comparison and level recurrence. No H10 closure is claimed.


## 2026-10-30 — Formalize the H8 five-N stratum

- Parent source `ff9e9a47891cd4dd430b5d5601bbe694b2ee1527` passed the full
  Lean project build (`lake build EvgenyTheorem`, run
  `41106775479`). Python 3.11/3.12 jobs were still running when this
  mathematical step began; they are tracked independently.
- Added `sg_trace_p8_five_N_stratum_zero` in the imported
  `GlueTrace.lean`. It handles all seven cyclic r=5 classes from the
  p=8 ordered-word inventory, each with exact orbit weight eight, total
  weight \(56=\binom{8}{5}\).
- Each representative is rotated using `trace_cyclic_list` only. The
  seven calls to `trace_five_N_powers_zero_of_OAnti` use the exact
  exponent tuples `(4,1,1,1,1,0)`, `(2,1,1,1,3,0)`,
  `(2,1,1,3,1,0)`, `(3,1,1,2,1,0)`, `(3,1,1,1,2,0)`,
  `(2,1,1,2,2,0)`, and `(2,1,2,1,2,0)`.
- The helper's two corner hypotheses are only for the second and fourth
  exponents \(b,d\). Here \(b=1\) in all seven classes and
  \(d\\in\\{1,2,3\\}\); \(m\\ge3\) gives \(3<2^m\), so the strict
  hypotheses follow with the existing concrete OAnti specialization.
  The theorem statement, its `OAnti (m+1) o` hypothesis, and the
  level bound are unchanged by this reduction.
- This proves only the r=5 odd stratum if the fresh Lean build succeeds.
  It is not the complete H8 ordered trace split and does not establish
  cancellation of the even boundary terms or an H8 recurrence.
- Verification on the new source SHA is pending. Next mathematical step,
  after green Lean: add the single r=7 class using
  `trace_seven_N_powers_zero_of_OAnti`, then assemble the full ordered
  H8 split with exact cyclic weights.


## 2026-10-30 — Verify H8 r=5 and add the r=7 class

- Parent `8e3d22da1c65eb04212161f2e21dc57869ceed06` passed the full Lean project build:
  `lake build EvgenyTheorem`, run
  [41108416124](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41108416124);
  the log reports `Build completed successfully (3060 jobs)`.
  Python run [41108416024](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41108416024)
  was still running at this checkpoint and remains independently tracked.
- The r=5 theorem `sg_trace_p8_five_N_stratum_zero` is therefore Lean-verified
  on `8e3d22da1c65eb04212161f2e21dc57869ceed06`: all seven classes compile, each with orbit weight eight
  (total 56).
- Added `sg_trace_p8_seven_N_stratum_zero` for the unique r=7 class. Its
  orbit weight is eight. The proof rotates the expanded representative
  `K * (K*N)^7` by moving its initial `[K,K]` block to the end, obtaining
  the exact seven-N word with exponent tuple `(0,1,1,1,1,1,1,2)`.
- The existing `trace_seven_N_powers_zero_of_OAnti` requires the three
  selected corner bounds only at exponents (b,d,f); here all are one.
  The bound (1<2^m) follows from (m\ge3). The only mathematical
  hypothesis is the unchanged `OAnti (m + 1) o`.
- The new r=7 source change and this log entry are pending a fresh full
  Lean build. H8 is not yet a complete trace split: the even boundary
  terms still require their joint weighted comparison and level transport.


## 2026-10-30 — Assemble the complete H8 ordered trace split

- Audited parent `343092e894bfa1b0849f1153c25f2e82680588f1`. The full project Lean build for
  [run 41109918875](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41109918875)
  passed; the job log reports `Build completed successfully (3060 jobs)`.
  Python 3.11/3.12 run
  [41109919069](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41109919069)
  was still running when this step began.
- Added `sg_trace_p8_cyclic_even` in the exact order of the even classes
  in `trace_orderedWordExpansion_eight_cyclic`, plus
  `sg_trace_p8_cyclic_even_eq_glueLHS8`. Its 19 explicit rotations match
  every class in `glueLHS8`: r=2 (4 classes), r=4 (10), r=6 (4),
  and r=8 (1). Their exact total orbit weights remain 28, 70, 28, and 1.
  Periodic classes retain weights 4 (r=2), 4 and 2 (r=4), and 4 (r=6).
- Added `sg_trace_p8_ordered_expansion_boundary`. It composes the general
  ordered-word expansion, the exact 36-class cyclic grouping, the four
  already-proved odd-stratum vanishing theorems (r=1,3,5,7), the 19
  even-class rotations, and `sg_trace_p8_all_even_strata_boundary`.
  The resulting identity is
  `trace((K + K*N)^8) = trace(K^8) + glueRHS8(m,K)` for m >= 3
  under `OAnti (m+1) o`.
- This closes the **level-local ordered trace split** only. It does not
  prove that `glueRHS8` cancels between the target operator configurations,
  does not prove a level-transport identity, and does not establish an
  H8 recurrence or closed formula. H10 remains deferred.
- Fresh full Lean and Python CI for the new source SHA are pending.


## 2026-10-30 — Normalize H8 odd-stratum identities in the full trace split

- Audited failed full Lean build
  [41112344232](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41112344232)
  on parent `c74dd4dfe93a302242ee0082db7d82b601f86aaf`. The only two source errors were in the newly
  added `sg_trace_p8_ordered_expansion_boundary` proof, at lines 3289
  and 3291. Python workflow
  [41112344222](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41112344222)
  passed for Python 3.11 and 3.12, with fast suites 219 passed and slow
  suites 8 passed on each version.
- Line 3289 compared the raw A/B words from the cyclic expansion with the
  odd-stratum theorems before zeta-reducing their local `K,N` lets and
  expanding the `K^n` blocks. The proof now performs `dsimp [K,N]`
  on the four odd identities and goal, followed by `simp only [pow_succ]`,
  before the linear combination. This is definitional normalization only;
  all four theorem statements and coefficients remain unchanged.
- Line 3291 used `congrArg` to add the common `trace(K^8)` term to the
  even-class identity. The simplifier cancels this common additive term
  in the target, so the proof now applies
  `sg_trace_p8_cyclic_even_eq_glueLHS8` directly after `simpa [N]`.
- No mathematical statement, representative, orbit weight, support
  hypothesis, or degree bound was changed. The fresh full Lean build is
  pending.


## 2026-10-31 — Root-cause correction: normalize zero powers in H8 odd-stratum assembly

- Rechecked the completed CI run for parent `75a9802791ee54dc6d9d04400cceb36e3e6838a7`:
  Lean run [41140559328](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41140559328)
  failed only at the odd-stratum `linear_combination` in
  `sg_trace_p8_ordered_expansion_boundary`; Python run
  [41140559183](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41140559183)
  passed for Python 3.11 and 3.12.
- The failed goal state showed `hOne`, `hThree`, and `hFive` still
  contained factors `K ^ 0 * ...`, while the ordered expansion contained
  the corresponding literal K words. The prior normalization expanded
  `pow_succ` but omitted its base case. This is the precise source of the
  remaining `ring expressions not equal` failure.
- Independently compared the odd terms in
  `trace_orderedWordExpansion_eight_cyclic` with the theorem statements:
  r=3 has seven matching words/weights (8 each), r=5 has seven matching
  words/weights (8 each), and r=1/r=7 each have the single expected class
  with weight 8. No factor permutation or representative mismatch was found.
- Completed the normalization set with `pow_zero`, `Matrix.one_mul`,
  and `Matrix.mul_one` before the existing linear combination. This changes
  no theorem statement, coefficient, orbit multiplicity, hypothesis, or
  matrix-factor order. Fresh full Lean verification is pending.
- Process correction: do not label a Lean proof-state fix complete from an
  assumed simplifier behaviour. The actual error goal must be inspected, and
  all base cases of any recursive normalization (here `pow_succ` plus
  `pow_zero`) must be checked against the target expression before pushing.


## 2026-10-31 — Complete the H8 word normalization with associativity

- Fresh Lean run [41142514999](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41142514999)
  on `4053b622ca7c1f605b1c091856d106e2b1391f8c` still failed at line 3291, in the same
  `linear_combination`; Python run
  [41142515198](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41142515198)
  passed for Python 3.11 and 3.12.
- The fresh log confirms `pow_zero` and `Matrix.one_mul` were used,
  but the compared trace products still had different parenthesizations.
  It also explicitly reports `Matrix.mul_one` as unused.
- Compared with the already-green H6 ordered-split proof: its working
  normalization uses `simp [pow_succ, Matrix.mul_assoc]` before
  `linear_combination`. The H8 proof had omitted associativity from its
  normalization. The line now includes `Matrix.mul_assoc` and drops the
  unused `Matrix.mul_one`. No factor order or mathematical statement is
  altered; associativity only normalizes parentheses.
- This is a focused correction to the same failed line. Full Lean
  verification on the new SHA is pending.


## 2026-10-31 — Lift the verified H8 trace split to the actual glued operator

- Parent `16c78a8fb79e49ab60c7c7b99dc447be765ec37e` passed the complete Lean project build:
  [run 41154816237](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41154816237),
  with `Build completed successfully (3060 jobs)`.
- Added `pOpO_trace8_glue_final`, the degree-eight analogue of the
  existing `pOpO_trace6_glue_final`. It composes:
  1. `pOpO_succ_trace_ordered_words` at (p=8);
  2. the complete local H8 ordered split
     `sg_trace_p8_ordered_expansion_boundary`;
  3. the arbitrary-degree block trace identity
     `trace_blockK_pow` at degree eight.
- The precise conclusion is
  `Tr(pOpO(m+1)^8) = Σ_c Tr(Hc(c)^8) + glueRHS8(m,sgK)`.
  The full boundary correction remains explicit. No equality of its
  values for different axis configurations, no cancellation, and no
  level recurrence are claimed by this wrapper.
- This is one proof-composition step only. Fresh full Lean build is pending;
  Python workflow for parent `16c78a8fb79e49ab60c7c7b99dc447be765ec37e` was still running at the time of
  this step and is tracked independently.
- Next mathematical target after green Lean: define the eighth-moment
  axis defect and derive its exact copy-split recurrence with the difference
  of the two `glueRHS8` corrections retained. Only then investigate whether
  that boundary difference stabilizes under the actual `faceAxis` versus
  fixed-Z configuration.


## 2026-10-31 — Exact H8 defect recurrence with the boundary difference retained

- Parent `8ee1dee5cbd78776bdd28904d9a575f457091618` was verified by both CI workflows:
  Lean [41155855127](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41155855127)
  passed the full `lake build EvgenyTheorem` (3,060 jobs), and Python
  [41155855107](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41155855107)
  passed both Python 3.11 and 3.12.
- Added `defectO8`, the difference of the two degree-eight traces for
  arbitrary axis functions `ax` and `ax'`.
- Added `defectO8_succ`, under the exact same hypotheses pattern as the
  verified `defectO6_succ`: (m\ge3), `OAnti (m+1) o`, and the two
  level-periodicity equations for each axis function.
- The proof applies `pOpO_trace8_glue_final` to both axis configurations,
  rewrites the two block sums with `sum_gcopy` and the defining identities
  for `Hc), then closes the subtraction identity by ring normalization.
- The exact conclusion is
  `D8(m+1)=D8(m,o)+D8(m,oBo)+D8(m,oCo)+ΔB8(m)`, where
  `ΔB8(m)=glueRHS8(m,sgK(ax,o))-glueRHS8(m,sgK(ax',o))`.
  The boundary difference is not set to zero, and this theorem alone does
  not establish a closed form or a scalar recurrence for the faceAxis/Z
  specialization.
- Fresh full Lean and Python CI for the new source SHA are pending.


## 2026-10-31 — Specialize the exact H8 recursion to the standard orientation

- Parent 8023cc210b8ecb3c20ad101d168e8a45d5847522 passed full Lean build:
  [41156780325](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41156780325)
  (lake build EvgenyTheorem, 3,060 jobs). Python 3.12 passed in
  [41156780329](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41156780329);
  Python 3.11 was still running when this step began.
- Added defectO8_congr and orient_transfer8, the degree-eight
  versions of the established flux-edge orientation-transfer results.
  The proof still depends only on agreement over the ordered face edges
  and anti-symmetry, exactly as the lower-moment transfer does.
- Added transfer_A8, transfer_B8, and transfer_C8. Their
  geometric proofs are the already-established A/B/C face transport
  arguments; the C-copy exceptional corner remains represented by
  oTil m, not silently identified with oNum m.
- Added defectO8_succ_num. For oNum (m+1), the three copy terms
  reduce to 2 D8(m,oNum(m)) + D8(m,oTil(m)), while the difference
  glueRHS8(faceAxis)-glueRHS8(fixed-Z) remains explicit.
- No stabilization or vanishing of the boundary residual is asserted.
  The result is a specialized exact recurrence, not a closed formula.
  Fresh full Lean and Python CI for the new SHA are pending.


## 2026-10-31 — Specialize the exact H8 recurrence to the flipped-corner orientation

- Rechecked branch work/h8-h10-exact-recurrence-certificates at parent
  c801797d9fbab6186d333644de915b2a81ca536c; the complete Lean build passed
  (lake build EvgenyTheorem, 3,060 jobs) in
  [41157905894](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41157905894).
  Python 3.11 and 3.12 fast and slow suites both passed in
  [41157905863](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/runs/41157905863).
- Added defectO8_succ_til in FinalTilde.lean, using the general
  defectO8_succ and the verified degree-eight orientation-transfer theorem.
- The copy transports are explicit: A maps oTil (m+1) to oNum m
  because cp1_not_A excludes the exceptional edge; B maps to oTil m
  because cp1_shiftB transports both directions of the exceptional edge;
  C maps to oTil m because cp1_shiftC proves that neither directed
  exceptional edge occurs in that copy. Thus the child contribution is
  exactly one oNum term and two oTil terms.
- The theorem retains
  glueRHS8(m, sgK(faceAxis,oTil(m+1))) -
  glueRHS8(m, sgK(fixed-Z,oTil(m+1)))
  as an explicit boundary difference. No cancellation, vanishing, or
  level-independence is asserted.
- Hypotheses remain m >= 3, θ : ℝ, OAnti (m+1) (oTil (m+1))
  (provided by oTil_anti), and the already proved two period identities
  for faceAxis; the fixed-Z axis identities are reflexive.
- Fresh full Lean and Python CI for the new commit are pending. H8 is still
  open: next derive the exact orientation-difference recurrence and then
  prove the needed H8 boundary-residual comparison. H10 remains deferred.


## 2026-10-31 — Exact H8 recurrence for the difference of orientations

- Rechecked branch work/h8-h10-exact-recurrence-certificates at parent
  62686b7c66afe583c56f53658667e5a2c0a9a830. The full Lean build passed
  (lake build EvgenyTheorem, 3,060 jobs) in run
  41159024416. Python 3.11 fast and slow suites passed in run
  41159024564; Python 3.12 was still running when this step began.
- Added defectO8_orientation_difference_succ in FinalTilde.lean.
  Its proof uses only the two already proved H8 recurrences
  defectO8_succ_num and defectO8_succ_til, then normalizes the resulting
  linear identity by ring. No new geometric or analytic hypothesis is added.
- With G8(m) defined as D8_num(m)-D8_til(m), the theorem states
  G8(m+1)=G8(m)+R8_num(m)-R8_til(m), where each R8 is the full
  faceAxis-versus-fixed-Z glueRHS8 difference at its corresponding
  orientation. The top and all other even boundary strata remain included.
- This result identifies the exact obstruction to constancy of the
  orientation gap. It does not assert R8_num=R8_til, does not assert
  G8 is constant, and does not establish a closed H8 formula.
- Fresh full Lean and Python CI for the new source SHA are pending.
  The next mathematical task is an H8-specific proof or reduction of
  R8_num(m)-R8_til(m), auditing all diagonal powers through the boundary
  degree and the precise support/degree conditions. Do not reuse the
  degree-six residual theorem without a separate degree-eight proof.


## 2026-10-31 — H8: extend flip-insensitivity of glued rows through degree seven

- Parent f15bdb55a5404c36dce8e2c4ba7d0c546a8a1848 has a successful
  full Lean build in run 41159919623. Python 3.11 fast and slow suites
  passed in run 41159919646; Python 3.12 fast passed and its slow suite
  was still running at the time of this step.
- The source audit of glueRHS8 shows that its largest explicit boundary
  diagonal power is seven, in the r=2 term (K^1)xx (K^7)sigma(x),sigma(x).
  The other r=2 terms use powers 2, 6, 3, 5, and 4; the r=4/r=6/r=8
  terms use powers no larger than those displayed in the definition.
- The existing flip-insensitivity lemma only covers rows through power
  five, because the distance from the B-copy glued corners to the
  exceptional edge is at least seven when m=3. That does not justify
  a degree-seven path argument at m=3.
- Added sgK_pow_zero_from_glue_to_flip_up_to_six for m >= 4,
  using the actual coordinate gap 2^m - 1 > 7 >= n, and then
  sgK_pow_row_eq_num_til_on_glue_up_to_seven and its diagonal
  corollary. The proof changes no operator or orientation hypotheses:
  the comparison is between oNum (m+1) and oTil (m+1), and is
  obtained from the previously proved row congruence away from the flip.
- This establishes the support/entry-comparison prerequisite for the
  H8 boundary residual audit. It does not yet prove that all of
  glueRHS8 is invariant, because each of its 19 boundary classes,
  including the four ordered r=6 traces and the top r=8 term, must be
  reduced to the specific glued-row/diagonal comparisons.
- The new full Lean and Python workflows are pending. H8 and H10 remain
  open; H10 is deferred until the H8 boundary comparison is proved.


## 2026-10-31 — H8: prove orientation invariance of the complete boundary correction

- Parent 132e84074e08009e4d3f54d923e873b3ce6b06a4 has a successful full
  Lean formalization build in run 41160699748. Its Python 3.11 fast and slow
  suites passed; Python 3.12 fast tests passed and the slow suite was still
  running when this change was prepared.
- Added a support-sensitive trace lemma for three ordered kernel factors
  separated by three supported diagonal weights. It allows the three kernel
  factors to differ and preserves their order.
- Added glueRHS8_congr_of_glued_row_pow. Its hypothesis is equality of
  every row starting at a glued state, for every power through degree seven.
  The proof explicitly treats all four r=2 weighted sums, all ten nested
  r=4 sums, all four r=6 ordered traces, and the r=8 fourth-power endpoint.
  The exact coefficients and factor order in glueRHS8 are unchanged.
- The r=6 traces are each reduced to an exact pointwise sum by the new
  three-diagonal trace lemma. The off-diagonal hypotheses needed for this
  reduction are discharged separately for both orientations using the
  existing degree-five glued-corner support theorem. The diagonal powers
  are then compared by the degree-seven row equality.
- Applied the congruence to oNum (m+1) and oTil (m+1). This proves that
  the H8 orientation gap is constant from level four onward and reduces
  every such gap to its exact level-four value. The proof does not assert
  that the level-four value is zero.
- This is a full comparison of glueRHS8, not yet the all-level H8 moment
  identity: the remaining task is to control the level dependence of the
  common boundary residual itself and derive the exact scalar recurrence.
  H8 and H10 are not marked closed.
- The new Lean and Python CI runs are pending at this commit.


## 2026-10-31 — H8: repair the first failed full-boundary comparison build

- The Lean run for commit 29987eb98f597c8c2fb6691abaa0d1acefad9fe6
  failed in GlueTrace.lean. The first type error showed that the existing
  two-kernel collapse theorem only accepts the same kernel on both sides;
  the new r=6 proof had supplied independent left and right support
  hypotheses, so that theorem was not applicable.
- Added an asymmetric two-kernel trace-collapse lemma from the explicit
  two-index finite-sum formula. It uses the support of both diagonal
  weights and the separate off-diagonal hypotheses for A and C; it does
  not assume symmetry or identify A with C.
- Corrected the r=6 intermediate sum to retain the support indicators
  inside the diagonal weights until the outer glued-point conditional is
  simplified. The previous simplifier calls failed because the condition
  was hidden behind the local abbreviation g.
- Lifted the three kernel-power bounds from <= 5 to <= 7 when applying
  the degree-seven row-comparison hypothesis; the off-diagonal support
  lemma itself remains used only through degree five.
- This is a compile-error repair only. No mathematical claim is treated
  as verified until the next full Lean workflow succeeds.


## 2026-10-31 — H8: second repair based on repository proof precedents

- Re-read the full Lean failure from run 41163149778 and compared the new
  asymmetric finite-sum lemma with the already compiling theorem
  trace_kernel_diagonal_kernel_diagonal_collapse in TraceExpand.lean.
- The previous proof had inserted an extra first branch after
  Finset.sum_eq_single. In this project, the verified pattern is:
  first prove the off-diagonal summands vanish, then close the impossible
  excluded-index case with simp. The new helper now follows that exact
  pattern. The unused Finset.mul_sum simp argument was also removed.
- The two no-progress errors in the r=4 outer sum came from a let-bound
  predicate g: after unfolding sg_trace_four_N_boundary_sum the outer
  guard is still written through (sgGlue m).g. The hfour branches now
  unfold g in the same way as the already repaired htop branch.
- The previous ring failure in the three-diagonal reduction was downstream
  of the failed asymmetric helper application. It will be reassessed from
  the next Lean log rather than pre-emptively changing algebraic tactics.
- No change to the moment statement, cyclic coefficients, word order,
  or geometric assumptions.


## 2026-10-31 — H8: replace the failed r=6 collapse with the supported-block comparison

- Re-audited the existing sg_trace_p8_six_N_stratum_boundary and its
  generic source trace_six_N_powers_boundary. These already establish the
  exact r=6 reduction to three ordered supported diagonal matrices
  D_b, D_d, D_f separated by the original ordered powers of K.
- The previous attempt added a second theorem that collapsed the trace
  further to a diagonal-only sum. That extra reduction was unnecessary and
  introduced the persistent Lean failure; it is removed entirely.
- The comparison now uses cyclicity only to rotate the original trace to
  trace((D_b*K^c)*(D_d*K^e)*(D_f*K^a)). Each D is diagonal and supported
  on the glue set. Thus D_b*K^c only reads rows of K^c whose indices lie
  in the glue set; the same holds for the other two blocks. The degree-seven
  row congruence gives equality of each block, including the diagonal
  weights at partner points because g(σ(x)) is already proved.
- This preserves the full trace and its order. It requires neither a
  diagonal collapse of the trace nor off-diagonal vanishing of the three
  factors. The four original orbit weights 8, 8, 8, and 4 are unchanged.
- The next full Lean build is the required verification. H8 and H10 remain
  open until the shared boundary residual has its level-transport proof.


## 2026-10-31 — H8 declaration order fix

The Lean run 41165333999 compiled GlueTrace but failed in FinalTilde at the use of sgK_pow_row_eq_num_til_on_glue_up_to_seven. The theorem was declared later in the same file. Lean declarations are sequential, so this was a forward-reference error, not a mathematical failure. Moved glueRHS8_num_eq_til and its two dependent orientation-gap corollaries after the degree-seven row theorem. Statements and proof terms are unchanged. A full build is required to confirm.


## 2026-10-31 — Sandbox/history audit and comment-boundary repair

- The last fully green checkpoint is 132e84074e08009e4d3f54d923e873b3ce6b06a4:
  full Lean build run 41160699748 and Python run 41160699737 both succeeded.
- The intervening H8 commits only attempted the degree-seven boundary
  congruence. Their successive Lean failures were:
  29987eb: invalid reuse of the symmetric two-kernel trace collapse;
  030b3f6: same mismatch persisted in the asymmetric helper proof;
  05f4e52: sum-branch and local-predicate simplification errors;
  0f2fc5c: GlueTrace passed, but FinalTilde referenced the seven-power
  row theorem before its declaration;
  175bdfa: after moving declarations, one syntax error remained because
  the first line of the following p=6 documentation comment was omitted.
- Restored the complete existing p=6 comment. This is a pure syntax repair;
  no theorem statement, proof term, hypothesis, or coefficient changed.
- The local execution image does not contain Lean/Lake and cannot reach
  GitHub from the shell, so an independent local lake build is unavailable.
  The code was cross-checked against the exact GitHub source blobs and
  complete Actions logs; the next full GitHub Lean workflow is the executable
  formalization check.


## 2026-10-31 — H8: generic degree-six/seven diagonal transport lemma

- Added matrix_pow_six_seven_diag_eq_of_local_equiv beside the existing
  radius-two fourth/fifth-power transport lemma.
- The new statement is purely algebraic: if two kernels agree on matched
  finite neighborhoods and their root rows/columns through degree three
  vanish outside those neighborhoods, then their root diagonal entries
  agree at degrees six and seven.
- The proof keeps matrix order explicit. It uses
  K^6 = K^3*K^3 and K^7 = K^3*K^4, derives the required restricted
  degree-two/three/four row or column sums, and reindexes only by the stated
  finite-set equivalence. No symmetry, commutativity, word reversal, or
  unproved level transport is assumed.
- This is the algebraic prerequisite for the H8 corner-neighborhood step;
  it does not yet prove that the concrete radius-three neighborhoods are
  equivalent across Sierpinski levels and does not establish residual
  stability. H8/H10 remain open.
- The full Lean workflow on the parent d74731b succeeded. The parent
  Python 3.11/3.12 slow suites were still reported in progress at the last
  status poll; the new commit will be checked independently.


## 2026-10-31 — H8 degree-six/seven helper: CI correction

- Lean run 41167830823 on parent 4e4f1bb found two elaboration issues in
  the new generic helper, both local to root-value rewriting:
  (1) the degree-two column calculation needed hrootVal after hEntry z xr;
  (2) the degree-three row reindexing already had x' and must not rewrite
      hrootVal a second time.
- Applied only those two proof-script corrections and removed empty lines
  inside the theorem proof that triggered style warnings. The matrix
  factorizations, finite-support hypotheses, and theorem statement are
  unchanged. Full Lean verification is required on the corrected commit.

## 2026-10-31 — Corrected audit of H8 degree-six/seven transport (run 41168333397)

The full log for SHA 2fd926f contains exactly two elaboration errors in
matrix_pow_six_seven_diag_eq_of_local_equiv:

1. In hpow2Row, after rewriting hEntry xr z and hEntry z y, the
   reindexed summand still has (e xr).1 as its first matrix index.
   hrootVal must be applied there, before Equiv.sum_comp e.
2. In hpow3Row, hpow2Row z has already changed the first matrix index
   to x'; there is no (e xr).1 left to rewrite. The extra root-value
   rewrite must be removed before Equiv.sum_comp e.

The hpow2Col proof already correctly applies hrootVal after
hEntry z xr and is left unchanged. This corrects the placement in the
previous attempt. The generic theorem statement, hypotheses,
factorizations K^6=K^3K^3, K^7=K^3K^4, and all H6 code remain
unchanged.

The style-linter warnings in FinalTilde.lean are not the build failure:
the green parent d74731b has the same class of warnings. The failure
is the two explicit proof errors above. No timeout occurred.

## 2026-10-31 — H8 transport: repair the reindexing mismatch (run 41169771612)

On SHA 3b17a66 the previous rewrite bundle still failed at FinalTilde.lean:3305.
The `Equiv.sum_comp` identity was correct, but its source sum had not been
normalized to the target-root summand: Lean retained `(e xr).1` on the left.
The earlier log wording that the root rewrite had been correctly applied
therefore overstated what the compiler had verified.

The hpow2Row summand proof is now split explicitly:
first use the two local-entry equalities to identify the K-products with
`L (e xr).1 ...`; then prove the separate root-value equality using
`hrootVal`; only after the outer sum has the form
`sum z in S, L x' (e z) ...` is `Equiv.sum_comp e` invoked.
This changes neither the matrix factor order nor the theorem hypotheses.
The previous failed SHA is retained as a failure record; the new full Lean
build is required before proceeding.
## 2026-10-31 — H8 transport: separate same-domain normalization and equivalence reindexing

The first follow-up patch after run 41169771612 still had a structural
proof error: it attempted `Finset.sum_congr rfl` directly between a sum
over `{z : W // z ∈ S}` and a sum over `{z : V // z ∈ T}`. These are
different index types; pointwise congruence cannot bridge them.

The hpow2Row chain is now explicitly split into two independent steps:
(1) a same-index-type sum over S, where `hrootVal` changes the fixed
root `(e xr).1` to `x'` pointwise; (2) a separate `Equiv.sum_comp e`
step transporting the already-normalized S-sum to the T-sum.
This is a proof-structure correction, not a new mathematical assumption.
The full Lean result for the intermediate SHA must not be treated as
verification; a fresh full build is required for the corrected SHA.
## 2026-10-31 — H8: radius-three corner coordinate transport

Added only the geometric coordinate layer in CornerLocality.lean:
- corner_O_radius_three_transport: the level-(m+1) O box [0,3]^2
  lies in the old A copy and avoids its two non-root glued corners;
- corner_X_radius_three_transport and corner_Y_radius_three_transport:
  the corresponding boxes lie in B and C, with the inverse-copy points
  avoiding the respective glued corners;
- exact X/Y radius-three box equivalences under the B/C shifts.

All statements use m >= 4, so 3 < 2^m and 2^m + 3 < 2^(m+1).
This is the first geometric input needed by the already-compiled generic
degree-six/seven diagonal transport lemma. No matrix-entry, spin, axis,
operator-power, r=6 trace, or residual-stability claim is included.
Full Lean and Python CI on the exact resulting SHA are required.

## 2026-10-31 — H8 radius-three transport repair

Lean run 41171919726 on parent SHA 6ded225b630b5a632124de487040819182f540ef reported two proof-script failures in CornerLocality.lean (lines 543 and 614). The X-copy proof had not normalized the untouched shifted y-bound before excluding parent point (0, 2^m); the symmetric Y-copy proof had not normalized x before excluding (2^m, 0). Both coordinate hypotheses are now explicitly simplified after the copy substitution, before omega. Statements, assumptions, and m >= 4 threshold are unchanged. This is a local proof-script repair only; full Lean and Python CI on the new SHA are still required. WSG support equivalences and H8 residual stability remain open.


## 2026-10-31 — H8 radius-three WSG support: O-corner reindexing

- The exact parent commit 90ba45a was rechecked: the full Lean formalization build and both Python 3.11/3.12 suites, including the slow tests, completed successfully (Actions runs 41174250278 and 41174250275).
- Added the concrete finite-state radius-three support around O in FinalTilde.lean. The support equivalence retains the copy index, coordinate, and spin, and uses corner_O_radius_three_transport at the geometric layer.
- The result is only a finite-set equivalence. It does not yet prove equality of high/low operator entries on the support, row/column support for powers one through three, any of the six corner transports, or H8 boundary-residual stability. The next step is to prove the corresponding O-corner spin-resolved entry bridge on the radius-three support and then derive row/column support for degrees 1–3.
- Full Lean and Python CI on the new exact SHA are required before treating the addition as verified.

## 2026-10-31 — H8 radius-three O-corner spin-resolved entry transport (CI verified)

Added the pointwise matrix-entry bridge for the O radius-three neighborhood,
with the two spin indices retained explicitly:
- the A-copy/O entries reduce to the parent through
  corner_O_radius_three_transport and pHeO_succ_A_num_entry;
- the B-copy/O entries use a radius-three exclusion of the shifted cp1 edge,
  then the existing oBo-to-numbering restriction and the O/A next-number
  entry transport;
- the C-copy/O entries keep the C orientation conversion through
  Hc_C_num_eq_parent_til separate from the O-box cp1 exclusion and the
  O/A point-entry transport.

All new statements retain m >= 4. They are entry equalities only:
no row/column support for powers 1, 2, or 3, no six/seven diagonal
transport instantiation, and no H8 boundary-residual stability is claimed.
Verification completed on the exact commit 9dabd9c56c4bbd10819116901a18ab4a046aabfc:
full Lean build passed (run 41177720579), and Python 3.11 plus 3.12
passed both fast and slow suites (run 41177720577).


## 2026-10-31 — H8 radius-three support: column vanishing

- Rechecked the exact parent SHA 9dabd9c56c4bbd10819116901a18ab4a046aabfc:
  the full Lean build and both Python 3.11/3.12 fast and slow suites passed.
- Added symmetry of the copy-preserving radius-three support. The proof
  swaps the two coordinate-distance inequalities in each coordinate and
  reverses the copy equality.
- Derived the column-zero statement for every degree n <= 3 from the
  existing row-zero theorem, using that support symmetry. No new locality
  assumption or geometric lemma is introduced.
- This supplies the column side only; together with the already-proved row
  form it gives both support directions needed by the generic local
  degree-six/seven diagonal transport. The O-corner specialization,
  other corners, and H8 boundary-residual stability remain unproved.
- Full Lean build and Python 3.11/3.12 fast and slow suites must be checked
  on the new exact SHA before proceeding.

## 2026-10-31 — O radius-three A-copy entry bridge

- Parent 0c490c23e0c89e4e0a4596512ef232591a076c1b passed the full Lean
  build and Python 3.11/3.12 workflows.
- Added the A-copy spin-resolved O radius-three entry bridge using the
  existing O/A next-number identity, and a dispatcher covering A, B, C.
- This completes the local matrix-entry bridge for every copy pair in the
  O radius-three support. It does not yet prove the degree-six/seven
  diagonal transport or the H8 boundary residual recurrence.
- Run full Lean and both Python suites on this exact new SHA before
  continuing.

## 2026-10-31 — Repair Lean namespace placement in O entry bridge

Lean run 41185762593 failed because the A/O entry bridge and the common
A/B/C dispatcher had been appended after the final `end EvgenyTheorem`
in FinalTilde.lean. Consequently their names (Axis, Point, GCopy, sgK,
pHeO, vertexOrder) were out of scope. The declarations are now moved
inside the existing EvgenyTheorem namespace. The failed Lean run did not
reach proof checking of these declarations, so the fresh full build is
required to reveal and address any proof-level issues. The Python 3.12
job passed; Python 3.11 was still running when the Lean failure was
inspected.

## 2026-10-31 — O radius-three diagonal transport for powers six and seven

- Verified parent commit 4848115f5962aee64f4faa0041393a60db25fb1c:
  the full Lean build passed (run 41186359604), and Python 3.11 and 3.12
  passed both fast and slow suites (run 41186359631).
- Added one generic O-corner theorem covering every GCopy label. It
  instantiates the radius-three support equivalence, the spin-resolved
  A/B/C entry dispatcher, and row/column vanishing through degree three.
- The existing finite-matrix lemma then identifies the degree-six and
  degree-seven diagonal entries across levels m+1 and m. No axis-periodicity
  assumption is needed at O.
- This closes the O-corner diagonal-transport component only. Other corner
  transports and the H8 boundary-residual comparison remain open; H8/H10
  are not claimed closed. Full CI on the new SHA is required next.

## 2026-10-31 — Repair O diagonal transport copy equality

The first Lean check of commit cfc75dea7ecf2f04d65e32a9c242429b345174b9
reported one type mismatch in the parent-support inclusion inside
sgK_O_diag_six_seven_transport. After unpacking radius-three support, the
copy equality was z.1 = x'.1, while the parent support asks for z.1 = w.1.
The local abbreviation x' is sgK_root_pullback m w, whose copy projection
is definitionally w.1. The proof now records x'.1 = w.1 by rfl and composes
the equalities explicitly. No geometric premise or theorem statement changed.
The previous Lean run therefore remains failed until a fresh full build of
this repair succeeds.

## 2026-10-31 — H8 radius-three X/Y finite-state support equivalences

- Rechecked the exact parent commit 18db05df1adacc6c1216ffb84723e65c8069bac8:
  the full Lean build passed, and Python 3.11/3.12 fast and slow suites
  both passed.
- Added coordinate-box characterizations for the X and Y radius-three
  neighborhoods using the already-proved corner_X_radius_three_box_iff
  and corner_Y_radius_three_box_iff results (m >= 4).
- Added parent-level finite support sets and explicit finite equivalences:
  inverse B shift at X and inverse C shift at Y. Both equivalences keep the
  copy label and spin unchanged.
- This step proves only equality/reindexing of the finite state supports.
  It does not prove pointwise matrix-entry equality, row/column vanishing
  for powers 1--3 under the corner shifts, sixth/seventh diagonal transport,
  or H8 boundary-residual stability. H8/H10 remain open.
- Full Lean build and Python 3.11/3.12 fast and slow suites must be checked
  on the new exact commit before any further code changes.

## 2026-10-31 — H8 X radius-three spin-resolved entry bridges

- On parent commit b5d09f34789931823488164327833d0ab03e9e9d, the full
  Lean formalization build passed; Python 3.12 fast and slow suites passed,
  and Python 3.11 fast passed. Its slow suite was still running when this
  change was prepared, so the next commit is gated on that exact check
  finishing successfully.
- Added a point-level X radius-three entry transport using
  corner_X_radius_three_transport. It explicitly uses the two excluded
  B-shift endpoints and reconciles the high tilde, B-local, and parent
  tilde orientations.
- Added the state-level X entry bridges for copies A and C, including the
  C-copy orientation conversion via Hc_C_num_eq_parent_til.
- No X diagonal transport has been claimed yet: the finite-support entry
  equivalence still needs to be assembled with the degree-1--3 row/column
  support transfer. Y radius-three entry bridges remain open. H8/H10 remain
  open.

## 2026-10-31 — Correct C-block X radius-three orientation index

- The Lean build for commit 818fc0cc12e5309f63ab23dde800419c48e16149
  exposed two type mismatches in the C state bridge. The point lemma used
  there had the A-block orientation transition oTil (m+2) to oTil (m+1),
  while Hc_C_num_eq_parent_til requires the C-block conversion to meet at
  oTil (m+1) on the high level and oTil m on the parent level.
- Replaced that composition with a dedicated radius-three point-entry
  bridge modelled on the already compiling radius-two theorem
  pHeO_corner_X_box_entry_next_til. It uses pHeO_succ_B_local_entry
  with the parent tilde orientation and the existing faceB orientation
  transport, so the exact endpoint types now match the C conversion.
- The A-block theorem is unchanged. This is a correction of the current
  C-block proof only; no diagonal transport or H8/H10 closure is claimed.

## 2026-10-31 — Align C-state calc with the radius-three parent entry

- The second Lean attempt reached and compiled the new point-level
  radius-three parent-tilde bridge. It reported only the two dependent
  C-state calc mismatches at the composition around hentry and hLowC.
- The precise issue was a single intermediate calc target: hentry has
  parent endpoint pHeO m ... (oTil m), but the written intermediate target
  incorrectly used oTil (m+1). Changed that target to oTil m, allowing
  hLowC.symm to start at its actual left endpoint. The final C-orientation
  conversion remains unchanged.
- No other proof declarations were altered. Await a full Lean build on
  this exact correction before proceeding.


## 2026-10-31 — X radius-three sixth/seventh diagonal transport

- Added a common X-corner diagonal transport theorem parameterized by a
  spin-resolved local-entry bridge. It uses the radius-three X support
  equivalence and the root pullback at (2^m, 0), not the O-corner origin.
- The proof explicitly verifies the parent X support contains the pulled
  root and that every radius-three state around that parent root lies in
  the parent X support. It transfers row and column vanishing for powers
  one, two, and three on both levels, then applies the existing finite
  matrix identity for powers six and seven.
- Instantiated the common result for the A and C copies using the two
  already-established X radius-three spin-resolved entry bridges.
- This completes the X/A and X/C local diagonal-transport components only.
  The B/Y partner cases, the full H8 boundary-residual stabilization, and
  H10 remain open. The new declarations are provisional until full Lean
  CI and both Python test versions pass on this exact commit.


## 2026-10-31 — X diagonal theorem declaration ordering correction

A source review caught that the first insertion placed the X diagonal theorem
before the matrix identity and entry-bridge declarations it depends on.
Moved the theorem block after all of those declarations, at the end of
FinalTilde.lean, and made the local bridge's membership proofs explicit in
its binder types. This is a source-ordering correction, not a change to the
mathematical statement. The prior SHA is not considered validated; full CI
must run against this corrected SHA.


## 2026-10-31 — Make the parent X-copy inclusion explicit

A second source-level audit of the X diagonal proof identified that the
low-level support inclusion must also transport the copy coordinate from
the pulled-back root to the fixed parent copy c. The proof now derives
x'.1 = c directly from sgK_root_pullback and the theorem premise
hwCopy, then composes it with the support's copy equality. This closes
that inclusion obligation explicitly; the corrected SHA still requires a
full Lean build and both Python suites.


## 2026-10-31 — Correct X diagonal support center and column arguments

The failed Lean run on the initial X diagonal commit identified three
concrete errors. The parent support must be indexed by w.1, because that is
the codomain of the X support equivalence; its root copy coordinate is
definitionally w.1. The low-support inclusion now composes the copy
equality with this exact coordinate identity. In addition, the radius-three
column-vanishing helper already performs support symmetry internally, so
its center/outside arguments must be passed in row order (root, outside),
not reversed. Corrected these argument orders for powers one through three
at both levels. The timeout/unknown-constant diagnostics are being checked
again after these primary type errors are removed; no success is claimed
until the fresh full Lean build passes.


## 2026-10-31 — Y radius-three spin-resolved entry bridges

- Added a radius-three Y/C point-level entry bridge at the numbering
  orientation, using the established Y radius-three geometric pullback
  and the C-local entry theorem. The hypotheses explicitly exclude the
  two exceptional C-shift endpoints for m >= 4.
- Added the exact parent-tilde version by converting the C orientation
  with Hc_C_num_eq_parent_til and using the radius-three exceptional-edge
  exclusion on the parent box.
- Packaged the point transport as state-level bridges for copies A and B.
  The B wrapper separately removes the B orientation flip using
  cp1_not_B_shift_radius_three at both levels and cp1_not_O_radius_three
  on the high level.
- These are entry-level results only. They do not yet prove Y diagonal
  transport for degrees 6/7 or H8 boundary stabilization. The previous
  SHA's Python 3.11 slow job was still in progress when this commit was
  made; this fact is recorded separately from the new SHA's CI status.

 
## 2026-10-31 — Assemble Y radius-three diagonal transport
 
- Fixed the two Y bridge argument mismatches by deriving 3 ≤ m from
  the existing 4 ≤ m hypothesis.
- Extended the existing finite-support matrix identity to return the
  diagonal comparisons for powers 1, 2, and 3 together with powers 6 and 7.
  The support equivalence and row/column locality hypotheses are unchanged.
- Adapted the existing X support-local diagonal assembly to the Y/C shift,
  using the already-proved Y support equivalence and A/B entry bridges.
- Added the six-case glued-partner assembly for diagonal powers 1, 2, 3, 6,
  and 7. Powers 4 and 5 remain supplied by the existing radius-two
  dispatcher used in the sixth-moment boundary argument.
- This assembles local diagonal-transport infrastructure only; it does not
  claim H8/H10 closure.

 
## 2026-10-31 — Repair Y support transport and assemble diagonal powers one–seven
 
- Corrected the two Y entry-bridge natural-number arguments by deriving
  3 ≤ m from the existing 4 ≤ m hypothesis.
- Corrected the Y diagonal transport specialization to use the C-shift
  periodicity 2 * 3^m, parent root (0, 2^m), Y parent support, Y support
  equivalence, and Y box equivalence for both endpoints.
- Corrected the high-level B/Y orientation for powers 3, 6, and 7 to
  oTil (m+2).
- Combined the existing O/X/Y transports for powers 1, 2, 3, 6, and 7 with
  the established fourth/fifth-power six-case dispatcher into one
  glued-partner theorem returning powers 1–7.
- This is an intermediate transport/assembly result; no H8/H10 closure
  is claimed.

 
## 2026-10-31 — H8 boundary correction in diagonal normal form
 
- Added a three-kernel supported-diagonal trace identity. It keeps distinct
  middle powers and the original ordered factors; no matrix factors are
  commuted.
- Added glued-state off-diagonal vanishing for powers through degree five,
  combining same-copy geometric vanishing with block-diagonal copy separation.
- Reduced all ten four-N H8 boundary terms and all four six-N H8 traces to
  products of diagonal powers at a glued state and its partner. The r=2 and
  r=8 strata retain their exact diagonal formulas.
- Proved the exact identity glueRHS8 = glueRHS8_diagonal_form, preserving
  every even stratum and its cyclic multiplicity. No cancellation, omitted
  term, or level-stability assumption is introduced in this reduction.


## 2026-10-31 — Recovery audit and verified continuation boundary

Restored `work/h8-h10-exact-recurrence-certificates` to the last same-SHA
green checkpoint `575597d5d66dd5c5de9044a9c15f284a23669388` after auditing
the branch head, commit ancestry, research journal, proof journal, and
Actions. Verification on that exact commit:

- Full Lean build: run `41227907808`, success.
- Python 3.11 and 3.12 fast and slow tests: run `41227907792`, success.

H6 remains closed on `main` via merged PR #9; no H6 source, PR, or main
branch state was modified.

At the restored H8 checkpoint, the exact full trace split, the 19-term
positive-even boundary functional, and its complete diagonal normal form
are compiled. The exact defect recurrence still retains the full boundary
difference. The numbering/flipped-orientation boundary comparison is
proved through degree seven, and the corresponding orientation gap is
constant from level four onward. What is missing is the common residual's
adjacent-level transport between faceAxis and the constant axis. The
radius-three local transport results alone do not imply that global
19-term comparison. No fixed H8 residual constant or H8 closed form is
currently established.

H10 remains a set of individual conditional boundary reductions, not a
complete ordered p=10 trace split or a proved weighted even-stratum
comparison. Do not start H10 residual propagation before H8 is closed.

The attempted commits after `575597d5` (`acf6e6a`, `167d15a`,
`019c510`, `ba837d4`, `8f969cd`) were excluded from the restored
working head because their Lean workflows failed. Specifically,
`8f969cd` failed in the proposed H8 constant-boundary algebra at
`linear_combination hgap`; it did not verify the proposed affine
recurrence or closed form. Do not reuse those failed declarations without
re-deriving and independently checking the missing hypotheses.

**Next step:** prove one precise theorem on top of the restored source:
adjacent-level invariance of the common H8 boundary residual under the
face-axis versus constant-axis comparison for the flipped orientation.
Build its hypotheses from the existing six-case glued-partner transport
and the 19 explicit diagonal pair-product terms. Compile that theorem
before adding a constant definition, scalar recurrence, or H8 closed form.


## 2026-10-31 — Exact H8 level-two base transition and coefficient

- Added computational/p8_base_certificate.py. It computes the full p=8
  trace polynomials at levels 2, 3, and 4 with sparse 2x2 block arithmetic
  over Gaussian-integer polynomial coefficients in c=cos(theta/2) and
  s=sin(theta/2). No floating-point values enter the certificate.
- The raw defects satisfy coefficient-by-coefficient
  D_3 - 3 D_2 = D_4 - 3 D_3. The common raw polynomial reduces under
  c^2+s^2=1 to
  C_8 = 193600 s^2 + 75776 c s^2 + 83712 s^3 - 512 c s^3 + 192 s^4.
- The reduced level-two value is
  D_2 = -1335552 s^2 + 244352 c s^2 - 40064 s^3
        + 64 c s^3 + 1920 s^4.
- Added affine_three_recurrence_from_two and the conditional Lean wrapper
  defectO8_num_affine_closed_form_from_level2. The wrapper exposes the
  exact finite base equation as its only extra hypothesis; the separate
  Python polynomial certificate discharges that finite bridge.
- Added exact raw/reduced coefficient assertions and independent theta=pi
  comparisons against the Gaussian-integer trace certificate. The exact
  p=8 symbolic test is marked slow because it also computes level four.
- H10 remains deferred. Full Lean and Python CI for this commit is pending.


## 2026-10-31 — Complete the remaining H10 four-N class specializations

- Audited the generic p=10 four-N class inventory in GlueAlg.lean.
  It contains nine cyclic representatives: 1162, 1153, 1117, 1126, 1216,
  1135, 1144, 1225, and the period-two class 1414.
- The Sierpinski GlueTrace.lean specialization previously contained only
  the first five. Added the remaining four concrete wrappers:
  1135, 1144, 1225 (each multiplicity 10), and 1414 (multiplicity 5).
- Each wrapper uses the existing degree-nine glued-state off-diagonal
  vanishing theorem. The exact ordered factors and outer/inner diagonal
  powers are copied from the generic GlueAlg theorem; no factors are
  commuted or merged.
- This completes the class-level r=4 wrapper inventory only. No combined
  four-N stratum theorem, no complete p=10 ordered expansion, and no H10
  boundary recurrence are claimed yet. Full Lean build and Python suites
  are pending on the new SHA.


## 2026-10-31 — Assemble the complete H10 four-N cyclic stratum

- Corrected the prior partial inventory: the nine named class lemmas in
  GlueAlg.lean are not all cyclic compositions of four positive K-run
  lengths summing to ten. The full set has 22 cyclic representatives.
- Enumerated all positive compositions of 10 into four parts modulo cyclic
  rotation. There are 20 orbit-size-four classes and two period-two classes:
  (1,4,1,4) and (2,3,2,3). No period-one class exists because 4 does not
  divide 10.
- Added a parametric Sierpinski boundary-sum definition and reduction for
  arbitrary four positive powers. It uses the existing degree-nine support
  theorem and the generic trace_four_N_powers_explicit without changing
  matrix-factor order.
- Added sg_trace_p10_four_N_stratum_boundary, listing all 22 representatives
  with exact coefficients 10 for orbit-size-four classes and 5 for
  period-two classes. The coefficient total is 20*10 + 2*5 = 210 = C(10,4).
- This closes the boundary reduction for the whole r=4/four-N stratum,
  not H10 as a whole. The remaining H10 work still includes complete
  expansion/cancellation with the two-N, six-N, eight-N and ten-N strata,
  and proving the resulting boundary residual stabilizes by level.
- Full Lean and Python CI are pending for the new commit.


## 2026-10-31 — Correct H10 four-N support threshold

The first CI run of the aggregate four-N theorem exposed a genuine hypothesis
m >= 4: the generic degree-nine support theorem
sgK_pow_hkg_up_to_nine_of_OAnti requires m >= 4, while the new parametric
wrapper had been stated for m >= 3. The aggregate theorem itself already
assumes m >= 4. Tightened the helper's lower-bound premise to m >= 4,
matching the exact dependency; no mathematical claim or matrix identity
was changed.


## 2026-10-31 — Assemble the complete H10 six-N cyclic stratum

- Enumerated all positive six-tuples summing to ten modulo cyclic rotation.
  Burnside's count gives (126 + 6) / 6 = 22 classes: 20 have orbit size
  six and two have orbit size three. The period-three representatives are
  (1,1,3,1,1,3) and (1,2,2,1,2,2).
- Added the ordered three-diagonal boundary term and a parametric
  specialization of the generic six-pairing boundary lemma, using the
  existing degree-nine support theorem for the three selected middle powers.
- Added sg_trace_p10_six_N_stratum_boundary, with all 22 cyclic
  representatives. The 20 full-orbit classes have coefficient 10;
  the two period-three classes have coefficient 5. The weights sum to
  210 = choose(10,6), the exact number of placements of six N factors.
- This completes the six-N/four-pairing boundary reduction only. It does
  not establish cancellation with the two-N, four-N, eight-N or ten-N
  strata, or an H10 residual recurrence. Full Lean and Python CI are pending.


## 2026-10-31 — Scope the H10 six-N aggregate elaboration budget

The first CI attempt for sg_trace_p10_six_N_stratum_boundary did not
report a type mismatch or a failed boundary identity. Lean exhausted its
default 200000-heartbeat budget while reducing the declaration's large
22-term matrix-trace expression at GlueTrace.lean:2244. Scoped a larger
heartbeat budget (1000000) to this aggregate theorem alone. No project-wide
option was changed, and no proof hypothesis or mathematical statement was
altered. The theorem still needs a fresh full Lean build.



## 2026-10-31 — Formalize the H10 three-N odd stratum

- Added `sg_trace_p10_three_N_stratum_zero` in GlueTrace.lean.
- Enumerated all 12 cyclic classes of positive triples summing to ten;
  each has multiplicity 10, giving total weight 120 = C(10,3).
- Preserved every matrix-factor order and used cyclic trace rotation to
  invoke the existing three-N corner-vanishing theorem. The selected
  middle exponents are at most three, below 2^m for m >= 3.
- Only the r=3 odd stratum is closed by this theorem. Other odd strata,
  the total ordered p=10 expansion, and the boundary recurrence remain open.


## 2026-10-31 — Correct Lean tactic-location syntax in H10 r=3 proof

The first retry revealed that the multiline `simp ... at` location list
was parsed incorrectly. Replaced it with separate explicit simplification
commands for each of the twelve established zero-trace identities and the
target. This is syntax-only; no hypotheses or mathematical statements change.


## 2026-11-01 — Fix the H10 r=3 weighted-sum coefficient

The full Lean build exposed that each of the twelve cyclic representatives
appears with coefficient 10 in the stratum, while the final
`linear_combination` had used each zero-trace identity with coefficient 1.
After normalization this left a residual coefficient 9 on every trace.
The proof now combines each established zero-trace equality with
coefficient 10, matching the exact orbit weights. No class inventory,
trace representative, or theorem hypothesis was changed.

## 2026-11-01 — Revert the unvalidated H10 r=5 experiment

The r=5 proof attempt was removed after repeated full Lean failures. The
last attempted commit, 5dccef5651023c621345470cb67e1a55169da93b, still
fails deterministically at WHNF in GlueTrace.lean:4464:50, 4534:10, and
4513:0 (200000 heartbeats). The first location is in the generic cyclic
rotation step based on Matrix.trace_mul_comm; the latter locations arise
while elaborating the dependent aggregate theorem. Raising the local budget
to 1000000 and changing the representation did not resolve the failure.

Restored GlueTrace.lean to the source at the last fully green H10 checkpoint,
ca9580afd4b42b40935f96bab15746b33ff6900d. This retains all Lean-validated
work present at that checkpoint. H10 r=5 is explicitly still open; no
five-N zero theorem is claimed. The Python workflow passed on 5dccef5, but
that does not override the failed Lean build. The restored branch head needs
a fresh full Lean build and test run.

## 2026-11-01 — Diagnose and correct the first H10 r=9 wrapper

The first wrapper was mathematically malformed: it placed K^0 in every
gap after the first N, although every N in the ordered expansion comes
from a K*N letter. The r=9 word has nine N factors and ten K factors.
That version therefore did not represent the intended cyclic class.
Its full Lean build also failed with WHNF timeouts at GlueTrace.lean:5093
and 5071 while elaborating the expanded expression. The attempted wrapper
is withdrawn and is not a verified theorem.

## 2026-11-01 — Correct H10 r=9 cyclic-class representative

Replaced the malformed expression by the exact cyclic representative
K^1*N*K^1*N*...*K^1, with nine N factors and ten K factors.
Introduced the compact term definition
`sg_trace_p10_nine_N_class_term` so the theorem statement does not
repeatedly elaborate the full matrix product. The proof unfolds only this
single term and applies `trace_nine_N_powers_zero_of_OAnti` with all ten
K exponents equal to one. The four required middle-power bounds follow
from m >= 3. This is one class-level weighted contribution, not the
complete H10 expansion. Full Lean validation is pending.

## 2026-11-01 — Diagnose the helper typeclass failure in H10 r=9

The full Lean build of commit 8b5bdb6b7783e9cb1c907050f6565a8f09682aa5
failed at GlueTrace.lean:5079–5081 because the new generic helper quantified
over an arbitrary matrix index type with [Fintype n] but omitted
[DecidableEq n]. Lean therefore could not synthesize the matrix power
instance. The later `sorry` and unused-tactic diagnostics were downstream
consequences of that failed elaboration, not accepted proof results.

The helper is being specialized to the project's actual index type WSG m,
which already supplies the required finite-index instances. No hypotheses
or heartbeat settings are weakened or enlarged.

## 2026-11-01 — H10 r=9 Lean validation and r=7 implementation

The full Lean formalization workflow completed successfully on
00d79d8cf2e281d9ce0f09629afe1974b9097e68. This validates the specialized
WSG helper and the r=9 nine-N cyclic-class vanishing theorem. The Python
workflow for this SHA was still reported in progress at the time of the
next edit; no Python result is claimed here.

Added the H10 r=7 cyclic-class reduction. The twelve representatives are
the cyclic orbits of seven positive K-gaps summing to ten, equivalently
the twelve cyclic orbits of seven nonnegative extras summing to three.
A shared helper rotates each representative using trace cyclicity and
applies trace_seven_N_powers_zero_of_OAnti. Its selected middle exponents
are e0+1, e2+1, and e4+1; each is at most four, hence below 2^m for m >= 3.
The aggregate theorem keeps all twelve orbit weights equal to ten.
The new r=7 declarations are pending a fresh full Lean build.

## 2026-11-01 — Pre-build syntax correction in H10 r=7 helper

A final source review of 5ecd458b59f9ad0007e30a252b7b0f2094ab15ac
found a missing closing parenthesis around the `trace_cyclic_list`
application in the shared r=7 rotation helper. The call is closed in this
follow-up commit. This was caught by source inspection while the CI job was
still setting up the Lean toolchain; the r=7 theorem remains unvalidated
until a full Lean build succeeds.

## 2026-11-01 — Replace the failed generic H10 r=7 rotation

The full Lean build on 528ab3a5e0e431b121e061d90fcff41c11c4fc5d failed
deterministically at the generic helper's symbolic-power normalization:
GlueTrace.lean:5112:4 timed out in isDefEq and the helper declaration
then timed out at 5082:0 during WHNF. The later unknown-constant diagnostic
was downstream from the unbuilt helper. Increasing heartbeat limits would
repeat the unsuccessful strategy already ruled out by earlier r=5 work.

The generic helper has been removed. The replacement keeps the compact
word definition but proves the twelve representatives separately. Each
cyclic rotation now uses the same explicit finite-list pattern as the
Lean-validated p=10 r=3 proof in this file, with only concrete exponents.
Each rotated trace is discharged by trace_seven_N_powers_zero_of_OAnti;
the three selected middle exponents are at most four. The replacement
full Lean build is pending; no r=7 success is claimed yet.

## 2026-11-01 — Add the uniform numerical corner bound to explicit r=7 cases

Review of the generated concrete cases found that their three strict
middle-exponent bounds need the shared fact 4 < 2^m, derived from m >= 3.
This fact is now established once at the start of the r=7 theorem; the
individual `omega` proofs then use the concrete exponents (each at most
four). This is a source-level correction made before relying on the new
CI result; full Lean validation remains pending.

## 2026-11-01 — Remove orphaned H10 r=7 helper documentation

Lean CI on 2b47d1a36e81300a41b9d06e51c429c397861195 failed at
GlueTrace.lean:5086:30 with `unexpected token '/--'; expected 'lemma'`.
The generic helper body had been withdrawn, but its preceding doc-comment
was accidentally left immediately before the new stratum theorem's doc-comment.
The stray comment has now been removed. The two Python jobs on that SHA
were still in progress when checked; no Python failure is recorded or claimed.
A fresh Lean build and both test jobs are required for this corrected source.

## 2026-11-01 — H10 r=5 cyclic stratum

Added the full p=10 five-N vanishing stratum using the established
trace_five_N_powers_zero_of_OAnti theorem. The 126 weak compositions of
five extra K factors into five cyclic gaps form 26 cyclic classes.
Twenty-five representatives have five distinct cyclic rotations and
therefore binary-word orbit weight ten; the periodic representative
(1,1,1,1,1) has orbit weight two. The weights sum to 252, matching
the number of ordered words with five K*N selections.

Each representative is expressed by a compact class-term definition.
Its trace is rotated explicitly by moving the final [K,N] pair to the
front, then normalized with concrete exponents (no symbolic-exponent
normalization). The five-N lemma applies with its two required middle
powers b=e0+1 and d=e2+1, each at most six. Since m >= 3, 6 < 2^m.
This new stratum is pending full Lean validation.


## 2026-11-01 — Withdraw the failed H10 r=5 rotation proof

The full Lean build on 4f9b0a18c2875c0149d31846eb16bc3c5cd9025c failed deterministically in the new r=5 declarations. The first concrete rotation equality times out at GlueTrace.lean:5413, and the r=5 helper/theorem elaboration also times out at GlueTrace.lean:5365. This is the same expensive trace-word normalization failure seen in the earlier r=5 attempts; making the representative compact did not make the explicit cyclic-rotation proof tractable. The r=5 theorem is withdrawn in this commit, restoring GlueTrace.lean exactly to the preceding green checkpoint 542006e0dae9910d6738d2386eaefa17d32e0081. The successful r=9 and r=7 layers are preserved. Do not retry the same explicit `trace_cyclic_list` expansion or increase heartbeat limits; first develop and independently validate a genuinely smaller rotation lemma or a different algebraic decomposition.

## 2026-11-01 — Rotation-free H10 r=5 representative lemma

After withdrawing the failed r=5 rotations, the gap word was re-examined
against the actual statement of trace_five_N_powers_zero_of_OAnti.
A representative
K^e0*(K*N)*K^e1*(K*N)*...*K^e4*(K*N) is already its required
five-N normal form after combining each K^ei*K into K^(ei+1);
the final exponent is zero. No cyclic trace rotation is mathematically
necessary. For five nonnegative gaps summing to five, the two constrained
middle exponents are e1+1 and e3+1, each at most six and hence below
2^m for m >= 3.

Added only the reusable gap-word vanishing lemma, not the 26-class
aggregate. Its full Lean validation is pending. This isolates the
power/associativity conversion before attempting the weighted stratum.

## 2026-11-01 — H10 r=5 weighted cyclic stratum from the rotation-free lemma

The full Lean build succeeded for the generic rotation-free gap-word lemma
on 26fff07391f9b8e58012ffc16fdd3748cb9a0813. This next change adds
the weighted aggregate over the 26 canonical gap necklaces and proves
each representative by direct application of that generic lemma.
No trace rotation is used. The 25 aperiodic classes have weight 10;
the all-ones gap tuple has weight 2. An independent enumeration checks
that there are 126 weak compositions, 26 cyclic classes, and total
binary-word orbit weight 25*10+2 = 252 = choose(10,5).
The aggregate requires a new full Lean build; it is not called validated
until that build succeeds.

## 2026-11-01 — Diagnose and isolate the p=10 cyclic-expansion simp timeout

The first Lean run for the new exact p=10 cyclic trace grouping reached
TraceExpand.lean:3204 and exhausted the standard 200000-heartbeat budget in
one of the generated rotation equalities. This was not a mathematical
counterexample: each equality is an instance of the already-proved
trace_cyclic_list theorem. The generated proof used unrestricted
`simpa [Matrix.mul_assoc]` while hundreds of earlier rotation equalities
were already in the local context, allowing the simplifier to inspect an
unnecessarily large local rewrite context. The correction restricts each
normalization to the explicit List.prod and matrix-associativity lemmas and
restricts the final ordered-expansion normalization to its explicit list
recursion lemmas. No heartbeat limit is raised. This correction is pending
full Lean CI; do not treat the 108-class p=10 cyclic expansion as validated
until the new SHA passes the complete build.

## 2026-11-01 — Replace the monolithic p=10 rotation context with 16 bounded blocks

The restricted-simp retry still failed in TraceExpand.lean:3480, now inside
`isDefEq` while elaborating another generated rotation equality. This confirms
the bottleneck is the single theorem's accumulating context of hundreds of
local equalities, not the simp set alone. The proof is therefore reorganized
into 16 suffix blocks, each containing exactly 64 words and its own local
rotation facts. A separate order-preserving append-expansion lemma splits the
full degree-ten list into its six-letter prefixes and four-letter suffixes;
the 16 block identities then assemble the same 108 cyclic representatives
with the same exact orbit weights. No change is made to the matrix identities,
stratum counts, assumptions, or heartbeat limits. Full Lean validation of the
new structure is pending.
