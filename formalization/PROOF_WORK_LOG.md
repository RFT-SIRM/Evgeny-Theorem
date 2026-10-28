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
