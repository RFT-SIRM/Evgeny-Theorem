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
