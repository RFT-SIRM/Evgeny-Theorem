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
- Last verified source commit: `30c98f303f58980ea2a764b51883e5c9f8203e1d`
- Last Lean formalization result: **success**.
