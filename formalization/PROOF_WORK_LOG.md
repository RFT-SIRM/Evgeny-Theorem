# Lean Proof Work Log

Scope: existing PR #9, branch `moment-6-8-10`. Do not create branches, PRs, or issues.

## Incident log

### 2026-10-25 — p=10 supported fifth-power trace lemma

- Commit `066d9de480bb2efa5fa142adca35c25df1103057`: added `trace_alternating_five_supported_diagonal`.
- CI result: Lean build failed in `formalization/EvgenyTheorem/GlueTrace.lean` at line 795. The goal after the attempted cyclic trace rewrite was:
  `(K * (diagonal f * (K * D))).trace = (K * (D * (K * diagonal f))).trace`.
  The proposed `rw [Matrix.trace_mul_comm]; simp [Matrix.mul_assoc]` did not close this goal.
- Commit `caf246c50841c98e6d24bfbc078495424330dc05`: attempted to make the cyclic trace rewrite explicit.
- CI result: Lean formalization failed again. The log contains the unresolved goal above at `GlueTrace.lean:795:56`. The CI job also reports a failed setup retry, but Lean itself ran and reported this proof error; do not misattribute the build failure solely to setup.
- Status: **unresolved; do not treat the p=10 lemma as proved or add dependent proof steps.**

## Required procedure for each next change

1. Read the latest PR head and the complete failing Lean log before editing.
2. Inspect the exact source around the reported line and compare with already compiling lemmas.
3. Make one narrowly scoped correction only; no speculative follow-on lemmas.
4. Wait for the Lean formalization workflow to finish and inspect its log. A green unrelated test workflow is not evidence that Lean compiles.
5. Record commit SHA, exact error or passing result, and next action here.
6. If the proof strategy cannot be justified from the available definitions, stop and report the blocker rather than guessing.

## Current verified status

- PR: https://github.com/RFT-SIRM/Evgeny-Theorem/pull/9
- Working branch: `moment-6-8-10`
- Last source commit checked: `caf246c50841c98e6d24bfbc078495424330dc05`
- Last Lean formalization result checked: **failure**.
