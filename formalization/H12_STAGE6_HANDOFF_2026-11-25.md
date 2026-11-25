# H12 Stage 6 handoff — 2026-11-25

## Saved working state

- Branch: `research/h12-full-trace-split`
- Parent commit before this preservation commit: `f8a123cabe3b566bf0af1bf95914b357744d44f8`
- Saved at: 2026-11-25 20:31:04 UTC
- Lean: `Lean (version 4.33.1, arm64-apple-darwin24.6.0, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)`
- Lake: `Lake version 5.0.0-src+819816b (Lean version 4.33.1)`

This note records the local Stage 6 state on top of the branch above. It is an
addendum to the earlier H12 research-log entries, not a rewrite of the older
proof boundary. In particular, the earlier statement that the level-three to
level-four bridge was still open is superseded by the Lean result below.

## Machine-checked H12 result

The following declarations are present in `formalization/EvgenyTheorem/FinalClosed12.lean`:

- `defectO12_succ_num_level3_constant_boundary`: for every real `θ` and
  every `m ≥ 3`, the numbering-orientation H12 defect obeys
  \[
  D_{m+1}^{(12)}(θ)=3D_m^{(12)}(θ)+C_{12}(θ).
  \]
- `defectO12_num_finite_base_bridge_level3`: the explicit finite bridge
  \(D_4^{(12)}=3D_3^{(12)}+C_{12}\).
- `defectO12_num_affine_closed_form_from_level3_unconditional`: the affine
  solution for every \(n\ge0\), equivalently every level \(m\ge3\),
  \[
  D_{n+3}^{(12)}(θ)=3^n\left(D_3^{(12)}(θ)+\frac{C_{12}(θ)}2\right)
                 -\frac{C_{12}(θ)}2.
  \]

Here \(C_{12}(θ)\) is the exact finite level-five trace residual
`defectO12_num_residual_constant θ`, defined in Lean from the positive-even
boundary contribution and the level-five orientation gap. The finite bridge
at \(m=3\) is no longer an external numerical assumption: it is derived in
Lean from the level-three boundary and orientation-invariance theorems.

The source chain includes the level-twelve trace expansion and positive-even
stratum/orientation transport in `GlueTrace12.lean`,
`GlueRows12Orientation.lean`, `FinalOrient12.lean`, and
`FinalClosed12.lean`.

## Verification recorded at preservation time

- The operator reported a successful full `lake build`: **3070 jobs built
  successfully**. This was the full build immediately before this handoff;
  this script does not modify Lean source and intentionally does not repeat
  that build.
- The two H12 exact Python regressions were rerun by this script on the current
  worktree: `test_p12_level4_base_bridge.py` and
  `test_p12_level5_affine_constant.py`. Their exact pytest output is printed
  in the terminal when this script runs.
- `git diff --check` passed before staging.

The Lean build result is local build evidence for this worktree. It is not a
claim that the new local commit has already passed GitHub Actions; no push or
CI run is performed by this script.

## Exact symbolic coefficient: proof boundary

The Python exact-arithmetic certificate in
`computational/higher_moment_p12_level5_constant.py` reduces the level-five
constant modulo \(c^2+s^2=1\), with \(c=\cos(θ/2)\) and
\(s=\sin(θ/2)\). Its factored form is
\[
C_{12}(c,s)=-64s^2 Q_{12}(c,s),
\]
where
\[
\begin{aligned}
Q_{12}={}&6c^6+6c^5s+240c^5-456c^4s-8858c^4\
&+2466c^3s-33138c^3+618c^2s+1612501c^2\
&+571254cs-18512844c-3259668s+13167067.
\end{aligned}
\]

This polynomial is an exact Python certificate/regression result, **not yet a
Lean theorem**. The Lean theorem currently retains \(C_{12}\) as the exact
finite trace expression. Likewise, the all-angle recurrence and affine form
are Lean theorems; replacing their finite-trace data by the displayed
trigonometric polynomial in the Lean kernel remains a separate formalization
step.

## Next mathematical step

Formalize the polynomial identity relating the Lean finite-trace definition of
\(C_{12}\) to \(-64s^2Q_{12}(c,s)\) in Lean. Do not describe that polynomial
identity as machine-checked until its Lean theorem compiles. Preserve the
current affine recurrence and its finite base bridge unchanged while doing so.

## Repository procedure

This preservation commit is local to the current H12 work branch. Review its
file list with `git show --stat --oneline HEAD`. Push only after the user
chooses to publish the branch. No merge to `main` is performed here.
