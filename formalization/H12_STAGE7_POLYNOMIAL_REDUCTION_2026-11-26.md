# H12 Stage 7 — exact polynomial reduction (2026-11-26)

## Repository checkpoint

- Repository: `RFT-SIRM/Evgeny-Theorem`
- PR #20 merged into `main`
- Merge commit: `f2d0669066e45e0bf8525bd0b4caf27177986805`
- Stage 6 source commit: `27014e7059b14f4ee93fa24c833a129d26f414ba`
- GitHub Actions Lean formalization: **success** (run `45700739229`)
- GitHub Actions Python Tests: **success** on Python 3.11 and 3.12, including both fast and slow test steps (run `45700739188`).
- In this environment, direct `git clone` failed due DNS resolution. Source files were inspected through GitHub's repository API; no claim of a local clone or Lean compilation in this environment is made.

## Lean theorem already proved in Stage 6

`FinalClosed12.lean` proves, for every real `theta` and every `m >= 3`,

\[
D_{m+1}^{(12)}(\theta)=3D_m^{(12)}(\theta)+C_{12}(\theta),
\]

and consequently

\[
D_{n+3}^{(12)}(\theta)=3^n\left(D_3^{(12)}(\theta)+\frac{C_{12}(\theta)}2\right)-\frac{C_{12}(\theta)}2.
\]

The finite bridge `D_4 = 3 D_3 + C_12` is included. In Lean, however, `D_3` and `C_12` are still exact finite trace expressions, not yet replaced by the explicit polynomials below.

## Exact all-angle polynomial candidates

Set

\[
c=\cos(\theta/2),\qquad s=\sin(\theta/2),\qquad c^2+s^2=1.
\]

The full sparse-matrix calculation using the repository's original operator orientation gives

\[
D_3^{(12)}(\theta)=32s^2Q_3(c,s),
\]

where

\[
\begin{aligned}
Q_3={}&-12c^6+24c^5s+1032c^5-2040c^4s-80120c^4\\
&+42894c^3s+2400282c^3-67494c^2s-30361019c^2\\
&-2479593cs+275590614c+3481440s-566815997.
\end{aligned}
\]

The exact finite constant is

\[
C_{12}(\theta)=-64s^2Q_{12}(c,s),
\]

with

\[
\begin{aligned}
Q_{12}={}&6c^6+6c^5s+240c^5-456c^4s-8858c^4\\
&+2466c^3s-33138c^3+618c^2s+1612501c^2\\
&+571254cs-18512844c-3259668s+13167067.
\end{aligned}
\]

Thus the closed formula implied by Stage 6 is

\[
\boxed{D_m^{(12)}(\theta)=32s^2\left(3^{m-3}(Q_3-Q_{12})+Q_{12}\right),\quad m\ge3.}
\]

For a convenient expanded coefficient, let

\[
\begin{aligned}
A:=Q_3-Q_{12}={}&-18c^6+18c^5s+792c^5-1584c^4s-71262c^4\\
&+40428c^3s+2433420c^3-68112c^2s-31973520c^2\\
&-3050847cs+294103458c+6741108s-579983064.
\end{aligned}
\]

Then `D_m = 32*s^2*(3^(m-3)*A + Q12)`.

## Exact cross-checks performed

All computations below used integer/Gaussian-integer sparse polynomial arithmetic; no floating-point values were used.

1. Recomputed the full level-3 and level-4 trace defects using the repository's original `higher_moment_p12_symbolic.py` orientation:
   - `D_3` has 41 raw monomials before circle reduction.
   - `D_4` has 41 raw monomials before circle reduction.
   - Both reduce exactly modulo `c^2+s^2=1` to the polynomials above.
2. Formed the exact circle-normal form of `D_4 - 3*D_3`. It is exactly the fixed 17-term `EXPECTED_C12_CIRCLE_NORMAL_FORM` in `higher_moment_p12_level5_constant.py`, and exactly equals `-64*s^2*Q12` modulo `c^2+s^2=1`.
3. Confirmed at `theta=pi` (`c=0,s=1`):
   - `D_3(pi) = -18,026,705,824`.
   - `C_12(pi) = -634,073,536`.
   - `D_4(pi) = -54,714,191,008`.
   - The recurrence gives `D_m(pi) = -18,343,742,592 * 3^(m-3) + 317,036,768` for `m >= 3`, agreeing with the repository's exact finite-level values at levels 3–6.
4. The two H12 Python regression files are part of the workflow's fast test step. Both Python-version fast-test steps completed successfully, and the final workflow status confirms that the slow-test stage also completed successfully on Python 3.11 and 3.12.

## Important orientation audit correction

Do **not** reverse a stored face rotation merely because the coordinate-oriented `fluxEdge` endpoints occur in the opposite order in `vertexOrder`.

In `pHeO`, `U` is obtained from the coordinate-oriented `fluxEdge`; the choice between `-U` and `-U^H` is then made independently by `o p q`. For `oNum`, the matrix entry from the lower `vIdx` to the higher `vIdx` is `-U`, even on a flux edge whose coordinate orientation runs from the larger vertex index to the smaller one. Therefore the original Python generator's convention—put `-U` in the lower-index-to-higher-index block and `-U^H` in the reverse block—matches Lean. A separate diagnostic that reversed those four level-3 edges was based on a misreading and its alternative polynomials must not be used.

## Remaining formalization work

The Stage 6 recurrence is already Lean-proved. The remaining target is to formalize these two exact polynomial identities in Lean:

1. `defectO12 3 ... (oNum 3) = Complex.ofReal (32 * s^2 * Q3)`.
2. `defectO12_num_residual_constant theta = Complex.ofReal (-64 * s^2 * Q12)`.

Then combine them with `defectO12_num_affine_closed_form_from_level3_unconditional` to state the explicit all-level polynomial formula for every `m >= 3`.

Do not alter the Stage 6 recurrence or claim this final polynomial step is Lean-verified until those declarations compile and the full `lake build EvgenyTheorem` succeeds.
