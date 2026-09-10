# Derivation notes

## Why a closed form exists at fourth order

`Tr(H^p)` is a sum over closed walks of length `p` on the graph, each walk contributing the trace of the ordered product of its edge matrices (including the diagonal degree term). Because `C` and `C′` share an identical graph, edge set, and local rotation angle, and differ *only* in the axis choice on flux edges, the difference `Δ_m(H^p)` receives contributions exclusively from closed walks that traverse at least one flux edge — every other walk cancels identically between the two configurations.

At `p = 4`, closed walks touching flux edges fall into three classes:

- **Class "0" (neutral):** walks that cannot distinguish axis choice at this order; cancel exactly between C and C′.
- **Class "+" (co-directed):** walks traversing a single flux edge twice in reinforcing directions within the 4-step loop; contribute a fixed positive trigonometric amplitude.
- **Class "−" (counter-directed):** the mirror-reversed walks of class "+"; contribute the negative amplitude. The antisymmetric combination of "+" and "−" is what survives as the net defect.

The count of length-4 closed walks capable of reaching a flux edge and returning scales linearly with the number of elementary triangles (`3^m`), which combined with the fixed per-walk amplitude `sin²(θ/2)` and normalization by the dimension (`~3^m`) produces the clean geometric convergence recorded in `VERIFICATION.md`.

**Status of this argument:** it explains *why* a closed form is plausible at `p=4` and is consistent with the formula. It is not a formally certified, exhaustively-enumerated combinatorial proof in this repository. The formula itself does not depend on the completeness of this qualitative argument — it is independently verified by direct computation (`tests/test_theta.py`, `tests/test_heldout.py`) to near machine precision at every tested parameter.

## The sixth-order moment: a rejected conjecture

An initial guess, obtained by analogy with the `p=4` result, proposed:

```
Δ_m(H⁶, θ) = −4 · W_m · sin²(θ/2) · (2cos θ + 1)²
```

for some level-dependent combinatorial weight `W_m`. This was tested directly: if correct, the ratio

```
Δ_m(H⁶, θ) / [sin²(θ/2) · (2cos θ + 1)²]
```

must be constant in `θ` at fixed `m` (equal to `−4·W_m`). It is not. At `m=2`, across six values of `θ`, the ratio varies from roughly `−1.6×10³` to `−1.1×10⁵` — a two-order-of-magnitude spread, including a spurious divergence near `θ ≈ 2π/3` where the proposed denominator has a near-zero that the true trace defect does not share.

Direct harmonic reconstruction (least-squares fit of `Δ_m(H⁶,θ)` against a trigonometric-polynomial basis `{1, cos(kθ), sin(kθ)}`) shows the residual against direct computation does not reach numerical noise until harmonics up to **order 10** (21 coefficients) are included. The conjectured form above has effective harmonic content of order ≤ 3. The two are structurally incompatible; this is not a coefficient error, it is the wrong class of function.

**Interpretation:** length-6 closed walks can couple up to three distinct flux-bearing triangles (rather than the two that suffice at length 4), which plausibly accounts for the higher harmonic content. No closed form for the sixth moment is available in this repository. It is left as an open, separate problem — see the "Out of scope" section of `THEOREM.md`.
