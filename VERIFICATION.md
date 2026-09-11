# Verification record

All numbers below are reproduced by `tests/test_heldout.py`, `tests/test_theta.py`, and `tests/test_gauge_invariance.py`. Commands to reproduce are given in each section.

## 1. Refinement sequence, θ = π/2, m = 1…7

| m | n (SG vertices) | dim(H) = 2n | I_m(π/2) | I_m / I_(m−1) |
|---|---|---|---|---|
| 1 | 6 | 12 | −1.333333 | — |
| 2 | 15 | 30 | −1.066667 | 0.8000 |
| 3 | 42 | 84 | −0.952381 | 0.8929 |
| 4 | 123 | 246 | −0.910569 | 0.9561 |
| 5 | 366 | 732 | −0.896175 | 0.9842 |
| 6 | 1095 | 2190 | −0.891324 | 0.9946 |
| 7 | 3282 | 6564 | −0.889701 | 0.9982 |

Level 7 is computed by repeated matrix multiplication (`moments.raw_trace`), not eigendecomposition — this is what keeps it tractable (~250s wall-clock in this environment).

Reproduce: `pytest tests/test_heldout.py::test_Im_sequence_theta_pi_over_2 tests/test_heldout.py::test_Im_converges_towards_minus_8_over_9 -v` (fast part, m≤6) and `pytest tests/test_heldout.py::test_level7_matches_formula -v -m slow` (level 7, slow).

## 2. Held-out cross-check against the closed form

Parameter pairs chosen *after* the closed form in `THEOREM.md` was fixed, specifically to rule out curve-fitting.

| m | θ | Direct computation | Formula | \|Δ\| |
|---|---|---|---|---|
| 2 | 0.7 | −7.5250500069 | −7.5250500069 | 2.21×10⁻¹² |
| 3 | 1.9 | −105.8631653491 | −105.8631653491 | 8.24×10⁻¹³ |
| 5 | 2.5 | −1181.5502117988 | −1181.5502117988 | 1.86×10⁻¹¹ |
| 1 | 3.0 | −31.8398799456 | −31.8398799456 | 8.17×10⁻¹⁴ |
| 4 | 0.3 | −10.0046264358 | −10.0046264359 | 2.54×10⁻¹¹ |

Reproduce: `pytest tests/test_heldout.py::test_heldout_pairs_match_formula tests/test_heldout.py::test_heldout_pairs_match_direct_computation -v`

## 3. Gauge invariance

A Haar-random SU(2) gauge transformation `g: V → SU(2)` applied vertex-wise: `U'(a,b) = g(a)·U(a,b)·g(b)†`.

| Quantity | Value |
|---|---|
| max \|spec(H) − spec(H_gauge)\| (level 3, seed 42) | 7.99×10⁻¹⁵ |
| M₄(original gauge) | 570.194764040863 |
| M₄(random gauge) | 570.194764040863 |
| Difference | exactly 0 |

Reproduce: `pytest tests/test_gauge_invariance.py -v`

## 4. θ-grid check at fixed level (independent of the held-out set)

`tests/test_theta.py` checks the closed form against direct computation across a 10-point θ grid (`0.05` to `3.13`) at levels 2 and 3 — 20 additional independent checks, all passing to `<1e-9`.

## 5. Limit value

Analytic limit of the closed form as `m → ∞` at `θ = π/2`:

```
I_∞(π/2) = −8/9 = −0.888888...
```

Aitken Δ²-extrapolation of the raw numerical sequence at m=5,6,7 gives `−0.8888855`, a difference of `3.3×10⁻⁶` from the exact value — consistent with finite-level truncation.

## Full test run

```bash
pytest tests/ -m "not slow" -v     # 60+ checks, seconds
pytest tests/ -m slow -v           # level-7 check, ~2-4 minutes
```
