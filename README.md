<div align="center">

# Evgeny's Theorem

### A Gauge-Invariant Spectral Invariant of a Noncommutative SU(2) Bundle on the Sierpinski Gasket

[![Tests](https://img.shields.io/github/actions/workflow/status/RFT-SIRM/Evgeny-Theorem/tests.yml?branch=main&style=for-the-badge&label=Tests&color=3ee290)](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/workflows/tests.yml)
[![License](https://img.shields.io/badge/License-Apache_2.0-yellow?style=for-the-badge)](LICENSE)
[![H4 Closed Form](https://img.shields.io/badge/H4-Exact%20Closed%20Form-5aa9ff?style=for-the-badge)](THEOREM.md)
[![H6 Research](https://img.shields.io/badge/H6-Open%20Research%20Program-orange?style=for-the-badge)](docs/HIGHER_MOMENTS.md)
[![Python](https://img.shields.io/badge/Python-3.11%2B-lightgrey?style=for-the-badge)](reproducibility/requirements.txt)
[![Visualization](https://img.shields.io/badge/Live%20Demo-GitHub%20Pages-c6ff5c?style=for-the-badge)](https://rft-sirm.github.io/Evgeny-Theorem/)

</div>

---

## The result

Let `SG(m)` be the standard Sierpinski gasket graph at refinement level `m`.
Equip it with the Hilbert space `C^n x C^2` and an SU(2)-valued connection
with non-commuting holonomy: the rotation axis on the flux edge of each
elementary triangle cycles through x, y, z by triangle index.
Compare against the commuting control `C'`, where the axis is fixed to z
for every triangle -- exactly two decoupled U(1) magnetic Laplacians.

The fourth spectral-moment defect

    Delta_m(H^4, theta) = Tr(H_C^4) - Tr(H_C'^4)

satisfies the **exact closed form**

    Delta_m(H^4, theta) = -16 * (3^(m-1) + 1) * sin^2(theta/2)

for every `m >= 1` and every `theta`, verified numerically to better than
`1e-9` at every tested parameter pair, and to `1e-13` at `m = 7`
(matrix dimension 6564).

Normalizing by `dim(H) = 3^(m+1) + 3` gives the intensive invariant

    I_m(theta) = Delta_m(H^4, theta) / (3^(m+1) + 3)  -->  -8/9

at `theta = pi/2`, with geometric convergence confirmed through `m = 7`.

---

## What is established

| Result | Status |
|---|---|
| **H4 exact closed form** | Exact -- analytic formula verified to 1e-13 |
| **Intensive limit** I_inf(pi/2) = -8/9 | Exact |
| **Gauge invariance** | Spectral deviation < 8e-15 under random SU(2) gauge |
| **Vanishes at p = 1, 2, 3** | Exact -- first nonzero at p = 4 |
| **H6 growth law** alpha(theta)*3^m + beta(theta) | Established numerically to machine precision |
| **H6 recurrence** Delta_m = 3*Delta_{m-1} + C(theta) | Established, C(pi) = 5280 exactly |
| **H6 path-class zero theorem** | Single- and two-triangle classes contribute zero |
| **H6/H8/H10 reference values** | Numerical regression, locked by tests |
| **Closed form for H6, H8, H10** | Open -- no claim made |

---

## Verification at a glance

### Refinement sequence, theta = pi/2

| m | dim(H) | I_m(pi/2) | ratio |
|:-:|---:|---:|---:|
| 1 | 12 | -1.333333 | -- |
| 2 | 30 | -1.066667 | 0.8000 |
| 3 | 84 | -0.952381 | 0.8929 |
| 4 | 246 | -0.910569 | 0.9561 |
| 5 | 732 | -0.896175 | 0.9842 |
| 6 | 2190 | -0.891324 | 0.9946 |
| **7** | **6564** | **-0.889701** | **0.9982** |

Aitken extrapolation of m = 5, 6, 7: **-0.8888855**,
versus exact **-8/9 = -0.8888889** (difference 3.3e-6).

### Held-out cross-check

| m | theta | Computed | Closed form | error |
|:-:|---:|---:|---:|---:|
| 2 | 0.7 | -7.5250500069 | -7.5250500069 | 2.2e-12 |
| 3 | 1.9 | -105.8631653491 | -105.8631653491 | 8.2e-13 |
| 5 | 2.5 | -1181.5502117988 | -1181.5502117988 | 1.9e-11 |
| 1 | 3.0 | -31.8398799456 | -31.8398799456 | 8.2e-14 |
| 4 | 0.3 | -10.0046264358 | -10.0046264359 | 2.5e-11 |

### Six-criterion acceptance protocol

| # | Criterion | Status |
|:-:|---|:---:|
| i | Stable limit as m -> inf | OK |
| ii | Differs from plain SG and U(1)-magnetic SG | OK |
| iii | Survives normalization | OK |
| iv | Gauge-invariant | OK |
| v | Not reducible to dim / edges / faces / flux density | OK |
| vi | Vanishes in the commuting limit | OK |

Full statement: [THEOREM.md](THEOREM.md) -- Full tables: [VERIFICATION.md](VERIFICATION.md)

---

## Higher moments: an open research program

### H6 structural results

**Growth law** (machine-precision verification):

    Delta_m(H^6, theta) = alpha(theta)*3^m + beta(theta)

Fit from m = 4, 5 predicts m = 3 with error below 1e-8.
No quadratic 3^(2m) term (coefficient ratio < 1e-15).

**Exact recurrence** (for m >= 2):

    Delta_m(H^6, theta) = 3 * Delta_{m-1}(H^6, theta) + C(theta)

At theta = pi:

    C(pi) = 5280  =  2^5 * 3 * 5 * 11   (exact integer)

At theta = pi, the growth law yields exact fractions:
alpha(pi) = -4112/3, beta(pi) = -2640.

**Path-class zero theorem**: on SG(1), only closed walks visiting
all three triangles contribute to Delta(H^6). Single-triangle and
two-triangle walk classes contribute exactly zero.

**Why H6 has no H4-type closed form**: every H4 contributing walk
performs one triangular traversal, giving the same -4*sin^2(theta/2).
The H6 class {0,1,2} contains 486 walks with different axis sequences
whose SU(2) holonomies do not collapse to a finite trig polynomial.

### Numerical reference values at theta = pi/2

| m | Delta(H6) | Delta(H8) | Delta(H10) |
|---:|---:|---:|---:|
| 1 | -3180.000000 | -246909.026268 | -14013358.982483 |
| 2 | -6956.588745 | -595053.284942 | -37686518.369790 |
| 3 | -18274.354980 | -1632052.331669 | -107772338.487566 |
| 4 | -52227.653685 | -4743049.471847 | -318029798.840894 |

Regression references only. See [docs/HIGHER_MOMENTS.md](docs/HIGHER_MOMENTS.md)

---

## Repository map
Evgeny-Theorem/
├── THEOREM.md
├── VERIFICATION.md
├── docs/
│ └── HIGHER_MOMENTS.md
├── src/
│ ├── graph/
│ ├── su2/
│ ├── operators/
│ └── moments/
├── tests/
│ ├── test_levels.py
│ ├── test_theta.py
│ ├── test_heldout.py
│ ├── test_gauge_invariance.py
│ ├── test_higher_moments.py
│ └── test_path_class_h6.py
├── data/
├── figures/
└── reproducibility/

---

## Reproduce it yourself

    git clone https://github.com/RFT-SIRM/Evgeny-Theorem.git
    cd Evgeny-Theorem
    python3 -m venv .venv && source .venv/bin/activate
    pip install -r reproducibility/requirements.txt
    pytest tests/ -m "not slow" -v
    pytest tests/ -m slow -v

---

## License

Apache License 2.0 -- see [LICENSE](LICENSE) and [NOTICE](NOTICE).
