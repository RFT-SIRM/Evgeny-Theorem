<div align="center">

# Evgeny's Theorem

### A Gauge-Invariant Spectral Invariant of a Noncommutative SU(2) Bundle on the Sierpinski Gasket

[![Tests](https://img.shields.io/github/actions/workflow/status/RFT-SIRM/Evgeny-Theorem/tests.yml?branch=main&style=for-the-badge&label=Tests&color=3ee290)](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/workflows/tests.yml)
[![License](https://img.shields.io/badge/License-Apache_2.0-yellow?style=for-the-badge)](LICENSE)
[![H4 Closed Form](https://img.shields.io/badge/H4-Exact%20Closed%20Form-5aa9ff?style=for-the-badge)](THEOREM.md)
[![Lean 4](https://img.shields.io/badge/Lean%204-Closed%20Form%20Machine--Checked-3ee290?style=for-the-badge)](formalization/README.md)
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

$$
\Delta_m(H^4, \theta) = \mathrm{Tr}(H_C^4) - \mathrm{Tr}(H_{C'}^4)
$$

satisfies the **exact closed form**

$$
\Delta_m(H^4, \theta) = -16 \left(3^{m-1} + 1\right) \sin^2\!\left(\frac{\theta}{2}\right)
$$

for every $m \ge 1$ and every $\theta$, verified numerically to better than
$10^{-9}$ at every tested parameter pair, and to $10^{-13}$ at $m = 7$
(matrix dimension 6564). The identity is also proved, for every $m \ge 1$ and every $\theta$, in Lean 4 (see [Lean 4 formalization](#lean-4-formalization)).

Normalizing by $\dim(H) = 3^{m+1} + 3$ gives the intensive invariant

$$
I_m(\theta) = \frac{\Delta_m(H^4, \theta)}{3^{m+1} + 3} \longrightarrow -\frac{8}{9}
$$

at $\theta = \pi/2$, with geometric convergence confirmed through $m = 7$.

---

## What is established

| Result | Status |
|---|---|
| **H4 exact closed form** | Exact -- analytic formula verified to 1e-13 |
| **Intensive limit** I_inf(pi/2) = -8/9 | Exact |
| **Gauge invariance** | Spectral deviation < 8e-15 under random SU(2) gauge |
| **Vanishes at p = 1, 2, 3** | Exact -- first nonzero at p = 4 |
| **H6 all-angle recurrence** ($m \ge 3$) | Lean-proved: $D_{m+1}=3D_m+C_6(\theta)$ with an exact finite level-three constant |
| **H6 affine growth law** ($m \ge 3$) | Lean-proved: $D_m=3^{m-3}A_6(\theta)+B_6(\theta)$ |
| **H6 coefficient simplification** | An elementary trigonometric expression for $C_6(\theta)$ remains open; exact $\theta=\pi$ certificate gives 5280 for tested transitions from levels 3 through 6 |
| **H6 path-class zero theorem** | Single- and two-triangle classes contribute zero |
| **H6/H8/H10 reference values** | Numerical regression, locked by tests |
| **Elementary coefficient formula for H6; all-angle H8/H10 recurrence** | Open; H6's affine growth law is proved for $m ge 3$, but $C_6(\theta)$ is not simplified and the $m=2$ base transition is not proved for all angles |
| **Lean 4: graph infrastructure** ($SG(m)$, `Vertex`, `Adj`, `degree`) | Computable, decidable, machine-checked (`lake build`) |
| **Lean 4: operator-level closed form** (`traceDefect_closed`) | Machine-checked for every `m >= 1` and every `theta`, for the concrete operators; no `sorry`, standard axioms only (see below) |

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

### Lean 4 formalization

The closed form is machine-checked in Lean 4 against Mathlib, for the concrete operators, for every
refinement level `m >= 1` and every angle `theta`
([`formalization/EvgenyTheorem/TildeEntries.lean`](formalization/EvgenyTheorem/TildeEntries.lean)):

```lean
theorem traceDefect_closed (θ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    traceDefect m θ =
      -16 * ((3 : ℂ) ^ (m - 1) + 1) * ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2
```

Here `traceDefect m θ` is the difference of the fourth traces of `HC` and `HCprime` (`Operator.lean`): the
connection operators on the Sierpinski-gasket graph `SG(m)` with SU(2) edge unitaries, the axis on the flux
edge of each triangle cycling through x, y, z (`faceAxis`) versus fixed to z. In
[`EvgenyTheorem.lean`](formalization/EvgenyTheorem.lean), `traceDefect_eq_delta` restates it as
`traceDefect m θ = (delta m θ : ℂ)` with `delta` the real closed form, and `traceDefect_re_eq_delta` /
`traceDefect_im_eq_zero` give the real and imaginary parts.

The proof follows a different route from the hand proof in `docs/PROOF.md`: the level-`m+1` operator is glued from three copies of the level-`m` operator, and a coupled recursion over two orientations closes the induction:

1. **Base cases.** `traceDefect_one` (`m = 1`, explicit 12x12 matrices) and `tilde_base` (the same computation with
   the corner flux edge reversed; the defect is `0`).
2. **Gluing.** `H_{m+1} = E K E^T` for the block-diagonal `K` of three copies; an abstract trace identity
   (`GlueAlg.lean`, `GlueBridge.lean`) leaves only corner data, proved in `sgK_corner_data`
   (the `Glue*.lean` files).
3. **Coupled recursion.** `D_{m+1} = 2 D_m + D~_m` and `D~_{m+1} = D_m + 2 D~_m`
   (`defect_succ_num`, `defect_succ_til`), then induction (`FinalArith.lean`, `FinalTheorem.lean`).

Check it yourself: `lake build`. The final theorems contain no `sorry` and depend only on
the standard axioms `propext`, `Classical.choice`, `Quot.sound` (verify with `#print axioms EvgenyTheorem.traceDefect_closed`). Details and a file map: [`formalization/README.md`](formalization/README.md).

What this does *not* cover: the theorem above is the fourth-moment formula only (`m >= 1`, not `m = 0`). The H6 branch now has a separate Lean-proved all-angle affine growth law for `m >= 3`, but its coefficient is still expressed through exact level-three data rather than a simplified trigonometric formula. The $m=2$ to $m=3$ base transition is not formally established for all angles, and the general H8/H10 recurrences remain open. The edge orientation in the Lean operator is the vertex-index order of `sg_graph.py` (see [`docs/ORIENTATION_NOTE.md`](docs/ORIENTATION_NOTE.md)).

---

## Higher moments: H6 growth law and open H8/H10 program

### H6: formally proved affine growth for m ≥ 3

For the sixth-moment numbering defect
`D_m(θ) = defectO6 m θ faceAxis (fun _ => 2) (oNum m)`, the current Lean proof establishes, for every real angle and every `m ≥ 3`,

$$
D_{m+1}(\theta)=3D_m(\theta)+C_6(\theta),
\qquad
D_m(\theta)=3^{m-3}A_6(\theta)+B_6(\theta).
$$

The coefficient and offset are exact, m-independent finite level-three
expressions assembled from the stabilized high-power boundary residual and
the level-three orientation gap. Neither contribution is assumed to vanish.
Both complete Lean formalization workflows passed on the source proving this
result.

This does not yet give an elementary trigonometric simplification for
`C₆(θ)`, nor a Lean proof of the separate level-2-to-3 base transition for
all angles. At `θ = π`, the exact sparse Gaussian-integer certificate gives
residual 5280 for tested transitions from levels 3 through 6; the Lean
coefficient has not yet been normalized to that integer by a separate theorem.

### H8 and H10: still an open all-angle program

The existing numerical data support affine growth for H8 and H10, but no
general all-angle Lean recurrence or closed form is claimed for those moments.


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

```text
Evgeny-Theorem/
├── THEOREM.md
├── VERIFICATION.md
├── docs/
│   ├── HIGHER_MOMENTS.md
│   ├── EXACT_VERIFICATION.md   exact (symbolic) verification for m=1..7; locality mechanism
│   ├── SPLIT_AUTOMATON.md      the sibling-vertex split: rule, mechanism, recursion
│   └── PROOF.md                hand proof of the identity for all m (not Lean-checked; the Lean proof takes a different route)
├── formalization/              Lean 4 formalization (closed form proved for all m >= 1)
│   ├── EvgenyTheorem.lean      delta, I, traceDefect_eq_delta, delta_one_pi_div_two
│   ├── README.md               proof structure, file map, how to check
│   └── EvgenyTheorem/
│       ├── Graph/              SG(m) graph (computable Vertex/Adj), triangular faces, flux edges
│       ├── SU2.lean, Operator.lean   Pauli matrices, SU(2) rotations, HC, HC', traceDefect
│       ├── Glue*.lean          gluing of three copies, corner data (hcorner)
│       ├── Final*.lean, Tilde*.lean, AlgebraTilde.lean   recursions, base cases, closed form
│       ├── SanityChecks.lean   decidable graph-level checks (degrees, vertex counts; levels 1-3)
│       └── SanityChecksLevel4.lean  same checks at level 4 (slow, not in the default build)
├── src/
│   ├── graph/
│   ├── su2/
│   ├── operators/
│   └── moments/
├── tests/
│   ├── test_levels.py
│   ├── test_theta.py
│   ├── test_heldout.py
│   ├── test_gauge_invariance.py
│   ├── test_higher_moments.py
│   ├── test_path_class_h6.py
│   ├── test_exact_symbolic.py       exact symbolic check of the closed form, m=1..7
│   ├── test_split_automaton.py      the sibling-vertex split rule
│   ├── test_bounded_formula.py      bounded 6-vertex local formula
│   ├── test_history_automaton.py    split rule from the vertex construction history
│   └── test_recursion_mechanism.py  why the recursion's additive constant is fixed
├── data/
├── figures/
└── reproducibility/
```

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
