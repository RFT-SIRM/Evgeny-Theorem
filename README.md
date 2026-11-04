<div align="center">

# Evgeny's Theorem

### Exact spectral moments of a noncommutative SU(2) connection on the Sierpiński gasket

[![Tests](https://img.shields.io/github/actions/workflow/status/RFT-SIRM/Evgeny-Theorem/tests.yml?branch=main&style=for-the-badge&label=Tests)](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/workflows/tests.yml)
[![License](https://img.shields.io/badge/License-Apache_2.0-yellow?style=for-the-badge)](LICENSE)
[![H⁴ theorem](https://img.shields.io/badge/H⁴-Exact%20closed%20form-5aa9ff?style=for-the-badge)](THEOREM.md)
[![Lean 4](https://img.shields.io/badge/Lean%204-Machine--checked-3ee290?style=for-the-badge)](formalization/README.md)
[![Higher moments](https://img.shields.io/badge/Higher%20moments-Research%20results-orange?style=for-the-badge)](docs/HIGHER_MOMENTS.md)
[![Python](https://img.shields.io/badge/Python-3.11%20%7C%203.12-lightgrey?style=for-the-badge)](reproducibility/requirements.txt)
[![Research site](https://img.shields.io/badge/Research%20site-GitHub%20Pages-c6ff5c?style=for-the-badge)](https://rft-sirm.github.io/Evgeny-Theorem/)

</div>

---

## The mathematical object

At refinement level $m$, let $SG(m)$ be the finite Sierpiński-gasket graph. Its numbers of vertices, edges, and elementary triangular faces are

$$
|V_m|=\frac{3^{m+1}+3}{2},\qquad
|E_m|=3^{m+1},\qquad
|F_m|=3^m.
$$

The operator acts on $\mathbb{C}^{|V_m|}\otimes\mathbb{C}^{2}$, and therefore has dimension

$$
\dim H_m=3^{m+1}+3.
$$

Every oriented edge carries an $SU(2)$ unitary. In configuration $C$, the rotation axis on the flux edge of each elementary triangle cycles through $x,y,z$. The comparison configuration $C'$ keeps the same graph and flux placement but fixes the axis to $z$, so its edge matrices commute.

The comparison is controlled: the graph, dimension, and flux placement are held fixed; the changed ingredient is the non-commuting axis pattern. At level $m=7$, the graph has 3,282 vertices and the operator dimension is 6,564.

This repository records the mathematical construction, its exact identities, the formal proof architecture, the higher-moment programme, and the computational evidence needed to audit each claim.

## The central theorem — the fourth spectral moment

Define the fourth-moment trace defect

$$
\Delta_m(H^4,\theta)
=
\mathrm{Tr}(H_C^4)-\mathrm{Tr}(H_{C'}^4).
$$

For every refinement level $m\ge1$ and every real angle $\theta$,

$$
\boxed{
\Delta_m(H^4,\theta)
=
-16\left(3^{m-1}+1\right)
\sin^2\left(\frac{\theta}{2}\right)
}
$$

This is the principal unconditional closed-form theorem in the repository. It is proved for the concrete operators in Lean 4 by `traceDefect_closed`, not merely fitted to a finite table.

Normalizing by the matrix dimension gives

$$
I_m(\theta)=\frac{\Delta_m(H^4,\theta)}{3^{m+1}+3}.
$$

Its all-angle limit is

$$
I_\infty(\theta)
=
-\frac{16}{9}\sin^2\left(\frac{\theta}{2}\right),
\qquad
I_\infty\left(\frac{\pi}{2}\right)=-\frac{8}{9}.
$$

The refinement sequence, held-out checks, gauge comparison, and reproduction commands are recorded in [VERIFICATION.md](VERIFICATION.md).

---

## What has been established

A Lean-kernel theorem, an exact finite symbolic certificate, and a numerical regression are different kinds of evidence. This repository labels them separately.

| Result | Current status | Evidence and scope |
|---|---|---|
| **H⁴ — fourth moment** | **Unconditional theorem** | Exact all-level, all-angle identity; machine-checked in Lean 4 for every $m\ge1$. |
| **H⁶ — sixth moment** | **All-angle recurrence and formula, Lean + exact certificate** | Lean recurrence for $m\ge3$, plus an exact symbolic $m=2\to3$ bridge. Combined formula for $m\ge2$; the finite bridge is not yet a Lean-kernel theorem. |
| **H⁸ — eighth moment** | **All-angle recurrence and formula, Lean + exact certificate** | Lean recurrence for $m\ge3$, plus an exact sparse-polynomial $m=2\to3$ bridge. Combined formula for $m\ge2$; the finite bridge is not yet a Lean-kernel theorem. |
| **H¹⁰ — tenth moment** | **Machine-checked conditional affine theorem** | p=10 gluing and orientation recurrences are formalized. The affine formula from level five assumes `H10TransportAll`, which is not yet proved in the current Lean source. |
| **Moments p=1,2,3** | **Exact vanishing** | The defect vanishes; the first nonzero moment in this family is p=4. |
| **H⁶ path classes on SG(1)** | **Exact finite-level result** | Single- and two-triangle classes contribute zero; the all-three-triangle class carries the nonzero contribution. |

The formulas and proof boundaries are collected in [docs/HIGHER_MOMENTS.md](docs/HIGHER_MOMENTS.md). In particular, the H¹⁰ statement is presented with its explicit hypothesis, not as an unconditional closed form.

## H⁶ — sixth moment

Write $D_m^{(6)}(\theta)$ for the Lean quantity `defectO6` evaluated at level $m$ in the numbering orientation, with the face-axis configuration compared against the fixed-$z$ control. Put

$$
c=\cos\left(\frac{\theta}{2}\right),
\qquad
s=\sin\left(\frac{\theta}{2}\right).
$$

Lean proves the recurrence for $m\ge3$:

$$
D_{m+1}^{(6)}(\theta)
=
3D_m^{(6)}(\theta)+C_6(\theta).
$$

The exact finite certificate supplies

$$
D_2^{(6)}(\theta)
=
-14592s^2+1344cs^2-384s^3,
$$

$$
C_6(\theta)
=
4512s^2+192cs^2+768s^3.
$$

Together they give, for every $m\ge2$,

$$
D_m^{(6)}(\theta)
=
3^{m-2}D_2^{(6)}(\theta)
+
\frac{3^{m-2}-1}{2}C_6(\theta).
$$

Equivalently,

$$
D_m^{(6)}(\theta)
=
-\left(12336\cdot3^{m-2}+2256\right)s^2
+\left(1440\cdot3^{m-2}-96\right)cs^2
-384s^3.
$$

At $\theta=\pi$, the exact coefficient is $C_6(\pi)=5280$.

**Proof boundary.** The recurrence for $m\ge3$ is Lean-proved. The exceptional finite transition is established by exact Gaussian-integer polynomial arithmetic in `computational/p6_level3_orientation_certificate.py` and checked in the regression suite; it is not yet part of the Lean-kernel proof.

## H⁸ — eighth moment

Write $D_m^{(8)}(\theta)$ for the Lean quantity `defectO8` with the same numbering and comparison conventions. Lean proves, for $m\ge3$,

$$
D_{m+1}^{(8)}(\theta)
=
3D_m^{(8)}(\theta)+C_8(\theta).
$$

The exact sparse-polynomial certificate gives the level-two value

$$
D_2^{(8)}(\theta)
=
-1335552s^2
+244352cs^2
-40064s^3
+64cs^3
+1920s^4,
$$

and the recurrence coefficient

$$
C_8(\theta)
=
193600s^2
+75776cs^2
+83712s^3
-512cs^3
+192s^4.
$$

It verifies the finite transition

$$
D_3^{(8)}-3D_2^{(8)}
=
D_4^{(8)}-3D_3^{(8)}
=
C_8(\theta).
$$

Therefore, for every $m\ge2$,

$$
D_m^{(8)}(\theta)
=
3^{m-2}D_2^{(8)}(\theta)
+
\frac{3^{m-2}-1}{2}C_8(\theta).
$$

At $\theta=\pi$, $C_8(\pi)=277504$.

**Proof boundary.** The structural recurrence is Lean-formalized for $m\ge3$. The exceptional $m=2\to3$ transition is an exact Gaussian-integer polynomial certificate in [computational/p8_base_certificate.py](computational/p8_base_certificate.py), not yet a Lean-kernel theorem. No sampled-angle fit is used.

## H¹⁰ — tenth moment: conditional affine theorem

The H¹⁰ formalization includes the ordered tenth-power expansion, exact word-stratum reductions, the p=10 gluing assembly, recurrences for the numbering and flipped-corner orientations, and corner-flip row transport through degree nine.

Write $D_m^{(10)}(\theta)$ for the Lean quantity `defectO10` in the numbering orientation. Let $C_{10}^{(5)}(\theta)$ be the exact level-five residual defined by `defectO10_num_residual_constant`.

Under the explicit hypothesis `H10TransportAll` — glued-state diagonal transport through degree nine, corresponding to radius-four corner locality — Lean proves, for every $m\ge4$,

$$
D_{m+1}^{(10)}(\theta)
=
3D_m^{(10)}(\theta)+C_{10}^{(5)}(\theta).
$$

Consequently, for every $m\ge5$,

$$
D_m^{(10)}(\theta)
=
3^{m-5}
\left(
D_5^{(10)}(\theta)
+\frac{C_{10}^{(5)}(\theta)}{2}
\right)
-\frac{C_{10}^{(5)}(\theta)}{2}.
$$

This is a machine-checked **conditional** affine closed form. The hypothesis `H10TransportAll` is explicit in the theorem and is not proved in the current Lean development. The level-five residual remains an exact trace expression; it has not yet been reduced to an explicit trigonometric polynomial. The unconditional all-angle H¹⁰ closed form is therefore not claimed by the current source.

The H¹⁰ source modules are:

- `GlueTrace10.lean` — tenth-power gluing assembly;
- `GlueRows10.lean` — glued-row and boundary transport;
- `FinalOrient10.lean` — orientation recurrences and comparison;
- `FinalClosed10.lean` — explicit transport hypothesis and conditional affine theorem.

Direct numerical values at $\theta=\pi/2$ remain regression references in `tests/test_higher_moments.py`. They do not replace the missing transport proof.

---

## The scale and the research programme

The mathematical object is a recursively defined family of non-commutative operators on a self-similar graph, not a single fitted curve or an isolated finite matrix. The graph grows exponentially with refinement; the theorem and recurrence statements describe how spectral traces change across that hierarchy.

The research record keeps six layers visible:

1. **The object:** the graph, edge connection, two SU(2) configurations, and trace defect.
2. **The exact identity:** the fourth-moment formula and normalized limit.
3. **The higher-moment structure:** recurrence laws, finite symbolic corrections, and the tenth-order gluing reduction.
4. **The formal proof:** concrete Lean declarations and their assumptions.
5. **The computational evidence:** source code, exact certificates, numerical reference tables, and tests.
6. **The research history:** chronological journals recording what was attempted, proved, repaired, and left open.

The objective is auditability: a reader can move from the statement to the construction, from the construction to the proof, and from the proof to the reproducible record.

## Verification and formalization

### Lean 4

The principal theorem is

```lean
theorem traceDefect_closed (θ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    traceDefect m θ =
      -16 * ((3 : ℂ) ^ (m - 1) + 1) * ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2
```

The final theorem contains no `sorry` and depends on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The proof architecture and module map are in [formalization/README.md](formalization/README.md).

Build from the repository root:

```bash
lake build
```

To inspect the theorem's axioms:

```bash
printf 'import EvgenyTheorem\n#print axioms EvgenyTheorem.traceDefect_closed\n' > /tmp/ax.lean
lake env lean /tmp/ax.lean
```

### Python and exact certificates

The computational layer provides direct operator calculations, exact polynomial certificates, trace-word inventories, and regression tests.

```bash
python -m pip install -r reproducibility/requirements.txt
pytest tests/ -m "not slow" -v
```

The slower refinement checks are run separately:

```bash
pytest tests/ -m slow -v
```

The test workflow uses Python 3.11 and 3.12. The Lean workflow builds the formalization when Lean sources or the toolchain configuration change. A passing workflow certifies only the checks it actually runs.

---

## Repository map

This map follows the files present in the current repository. The two research logs are primary chronological records; this README is an overview, not a replacement for them.

```text
Evgeny-Theorem/
├── README.md
├── THEOREM.md
├── VERIFICATION.md
├── CITATION.cff
├── LICENSE
├── NOTICE
├── .nojekyll
├── .github/workflows/
│   ├── lean-formalization.yml
│   └── tests.yml
├── computational/
│   ├── corner_power_report.py
│   ├── higher_moment_pi_certificate.py
│   ├── p6_level3_orientation_certificate.py
│   ├── p8_base_certificate.py
│   ├── trace_word_counts.py
│   ├── trace_word_inventory_p6_p8_p10.json
│   └── trace_word_reduction_ledger_p6_p8_p10.json
├── data/
│   ├── raw/
│   │   ├── README.md
│   │   └── SG_spectra_levels4-6.csv
│   └── spectra/
│       └── plain_sg_spectra_levels1-6.csv
├── docs/
│   ├── EXACT_VERIFICATION.md
│   ├── HIGHER_MOMENTS.md
│   ├── LEAN_PLAN_GENERAL_M.md
│   ├── LEAN_ROADMAP.md
│   ├── ORIENTATION_NOTE.md
│   ├── PROOF.md
│   ├── SPLIT_AUTOMATON.md
│   └── index.html
├── figures/
│   └── convergence_I4.png
├── formalization/
│   ├── README.md
│   ├── EvgenyTheorem.lean
│   ├── HIGHER_MOMENT_RESEARCH_LOG.md
│   ├── PROOF_WORK_LOG.md
│   ├── .gitignore
│   ├── .gitkeep
│   ├── .github/workflows/
│   │   ├── create-release.yml
│   │   ├── lean_action_ci.yml
│   │   └── update.yml
│   └── EvgenyTheorem/
│       ├── Graph/
│       │   ├── Faces.lean
│       │   └── Sierpinski.lean
│       ├── Algebra.lean
│       ├── AlgebraTilde.lean
│       ├── BaseCase.lean
│       ├── BaseCaseTheorem.lean
│       ├── CornerFaces.lean
│       ├── CornerLocality.lean
│       ├── DegSplit.lean
│       ├── EdgeCopies.lean
│       ├── EdgeSplit.lean
│       ├── EdgeStep.lean
│       ├── FinalArith.lean
│       ├── FinalClosed10.lean
│       ├── FinalOrient.lean
│       ├── FinalOrient10.lean
│       ├── FinalTheorem.lean
│       ├── FinalTilde.lean
│       ├── FlipB.lean
│       ├── FlipC.lean
│       ├── FlipCount.lean
│       ├── FlipFaces.lean
│       ├── FluxSplit.lean
│       ├── GlueAlg.lean
│       ├── GlueBridge.lean
│       ├── GlueCorner.lean
│       ├── GlueCornerCube.lean
│       ├── GlueCornerData.lean
│       ├── GlueCornerGeom.lean
│       ├── GlueCornerSum.lean
│       ├── GlueCornerTri.lean
│       ├── GlueCornerU.lean
│       ├── GlueK.lean
│       ├── GlueRows10.lean
│       ├── GlueSG.lean
│       ├── GlueTrace.lean
│       ├── GlueTrace10.lean
│       ├── ListOrder.lean
│       ├── Locality.lean
│       ├── OpSplit1.lean
│       ├── OpSplit2.lean
│       ├── OpSplit3.lean
│       ├── Operator.lean
│       ├── OrientSq.lean
│       ├── Orientation.lean
│       ├── PairUnit.lean
│       ├── PointModel1.lean
│       ├── PointModel2.lean
│       ├── SGStruct.lean
│       ├── SU2.lean
│       ├── SanityChecks.lean
│       ├── SanityChecksLevel4.lean
│       ├── Setup.lean
│       ├── TildeBase.lean
│       ├── TildeEntries.lean
│       ├── TraceExpand.lean
│       ├── VertexIndex.lean
│       └── VertexOrder.lean
├── reproducibility/
│   ├── environment.md
│   ├── regenerate_figures.py
│   └── requirements.txt
├── src/
│   ├── graph/
│   │   ├── __init__.py
│   │   └── sg_graph.py
│   ├── moments/
│   │   ├── __init__.py
│   │   └── moments.py
│   ├── operators/
│   │   ├── __init__.py
│   │   └── operators.py
│   └── su2/
│       ├── __init__.py
│       └── su2_utils.py
├── tests/
│   ├── general_m_structure_check.py
│   ├── orientation_check.py
│   ├── test_bounded_formula.py
│   ├── test_corner_power_report.py
│   ├── test_exact_symbolic.py
│   ├── test_gauge_invariance.py
│   ├── test_heldout.py
│   ├── test_higher_moment_pi_sparse.py
│   ├── test_higher_moments.py
│   ├── test_history_automaton.py
│   ├── test_lean_python_graph_conventions.py
│   ├── test_levels.py
│   ├── test_path_class_h6.py
│   ├── test_recursion_mechanism.py
│   ├── test_split_automaton.py
│   ├── test_theta.py
│   └── test_trace_word_counts.py
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
├── pyproject.toml
└── .gitignore
```

### Reading guide

| Start here | Purpose |
|---|---|
| [THEOREM.md](THEOREM.md) | Concise statement of the fourth-moment theorem and its mathematical object. |
| [VERIFICATION.md](VERIFICATION.md) | Numerical tables, held-out checks, gauge test, and reproduction commands. |
| [docs/PROOF.md](docs/PROOF.md) | Human-readable mathematical proof of the fourth-moment identity. |
| [docs/EXACT_VERIFICATION.md](docs/EXACT_VERIFICATION.md) | Exact symbolic verification and locality mechanism. |
| [docs/SPLIT_AUTOMATON.md](docs/SPLIT_AUTOMATON.md) | Recursive sibling-vertex split and its mechanism. |
| [docs/HIGHER_MOMENTS.md](docs/HIGHER_MOMENTS.md) | H⁶/H⁸ formulas, H¹⁰ conditional theorem, and exact proof boundaries. |
| [formalization/README.md](formalization/README.md) | Lean theorem, build command, proof architecture, and module map. |
| [formalization/HIGHER_MOMENT_RESEARCH_LOG.md](formalization/HIGHER_MOMENT_RESEARCH_LOG.md) | Chronological higher-moment research journal. |
| [formalization/PROOF_WORK_LOG.md](formalization/PROOF_WORK_LOG.md) | Chronological Lean proof-development journal. |
| [docs/LEAN_ROADMAP.md](docs/LEAN_ROADMAP.md) and [docs/LEAN_PLAN_GENERAL_M.md](docs/LEAN_PLAN_GENERAL_M.md) | Formalization roadmap and general-level proof plan. |
| [docs/ORIENTATION_NOTE.md](docs/ORIENTATION_NOTE.md) | Edge-orientation convention used by the graph and Lean operator. |

## Authorship and research record

This repository records the mathematical construction, theorem statements, formal proof development, exact certificates, computational checks, and the sequence of research decisions that led to them. It is intended to be read as mathematics, checked as formal code, and audited as a reproducible research record.

**Evgeny Zaprudnov**  
*Author of Evgeny's Theorem and originator of the mathematical research programme recorded here.*

Sierpiński Gasket · Non-commutative SU(2) Connection · Spectral Moments · Lean 4

---

## License

Apache License 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
