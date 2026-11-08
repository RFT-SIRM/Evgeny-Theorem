<div align="center">

# Evgeny's Theorem

### Spectral trace identities for non-commutative SU(2) operators on the Sierpiński gasket

[![Tests](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/workflows/tests.yml/badge.svg?branch=main)](https://github.com/RFT-SIRM/Evgeny-Theorem/actions/workflows/tests.yml)
[![License](https://img.shields.io/badge/License-Apache_2.0-yellow?style=for-the-badge)](LICENSE)
[![H4 theorem](https://img.shields.io/badge/H4-Exact%20closed%20form-5aa9ff?style=for-the-badge)](THEOREM.md)
[![Lean 4](https://img.shields.io/badge/Lean%204-Machine--checked-3ee290?style=for-the-badge)](formalization/README.md)
[![Higher moments](https://img.shields.io/badge/Higher%20moments-Research%20programme-orange?style=for-the-badge)](docs/HIGHER_MOMENTS.md)

</div>

## Research dissertation

The complete research dissertation is available here: [**DISSERTATION.md**](DISSERTATION.md).

---

## 1. The mathematical object

Let $SG(m)$ be the Sierpiński-gasket graph at refinement level $m$. Its numbers of vertices, edges, and elementary triangular faces are

$$
|V_m|=(3^{m+1}+3)/2,\quad |E_m|=3^{m+1},\quad |F_m|=3^m.
$$

The operators act on a two-component state at every graph vertex. Their matrix dimension is

$$
N_m=2|V_m|=3^{m+1}+3.
$$

Each oriented graph edge carries an $SU(2)$ unitary. In configuration $C$, the rotation axis attached to the flux edge of an elementary triangle cycles through $x,y,z$. The comparison configuration $C'$ keeps the graph and flux placement fixed, but uses the same $z$ axis on every triangle. Thus the second configuration is commuting, while the first carries genuinely non-commuting transport.

The comparison changes the connection structure without changing the underlying graph, its size, or the locations of the flux edges.

### The scale of the construction

The graph grows exponentially with refinement. The matrix dimensions below follow directly from the exact graph-size formula.

| Refinement level $m$ | Vertices $|V_m|$ | Operator dimension $N_m$ |
|---:|---:|---:|
| 1 | 6 | 12 |
| 4 | 123 | 246 |
| 7 | 3,282 | 6,564 |
| 10 | 88,575 | 177,150 |
| 12 | 797,163 | 1,594,326 |

At level 12, the operator already acts on a space of dimension 1,594,326. The purpose of the recurrence and closed-form programme is to understand spectral quantities for this recursively growing family without treating every level as an unrelated finite matrix.

---

## 2. The central result: the fourth spectral moment

For the non-commuting configuration and its commuting control, define the fourth-moment trace defect

$$
\Delta_m(H^4,\theta)=\mathrm{Tr}(H_C(m,\theta)^4)-\mathrm{Tr}(H_{C'}(m,\theta)^4).
$$

The exact identity is

$$
\Delta_m(H^4,\theta)=-16(3^{m-1}+1)\sin^2(\theta/2),\quad m\geq1.
$$

This is the principal unconditional closed-form theorem in the repository. It is machine-checked in Lean 4 for every refinement level $m\geq1$ and every real angle $\theta$.

Normalizing by the matrix dimension gives

$$
I_m(\theta)=\Delta_m(H^4,\theta)/(3^{m+1}+3).
$$

Its exact limit is

$$
I_\infty(\theta)=-\frac{16}{9}\sin^2(\theta/2),\quad I_\infty(\pi/2)=-8/9.
$$

The proof, theorem declaration, numerical checks, and gauge-invariance record are linked below in [THEOREM.md](THEOREM.md), [VERIFICATION.md](VERIFICATION.md), and [formalization/README.md](formalization/README.md).

---

## 3. Higher spectral moments

The higher moments require separate arguments. The fourth-moment theorem does not by itself imply recurrences for the sixth, eighth, or tenth moments.

Use the notation $\Delta_m^{(p)}(\theta)$ for the trace defect at moment order $p$. For the recurrence statements, write $D_m^{(p)}(\theta)$ for the corresponding orientation-specific quantity in the Lean development.

### H⁶ — sixth moment

Lean proves the all-angle recurrence

$$
D_{m+1}^{(6)}(\theta)=3D_m^{(6)}(\theta)+C_6(\theta),\quad m\geq3.
$$

The exact finite polynomial certificate supplies the exceptional transition from level two to level three. Together, the Lean recurrence and that certificate give the all-level formula for $m\geq2$. The level-two value and coefficient are recorded in [docs/HIGHER_MOMENTS.md](docs/HIGHER_MOMENTS.md).

At $\theta=\pi$, the exact recurrence coefficient is $C_6(\pi)=5280$.

**Proof boundary:** the recurrence is inside the Lean kernel for $m\geq3$. The finite $m=2\to3$ bridge is an exact symbolic certificate, but is not yet a Lean-kernel theorem.

### H⁸ — eighth moment

Lean proves the all-angle affine recurrence

$$
D_{m+1}^{(8)}(\theta)=3D_m^{(8)}(\theta)+C_8(\theta),\quad m\geq3.
$$

An exact sparse-polynomial certificate establishes the exceptional finite transition and supplies the level-two polynomial. Together these give the explicit all-angle formula for $m\geq2$.

At $\theta=\pi$, the exact coefficient is $C_8(\pi)=277504$.

**Proof boundary:** the structural recurrence is Lean-formalized for $m\geq3$. The finite $m=2\to3$ bridge is an exact Gaussian-integer polynomial certificate, not yet a Lean-kernel theorem.


### H¹⁰ — tenth moment

The tenth-moment development includes the ordered p=10 trace expansion, exact word-stratum reductions, the gluing assembly, the two orientation recurrences, and corner-row transport through degree nine.

The radius-four glued-state diagonal transport required by the tenth-moment boundary correction is now proved in Lean for both the face-axis and fixed-axis configurations, at every level `m ≥ 4`. The theorem `H10TransportAll_proved` establishes `H10TransportAll` without additional assumptions.

Write $D_m^{(10)}(\theta)$ for the numbering-orientation defect, and let $C_{10}^{(5)}(\theta)$ be the exact level-five residual constant defined in Lean.

Lean therefore proves unconditionally

$$
D_{m+1}^{(10)}(\theta)=3D_m^{(10)}(\theta)+C_{10}^{(5)}(\theta),\quad m\geq4.
$$

Consequently, for every $m\geq5$,

$$
D_m^{(10)}(\theta)=3^{m-5}(D_5^{(10)}(\theta)+C_{10}^{(5)}(\theta)/2)-C_{10}^{(5)}(\theta)/2.
$$

Both the recurrence and the affine formula are machine-checked for every real angle. The level-five constant remains an exact finite trace expression; it has not yet been reduced to an explicit trigonometric polynomial. Thus the H¹⁰ affine theorem is unconditional, while its correction coefficient is retained in exact trace form.

The relevant Lean modules are `GlueTrace10`, `GlueRows10`, `FinalOrient10`, and `FinalClosed10`. The transport and final theorem names are listed in [docs/HIGHER_MOMENTS.md](docs/HIGHER_MOMENTS.md).


---

## 4. What the project establishes

| Result | Status | Evidence boundary |
|---|---|---|
| H⁴ exact closed form | **Unconditional theorem** | Lean-checked for all $m\geq1$ and all $\theta$. |
| Normalized H⁴ limit | **Exact formula** | Follows from the closed form and graph dimension. |
| H⁶ recurrence | **Lean theorem for $m\geq3$** | Finite level-two transition supplied by exact symbolic arithmetic. |
| H⁶ closed form for $m\geq2$ | **Lean recurrence + exact certificate** | The exceptional bridge is not yet in the Lean kernel. |
| H⁸ recurrence | **Lean theorem for $m\geq3$** | Finite level-two transition supplied by exact sparse-polynomial arithmetic. |
| H⁸ closed form for $m\geq2$ | **Lean recurrence + exact certificate** | The exceptional bridge is not yet in the Lean kernel. |
| H¹⁰ affine form | **Unconditional Lean theorem** | Degree-nine radius-four diagonal transport is proved for both configurations; the exact level-five trace correction is retained. |
| H⁶ path-class cancellation on $SG(1)$ | **Exact finite-level result** | Single- and two-triangle classes vanish; the all-three-triangle class contributes. |

A finite exact certificate, a numerical regression, and a Lean-kernel theorem are not interchangeable. The documentation preserves these proof boundaries explicitly.

---

## 5. The formal and computational programme

The repository brings together several complementary forms of work.

**Graph and operator construction.** The finite Sierpiński-gasket graphs, their indexing conventions, the $SU(2)$ connection, the non-commuting operator, and its commuting control are implemented in the Python source and formalized in Lean.

**Exact trace calculations.** The computational directory contains exact finite certificates, trace-word counts, reduction ledgers, and supporting calculations for the higher moments.

**Lean 4 proof.** The formalization contains the kernel-checked fourth-moment theorem and the higher-moment recurrence, gluing, orientation, and transport results. For H10, radius-four diagonal transport is proved for both configurations at every level m ≥ 4; consequently, the affine recurrence is an unconditional Lean theorem for m ≥ 4, and the affine closed form is an unconditional Lean theorem for m ≥ 5, for every real θ. The H6 and H8 finite base transitions remain exact certificates outside the Lean kernel. The proof boundaries and theorem names are stated next to the corresponding results.

**Reproducibility.** Tests, data, environment notes, and verification documents record how to repeat the computational checks. The chronological research journals preserve the sequence of proof work and mathematical decisions.

This is a research programme about a recursively defined family of large non-commutative operators. Its scale comes from the graph hierarchy and its spectral structure; its credibility comes from keeping the mathematical statements, proof assumptions, exact certificates, and numerical evidence distinguishable and inspectable.

---

## 6. Repository map

The tree below is synchronized with the current `main` branch. It includes the research journals, exact certificates, current H¹⁰ modules, source code, tests, and supporting data.

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

| Document | What it contains |
|---|---|
| [THEOREM.md](THEOREM.md) | Mathematical statement of the fourth-moment theorem and its scope. |
| [VERIFICATION.md](VERIFICATION.md) | Refinement tables, held-out checks, gauge test, and reproduction commands. |
| [docs/PROOF.md](docs/PROOF.md) | Human-readable proof of the fourth-moment identity. |
| [docs/EXACT_VERIFICATION.md](docs/EXACT_VERIFICATION.md) | Exact symbolic verification and the local mechanism. |
| [docs/SPLIT_AUTOMATON.md](docs/SPLIT_AUTOMATON.md) | Recursive split rule and its structural explanation. |
| [docs/HIGHER_MOMENTS.md](docs/HIGHER_MOMENTS.md) | Full H⁶, H⁸, and H¹⁰ formulas and proof boundaries. |
| [formalization/README.md](formalization/README.md) | Lean theorem, proof architecture, build command, and module map. |
| [formalization/HIGHER_MOMENT_RESEARCH_LOG.md](formalization/HIGHER_MOMENT_RESEARCH_LOG.md) | Chronological higher-moment research journal. |
| [formalization/PROOF_WORK_LOG.md](formalization/PROOF_WORK_LOG.md) | Chronological Lean proof-development journal. |

---

## 7. Reproduce the checks

From a clean checkout:

```bash
git clone https://github.com/RFT-SIRM/Evgeny-Theorem.git
cd Evgeny-Theorem
python3 -m venv .venv
source .venv/bin/activate
pip install -r reproducibility/requirements.txt
pytest tests/ -m "not slow" -v
pytest tests/ -m slow -v
lake build
```

The Python workflow runs the fast and slow suites on Python 3.11 and 3.12. The Lean workflow builds the formalization when Lean sources or the toolchain configuration change. A passing workflow certifies only the checks it actually executes.

---

## Authorship and research record

**Evgeny Zaprudnov**  
*Author of Evgeny's Theorem and originator of the mathematical research programme recorded in this repository.*

Sierpiński Gasket · Non-commutative SU(2) Connection · Spectral Moments · Lean 4

---

## License

Apache License 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
