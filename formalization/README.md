# Lean 4 formalization — Evgeny's Theorem

The Lean project is built with the pinned Lean toolchain and Mathlib versions in `lean-toolchain` and `lakefile.toml`. The repository root sets `srcDir = "formalization"`, so all commands below are run from the repository root.

## Main theorem: fourth spectral moment

For every refinement level $m\ge1$ and every angle $\theta$, the concrete operators satisfy

```lean
theorem traceDefect_closed (θ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    traceDefect m θ =
      -16 * ((3 : ℂ) ^ (m - 1) + 1) * ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2
```

The theorem is in `EvgenyTheorem/TildeEntries.lean`. The root module `EvgenyTheorem.lean` restates the identity using the real closed form `delta` through `traceDefect_eq_delta`, `traceDefect_re_eq_delta`, and `traceDefect_im_eq_zero`.

The final theorem contains no `sorry` and uses the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. It is a theorem about the concrete H⁴ operators for $m\ge1$; it does not by itself prove the higher-moment results.

## Build and inspect the theorem

Run from the repository root:

```bash
lake build
```

To inspect the declared axioms:

```bash
printf 'import EvgenyTheorem\n#print axioms EvgenyTheorem.traceDefect_closed\n' > /tmp/ax.lean
lake env lean /tmp/ax.lean
```

`SanityChecks.lean` uses `native_decide` for selected finite graph checks. Those checks are not assumptions in the proof of `traceDefect_closed`.

## Proof architecture for H⁴

The Lean proof uses the recursive gluing of three level-$m$ copies into level $m+1$ and a coupled recursion over two orientations.

1. **Base cases.** `traceDefect_one` treats level one with explicit 12×12 matrices. `tilde_base` treats the orientation with the corner flux edge reversed.
2. **Gluing.** The next-level operator is represented using a block-diagonal operator of three copies. `GlueAlg`, `GlueBridge`, `GlueSG`, and `GlueK` reduce the trace identity to corner data.
3. **Corner structure.** The `GlueCorner*` modules establish the geometric and algebraic identities at the glued vertices.
4. **Orientation transport.** `FinalOrient` and the flip modules identify the orientations induced on the copies.
5. **Coupled recursion.** `FinalTilde` proves the two recurrences
   $D_{m+1}=2D_m+\widetilde D_m$ and
   $\widetilde D_{m+1}=D_m+2\widetilde D_m$.
6. **Closed form.** `FinalArith` and `FinalTheorem` complete the induction.

The edge orientation is the vertex-index order `vIdx` of the graph construction. See [ORIENTATION_NOTE.md](../docs/ORIENTATION_NOTE.md).

## Higher moments: current Lean boundary

The H⁶ and H⁸ Lean developments prove their all-angle structural recurrences for the stated ranges. Their exceptional finite base transitions are verified by separate exact symbolic certificates and are not yet Lean-kernel theorems.

The H¹⁰ development is more extensive than a numerical reference calculation. The current source contains the p=10 gluing assembly, exact ordered-word stratum reductions, orientation recurrences, and row transport through degree nine. The final affine formula is machine-checked under the explicit assumption `H10TransportAll`. That assumption is not proved in the current source, so the H¹⁰ formula is conditional rather than an unconditional Lean theorem. See [HIGHER_MOMENTS.md](../docs/HIGHER_MOMENTS.md) for the formulas and exact proof boundaries.

## Lean module map

The following list matches the Lean modules currently present under `formalization/EvgenyTheorem/`.

| Layer | Modules |
|---|---|
| **Graph geometry and indexing** | `Graph/Sierpinski`, `Graph/Faces`, `SGStruct`, `CornerFaces`, `CornerLocality`, `EdgeStep`, `EdgeCopies`, `EdgeSplit`, `VertexIndex`, `VertexOrder`, `ListOrder`, `Orientation` |
| **SU(2) operators and local structure** | `SU2`, `Operator`, `Locality`, `PointModel1`, `PointModel2`, `OpSplit1`, `OpSplit2`, `OpSplit3`, `DegSplit`, `FluxSplit`, `OrientSq`, `PairUnit` |
| **Orientation changes** | `FlipB`, `FlipC`, `FlipCount`, `FlipFaces` |
| **Base cases and trace expansion** | `Algebra`, `AlgebraTilde`, `BaseCase`, `BaseCaseTheorem`, `Setup`, `TildeBase`, `TildeEntries`, `TraceExpand` |
| **Gluing and corner data** | `GlueAlg`, `GlueBridge`, `GlueCorner`, `GlueCornerCube`, `GlueCornerData`, `GlueCornerGeom`, `GlueCornerSum`, `GlueCornerTri`, `GlueCornerU`, `GlueK`, `GlueSG`, `GlueTrace` |
| **H¹⁰ gluing and transport** | `GlueRows10`, `GlueTrace10` |
| **Recurrences and closed forms** | `FinalArith`, `FinalOrient`, `FinalOrient10`, `FinalClosed10`, `FinalTheorem`, `FinalTilde` |
| **Finite graph checks** | `SanityChecks`, `SanityChecksLevel4` (the level-four check is slow and is not part of the default build) |

## Research records and supporting directories

The primary chronological records are:

- `formalization/HIGHER_MOMENT_RESEARCH_LOG.md` — detailed higher-moment research journal;
- `formalization/PROOF_WORK_LOG.md` — Lean proof-development journal.

Other supporting material:

- `computational/` — exact finite symbolic certificates, corner-power reports, and trace-word inventories;
- `tests/` — numerical regression, exact symbolic checks, graph-convention checks, and structural tests;
- `docs/` — mathematical proofs, exact verification, higher-moment status, orientation note, and proof roadmaps;
- `src/` — Python graph, SU(2), operator, and moment implementations.

Do not make `formalization/` a separate Git repository and do not create a nested `.git` directory.
