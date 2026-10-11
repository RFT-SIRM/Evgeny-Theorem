# Lean formalization — Evgeny's Theorem

Lean 4 + Mathlib (versions pinned in `lean-toolchain` / `lakefile.toml`). Build with `lake build`.

## Main result (machine-checked)

For every refinement level `m ≥ 1` and every angle `θ`, for the concrete operators:

```lean
theorem traceDefect_closed (θ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    traceDefect m θ =
      -16 * ((3 : ℂ) ^ (m - 1) + 1) * ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2
```

(`EvgenyTheorem/TildeEntries.lean`). `EvgenyTheorem.lean` restates it with the real closed form `delta` as
`traceDefect m θ = (delta m θ : ℂ)` (`traceDefect_eq_delta`, with `traceDefect_re_eq_delta` and
`traceDefect_im_eq_zero`). `traceDefect m θ` is the difference of the fourth traces of `HC` and `HCprime`
(`Operator.lean`).

Scope: `m ≥ 1` only; the fourth moment only. No `sorry`, no numerical tolerance, no axiom asserting the target.
`SanityChecks.lean` uses `native_decide` for a few degree examples at level 1; the final theorems do not depend on it.

## Check it

    lake build
    printf 'import EvgenyTheorem\n#print axioms EvgenyTheorem.traceDefect_closed\n' > /tmp/ax.lean
    lake env lean /tmp/ax.lean      # expect: propext, Classical.choice, Quot.sound

## Proof structure

The route differs from the hand proof in `docs/PROOF.md`: it glues three copies of level `m` into level `m+1` and
closes a coupled recursion over two orientations (full plan: `docs/LEAN_PLAN_GENERAL_M.md`, "Final route").

1. **Base cases.** `traceDefect_one` (`m = 1`, explicit 12×12 matrices in `Algebra.lean`, `BaseCaseTheorem.lean`) and
   `tilde_base` (`TildeBase.lean`, `TildeEntries.lean`, `AlgebraTilde.lean`): the same computation with the corner flux edge
   reversed, where the defect is `0`.
2. **Gluing.** `H_{m+1} = E K Eᵀ` for the block-diagonal operator `K` of three copies (`GlueSG`, `GlueK`); an abstract
   trace identity (`GlueAlg`, `GlueBridge`, `GlueTrace`) leaves only corner data at the six glued points, proved as
   `sgK_corner_data` (`GlueCorner*.lean`: corner geometry, triangle sum, independence of the axis function).
3. **Orientation transport.** The numbering orientation on the three copies is transported to level `m` and to the
   orientation with the corner edge reversed (`FinalOrient.lean`, using `FlipFaces.lean`).
4. **Coupled recursion and induction.** `defect_succ_num`: `D_{m+1} = 2 D_m + D~_m`; `defect_succ_til`:
   `D~_{m+1} = D_m + 2 D~_m` (`FinalTilde.lean`); the closed form follows by induction (`FinalArith.lean`,
   `FinalTheorem.lean`).

Edge orientation is the vertex-index order `vIdx` of `sg_graph.py` (`Orientation.lean`); see `docs/ORIENTATION_NOTE.md`
for why this matters.

## File map

| Layer | Files |
|---|---|
| Graph and gasket structure | `Graph/Sierpinski`, `Graph/Faces`, `SGStruct`, `EdgeStep`, `EdgeCopies`, `EdgeSplit`, `VertexOrder`, `VertexIndex`, `ListOrder`, `Orientation`, `CornerFaces` |
| SU(2) and operators | `SU2`, `Operator`, `Locality`, `PointModel1`, `PointModel2`, `OpSplit1`–`3`, `DegSplit`, `FluxSplit`, `OrientSq`, `PairUnit` |
| Orientation flips | `FlipB`, `FlipC`, `FlipFaces`, `FlipCount` |
| Base cases | `Algebra`, `Setup`, `BaseCase`, `BaseCaseTheorem`, `TraceExpand`, `AlgebraTilde`, `TildeBase`, `TildeEntries` |
| Gluing | `GlueAlg`, `GlueBridge`, `GlueSG`, `GlueK`, `GlueTrace`, `GlueCorner`, `GlueCornerData`, `GlueCornerU`, `GlueCornerTri`, `GlueCornerSum`, `GlueCornerGeom`, `GlueCornerCube` |
| Recursion and closed form | `FinalOrient`, `FinalArith`, `FinalTilde`, `FinalTheorem`, `TildeEntries` |
| Sanity checks | `SanityChecks`, `SanityChecksLevel4` (slow; not in the default build) |

The Python suite in the main repository remains the computational verification layer for the numerical claims
(including H6/H8/H10, which are not covered by this formalization).

Do **not** make `formalization/` a separate Git repository and do not create a nested `.git`.
