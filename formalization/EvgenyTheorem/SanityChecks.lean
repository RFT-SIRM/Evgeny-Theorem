import EvgenyTheorem.Graph.Sierpinski
import EvgenyTheorem.Operator

/-!
# Sanity checks for the graph-level formalization

These are *not* the theorem. They confirm that `Vertex`, `Adj` and `degree`
are wired up correctly and are fully computable, using `Vertex.fintype`
and `Adj.decidable` from `Graph/Sierpinski.lean`. Everything here is
decidable because it only involves natural numbers and finite graphs -- it
says nothing about the theta : R, SU(2)-valued part of the construction,
which cannot be checked by `decide`/`native_decide`.
-/

namespace EvgenyTheorem

example : Fintype.card (Vertex 1) = 6 := by decide
example : Fintype.card (Vertex 2) = 15 := by decide

-- Degrees at level 1: the three outer corners have degree 2,
-- the three edge midpoints have degree 4.
example : degree 1 ⟨(0, 0), by decide⟩ = 2 := by native_decide
example : degree 1 ⟨(2, 0), by decide⟩ = 2 := by native_decide
example : degree 1 ⟨(0, 2), by decide⟩ = 2 := by native_decide
example : degree 1 ⟨(1, 0), by decide⟩ = 4 := by native_decide
example : degree 1 ⟨(0, 1), by decide⟩ = 4 := by native_decide
example : degree 1 ⟨(1, 1), by decide⟩ = 4 := by native_decide


/-! ### Named structural facts (levels 1, 2 and 3)

These are the Lean-checked versions of the graph facts used in
`docs/PROOF.md` §4.1 and `docs/EXACT_VERIFICATION.md` §2: `SG(m)` has
exactly three vertices of degree 2 (the outer corners), and every vertex
has degree 2 or 4 (so every non-corner vertex has degree exactly 4).

Each is proved by plain `decide` (kernel-checked; the only axioms are the
standard `propext`, `Classical.choice`, `Quot.sound` — no `native_decide`)
for the concrete levels below; level 4 is in `SanityChecksLevel4.lean`,
kept out of the default build because it takes about three minutes. For
general `m` these facts need induction through `InSG`/`EdgeB` — not done
here. -/

theorem card_degree_two_level1 :
    (Finset.univ.filter (fun v : Vertex 1 => degree 1 v = 2)).card = 3 := by
  decide

theorem card_degree_two_level2 :
    (Finset.univ.filter (fun v : Vertex 2 => degree 2 v = 2)).card = 3 := by
  decide

set_option maxRecDepth 100000 in
theorem card_degree_two_level3 :
    (Finset.univ.filter (fun v : Vertex 3 => degree 3 v = 2)).card = 3 := by
  decide

theorem degrees_are_two_or_four_level1 :
    ∀ v : Vertex 1, degree 1 v = 2 ∨ degree 1 v = 4 := by
  decide

theorem degrees_are_two_or_four_level2 :
    ∀ v : Vertex 2, degree 2 v = 2 ∨ degree 2 v = 4 := by
  decide

set_option maxRecDepth 100000 in
theorem degrees_are_two_or_four_level3 :
    ∀ v : Vertex 3, degree 3 v = 2 ∨ degree 3 v = 4 := by
  decide

end EvgenyTheorem
