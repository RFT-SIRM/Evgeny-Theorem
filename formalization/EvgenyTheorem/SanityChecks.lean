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

end EvgenyTheorem
