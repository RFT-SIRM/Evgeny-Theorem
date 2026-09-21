import EvgenyTheorem.Operator

namespace EvgenyTheorem

noncomputable section

instance finiteVertexSG1 : Finite (Vertex 1) :=
  Finite.of_injective
    (fun v : Vertex 1 => v.1)
    (by
      intro a b h
      exact Subtype.ext h)

instance fintypeVertexSG1 : Fintype (Vertex 1) :=
  Fintype.ofFinite (Vertex 1)

def traceFourthSG1 (A : Matrix (HilbertIndex 1) (HilbertIndex 1) ℂ) : ℂ :=
  Matrix.trace (((A * A) * A) * A)

example : traceDefect 1 0 = 0 := by
  exact traceDefect_zero 1

end

end EvgenyTheorem
