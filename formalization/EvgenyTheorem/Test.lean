import EvgenyTheorem.Operator

namespace EvgenyTheorem

noncomputable section

instance fintypeVertex (m : ℕ) : Finite (Vertex m) :=
  Finite.of_injective Subtype.val Subtype.val_injective

instance fintypeVertex' (m : ℕ) : Fintype (Vertex m) :=
  Fintype.ofFinite (Vertex m)

def traceFourth
    (A : Matrix (HilbertIndex 1) (HilbertIndex 1) ℂ) : ℂ :=
  Matrix.trace (((A * A) * A) * A)

#check traceFourth
#check HC
#check HCprime


noncomputable def traceDefect (m : ℕ) (θ : ℝ) : ℂ :=
  Matrix.trace
      (((HC m θ * HC m θ) * HC m θ) * HC m θ) -
    Matrix.trace
      (((HCprime m θ * HCprime m θ) * HCprime m θ) * HCprime m θ)

#check traceDefect

end
end EvgenyTheorem

#eval (facesExact 1).length
#eval (fluxEdges 1).length
#eval (fluxIndex 1 (fluxEdges 1).get! 0)
#eval (fluxIndex 1 (fluxEdges 1).get! 1)
#eval (fluxIndex 1 (fluxEdges 1).get! 2)
#eval ((faceAxis 0).val, (faceAxis 1).val, (faceAxis 2).val)
