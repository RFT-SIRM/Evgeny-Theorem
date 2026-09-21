import EvgenyTheorem.Operator

namespace EvgenyTheorem

noncomputable section

instance finiteVertex (m : ℕ) : Finite (Vertex m) :=
  Finite.of_injective
    (fun v : Vertex m => v.1)
    (by
      intro a b h
      exact Subtype.ext h)

noncomputable instance fintypeVertex (m : ℕ) : Fintype (Vertex m) :=
  Fintype.ofFinite (Vertex m)

example (u : HilbertIndex 1) :
    HC 1 0 u u = Complex.ofReal (degree 1 u.1) := by
  exact connectionOperator_diagonal 1 0 u

example :
    HC 1 0 = HCprime 1 0 := by
  exact connectionOperatorWithAxis_zero_eq 1 faceAxis (fun _ => 2)

end
end EvgenyTheorem
