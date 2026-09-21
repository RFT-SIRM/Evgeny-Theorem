import EvgenyTheorem.Operator

namespace EvgenyTheorem
noncomputable section

example : InSG 1 0 0 := by simp [InSG]
example : InSG 1 1 0 := by simp [InSG]
example : InSG 1 0 1 := by simp [InSG]
example : InSG 1 2 0 := by simp [InSG]
example : InSG 1 1 1 := by simp [InSG]
example : InSG 1 0 2 := by simp [InSG]

example : ¬ InSG 1 1 2 := by simp [InSG]
example : ¬ InSG 1 2 1 := by simp [InSG]
example : ¬ InSG 1 2 2 := by simp [InSG]

def vertices1 : List (Vertex 1) :=
  [ ⟨(0, 0), by simp [InSG]⟩
  , ⟨(1, 0), by simp [InSG]⟩
  , ⟨(0, 1), by simp [InSG]⟩
  , ⟨(2, 0), by simp [InSG]⟩
  , ⟨(1, 1), by simp [InSG]⟩
  , ⟨(0, 2), by simp [InSG]⟩ ]

example : degree 1 ⟨(0, 0), by simp [InSG]⟩ = 2 := by
  simp only [degree]
  rw [Finset.card_eq_two]
  refine ⟨⟨(1, 0), by simp [InSG]⟩, ⟨(0, 1), by simp [InSG]⟩, ?_, ?_⟩
  · intro h
    simp [Adj, EdgeB, InSG] at h
  · simp [Adj, EdgeB, InSG]

end
end EvgenyTheorem

namespace EvgenyTheorem

#check Fintype.equivFin
#check Fintype.equivFinOfCardEq
#check Fintype.sum_equiv

end EvgenyTheorem
