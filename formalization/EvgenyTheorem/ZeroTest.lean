import EvgenyTheorem.Operator

namespace EvgenyTheorem

theorem axisRotation_zero (a : Axis) :
    axisRotation a 0 = (1 : Matrix C2 C2 ℂ) := by
  simp [axisRotation, su2Rotation]

theorem edgeUnitaryWithAxis_zero
    (m : ℕ) (axisOfIndex : ℕ → Axis) (e : Point × Point) :
    edgeUnitaryWithAxis m 0 axisOfIndex e =
      (1 : Matrix C2 C2 ℂ) := by
  classical
  by_cases h : e ∈ fluxEdges m
  · simp [edgeUnitaryWithAxis, h, axisRotation_zero]
  · simp [edgeUnitaryWithAxis, h]

end EvgenyTheorem

namespace EvgenyTheorem

theorem connectionOperatorWithAxis_zero_eq
    (m : ℕ) (a b : ℕ → Axis) :
    connectionOperatorWithAxis m 0 a =
      connectionOperatorWithAxis m 0 b := by
  classical
  letI : Finite (Vertex m) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (Vertex m) := Fintype.ofFinite (Vertex m)
  funext u v
  simp [connectionOperatorWithAxis, edgeUnitaryWithAxis_zero]

theorem HC_zero_eq_HCprime_zero (m : ℕ) :
    HC m 0 = HCprime m 0 := by
  exact connectionOperatorWithAxis_zero_eq m faceAxis (fun _ => 2)

end EvgenyTheorem

namespace EvgenyTheorem

noncomputable section

noncomputable def traceDefect0 (m : ℕ) (θ : ℝ) : ℂ := by
  classical
  letI : Finite (Vertex m) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (Vertex m) := Fintype.ofFinite (Vertex m)
  exact
    Matrix.trace
        (((HC m θ * HC m θ) * HC m θ) * HC m θ) -
      Matrix.trace
        (((HCprime m θ * HCprime m θ) * HCprime m θ) * HCprime m θ)

theorem traceDefect0_zero (m : ℕ) :
    traceDefect0 m 0 = 0 := by
  classical
  letI : Finite (Vertex m) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (Vertex m) := Fintype.ofFinite (Vertex m)
  simp only [traceDefect0]
  rw [HC_zero_eq_HCprime_zero m]
  ring

end
end EvgenyTheorem
