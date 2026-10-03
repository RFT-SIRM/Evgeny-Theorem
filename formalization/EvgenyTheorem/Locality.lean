import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import EvgenyTheorem.Operator

namespace EvgenyTheorem

open Matrix

theorem axisRotation_unitary_left (a : Axis) (θ : ℝ) :
    (axisRotation a θ)ᴴ * axisRotation a θ = 1 :=
  mul_eq_one_comm.mp (axisRotation_unitary a θ)

theorem edgeUnitaryWithAxis_mul_conjTranspose
    (m : ℕ) (θ : ℝ) (axisOfIndex : ℕ → Axis) (e : Point × Point) :
    edgeUnitaryWithAxis m θ axisOfIndex e *
      (edgeUnitaryWithAxis m θ axisOfIndex e)ᴴ = 1 := by
  unfold edgeUnitaryWithAxis
  split_ifs
  · exact axisRotation_unitary _ _
  · simp

theorem edgeUnitaryWithAxis_conjTranspose_mul
    (m : ℕ) (θ : ℝ) (axisOfIndex : ℕ → Axis) (e : Point × Point) :
    (edgeUnitaryWithAxis m θ axisOfIndex e)ᴴ *
      edgeUnitaryWithAxis m θ axisOfIndex e = 1 :=
  mul_eq_one_comm.mp (edgeUnitaryWithAxis_mul_conjTranspose m θ axisOfIndex e)

theorem edgeUnitary_mul_conjTranspose (m : ℕ) (θ : ℝ) (e : Point × Point) :
    edgeUnitary m θ e * (edgeUnitary m θ e)ᴴ = 1 := by
  unfold edgeUnitary
  split_ifs
  · exact axisRotation_unitary _ _
  · simp

theorem edgeUnitary_conjTranspose_mul (m : ℕ) (θ : ℝ) (e : Point × Point) :
    (edgeUnitary m θ e)ᴴ * edgeUnitary m θ e = 1 :=
  mul_eq_one_comm.mp (edgeUnitary_mul_conjTranspose m θ e)

end EvgenyTheorem
