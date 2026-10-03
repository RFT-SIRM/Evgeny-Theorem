import EvgenyTheorem.BaseCase

namespace EvgenyTheorem

open Matrix

theorem vIdx_one_00 : vIdx 1 (0, 0) = 0 := by first | decide | rfl
theorem vIdx_one_10 : vIdx 1 (1, 0) = 1 := by first | decide | rfl
theorem vIdx_one_01 : vIdx 1 (0, 1) = 2 := by first | decide | rfl
theorem vIdx_one_20 : vIdx 1 (2, 0) = 3 := by first | decide | rfl
theorem vIdx_one_11 : vIdx 1 (1, 1) = 4 := by first | decide | rfl
theorem vIdx_one_02 : vIdx 1 (0, 2) = 5 := by first | decide | rfl

/-- Basis of `HilbertIndex 1` in the order used by `Algebra.lean`
(vertex order of `sg_graph.py`, two spin components per vertex). -/
def vt12 : Fin 12 → HilbertIndex 1 :=
  ![(v00, 0), (v00, 1), (v10, 0), (v10, 1), (v01, 0), (v01, 1),
    (v20, 0), (v20, 1), (v11, 0), (v11, 1), (v02, 0), (v02, 1)]

theorem vt12_bijective : Function.Bijective vt12 := by decide

noncomputable def eqv12 : Fin 12 ≃ HilbertIndex 1 := Equiv.ofBijective vt12 vt12_bijective

theorem tr4_reindex {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (e : n ≃ m) (M : Matrix m m ℂ) :
    Matrix.trace (M * M * M * M) =
      Matrix.trace ((M.submatrix e e) * (M.submatrix e e) * (M.submatrix e e) *
        (M.submatrix e e)) := by
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact (Equiv.sum_comp e (fun i => (M * M * M * M) i i)).symm

theorem traceDefect_one_unfold (θ : ℝ) :
    traceDefect 1 θ =
      Matrix.trace (HC 1 θ * HC 1 θ * HC 1 θ * HC 1 θ) -
        Matrix.trace (HCprime 1 θ * HCprime 1 θ * HCprime 1 θ * HCprime 1 θ) := by
  unfold traceDefect
  congr <;> exact Subsingleton.elim _ _

-- calibration samples for the entry lemma (corrected finisher)
example (θ : ℝ) :
    HC 1 θ (v10, 0) (v00, 0) = - (axisRotation 0 θ)ᴴ 0 0 := by
  simp [HC, connectionOperatorWithAxis, v00, v10, Adj, EdgeB, edgeUnitaryWithAxis,
    fluxEdges_one, fluxIndex_one_0, faceAxis_zero, vIdx_one_00, vIdx_one_10]
    <;> exact if_neg (fun h => by have := congrArg Subtype.val h; simp at this)

example (θ : ℝ) : HC 1 θ (v00, 0) (v01, 0) = -1 := by
  simp [HC, connectionOperatorWithAxis, v00, v01, Adj, EdgeB, edgeUnitaryWithAxis,
    fluxEdges_one, vIdx_one_00, vIdx_one_01]
    <;> exact if_neg (fun h => by have := congrArg Subtype.val h; simp at this)

example (θ : ℝ) : HC 1 θ (v00, 0) (v20, 0) = 0 := by
  simp [HC, connectionOperatorWithAxis, v00, v20, Adj, EdgeB]
    <;> exact if_neg (fun h => by have := congrArg Subtype.val h; simp at this)

example (θ : ℝ) :
    HC 1 θ (v20, 0) (v10, 1) = - (axisRotation 1 θ)ᴴ 0 1 := by
  simp [HC, connectionOperatorWithAxis, v20, v10, Adj, EdgeB, edgeUnitaryWithAxis,
    fluxEdges_one, fluxIndex_one_1, faceAxis_one, vIdx_one_20, vIdx_one_10]
    <;> exact if_neg (fun h => by have := congrArg Subtype.val h; simp at this)

example (θ : ℝ) :
    HC 1 θ (v01, 1) (v11, 0) = - axisRotation 2 θ 1 0 := by
  simp [HC, connectionOperatorWithAxis, v01, v11, Adj, EdgeB, edgeUnitaryWithAxis,
    fluxEdges_one, fluxIndex_one_2, faceAxis_two, vIdx_one_01, vIdx_one_11]
    <;> exact if_neg (fun h => by have := congrArg Subtype.val h; simp at this)

end EvgenyTheorem
