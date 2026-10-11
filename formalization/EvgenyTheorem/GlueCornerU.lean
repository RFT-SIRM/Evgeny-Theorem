import EvgenyTheorem.GlueCornerData
import EvgenyTheorem.BaseCaseTheorem

namespace EvgenyTheorem

open Matrix

/-- The cube of the glued operator on the diagonal is the cube of one copy block. -/
theorem sgK_cube_eq (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (c : GCopy) (x : Pt m) (i : C2) :
    (sgK m θ ax o * sgK m θ ax o * sgK m θ ax o) (c, x, i) (c, x, i) =
      (Hc m θ ax o c * Hc m θ ax o c * Hc m θ ax o c) (x, i) (x, i) := by
  unfold sgK
  rw [blockK_mul, blockK_mul]
  simp [blockK]

/-- `U + U†` for a rotation does not depend on the axis. -/
theorem axisRotation_add_conj (a : Axis) (θ : ℝ) :
    axisRotation a θ + (axisRotation a θ)ᴴ = (2 * cC θ) • (1 : Matrix C2 C2 ℂ) := by
  fin_cases a
  · show axisRotation 0 θ + (axisRotation 0 θ)ᴴ = _
    rw [rotXh, rotX]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  · show axisRotation 1 θ + (axisRotation 1 θ)ᴴ = _
    rw [rotYh, rotY]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  · show axisRotation 2 θ + (axisRotation 2 θ)ᴴ = _
    rw [rotZh, rotZ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

open Classical in
/-- `U + U†` of an edge block: `2cos(θ/2)` on flux edges, `2` on other edges. -/
theorem edgeU_add_conj (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (e : Point × Point) :
    edgeUnitaryWithAxis m θ ax e + (edgeUnitaryWithAxis m θ ax e)ᴴ =
      (if e ∈ fluxEdges m then 2 * cC θ else 2) • (1 : Matrix C2 C2 ℂ) := by
  unfold edgeUnitaryWithAxis
  by_cases h : e ∈ fluxEdges m
  · rw [if_pos h, if_pos h]
    exact axisRotation_add_conj _ _
  · rw [if_neg h, if_neg h]
    simp [two_smul]

end EvgenyTheorem
