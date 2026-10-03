import EvgenyTheorem.Setup
import EvgenyTheorem.Algebra

set_option maxHeartbeats 8000000

namespace EvgenyTheorem

open Matrix

noncomputable def cC (θ : ℝ) : ℂ := ((Real.cos (θ / 2) : ℝ) : ℂ)
noncomputable def sC (θ : ℝ) : ℂ := ((Real.sin (θ / 2) : ℝ) : ℂ)

theorem conj_cC (θ : ℝ) : (starRingEnd ℂ) (cC θ) = cC θ := Complex.conj_ofReal _
theorem conj_sC (θ : ℝ) : (starRingEnd ℂ) (sC θ) = sC θ := Complex.conj_ofReal _

/-! ### Explicit SU(2) rotations -/

theorem rotX (θ : ℝ) :
    axisRotation 0 θ = !![cC θ, -(Complex.I * sC θ); -(Complex.I * sC θ), cC θ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisRotation, axisPauli, su2Rotation, pauliX, cC, sC] <;> ring

theorem rotY (θ : ℝ) :
    axisRotation 1 θ = !![cC θ, -sC θ; sC θ, cC θ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisRotation, axisPauli, su2Rotation, pauliY, cC, sC] <;> ring_nf <;> simp

theorem rotZ (θ : ℝ) :
    axisRotation 2 θ =
      !![cC θ - Complex.I * sC θ, 0; 0, cC θ + Complex.I * sC θ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisRotation, axisPauli, su2Rotation, pauliZ, cC, sC] <;> ring

theorem rotXh (θ : ℝ) :
    (axisRotation 0 θ)ᴴ = !![cC θ, Complex.I * sC θ; Complex.I * sC θ, cC θ] := by
  rw [rotX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Complex.star_def, conj_cC, conj_sC, Complex.conj_I, map_neg, map_mul] <;> ring

theorem rotYh (θ : ℝ) :
    (axisRotation 1 θ)ᴴ = !![cC θ, sC θ; -sC θ, cC θ] := by
  rw [rotY]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Complex.star_def, conj_cC, conj_sC, Complex.conj_I, map_neg, map_mul] <;> ring

theorem rotZh (θ : ℝ) :
    (axisRotation 2 θ)ᴴ =
      !![cC θ + Complex.I * sC θ, 0; 0, cC θ - Complex.I * sC θ] := by
  rw [rotZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Complex.star_def, conj_cC, conj_sC, Complex.conj_I, map_neg, map_mul] <;> ring

/-! ### Basis points and degrees -/

theorem eqv12_0 : eqv12 0 = (v00, 0) := rfl
theorem eqv12_1 : eqv12 1 = (v00, 1) := rfl
theorem eqv12_2 : eqv12 2 = (v10, 0) := rfl
theorem eqv12_3 : eqv12 3 = (v10, 1) := rfl
theorem eqv12_4 : eqv12 4 = (v01, 0) := rfl
theorem eqv12_5 : eqv12 5 = (v01, 1) := rfl
theorem eqv12_6 : eqv12 6 = (v20, 0) := rfl
theorem eqv12_7 : eqv12 7 = (v20, 1) := rfl
theorem eqv12_8 : eqv12 8 = (v11, 0) := rfl
theorem eqv12_9 : eqv12 9 = (v11, 1) := rfl
theorem eqv12_10 : eqv12 10 = (v02, 0) := rfl
theorem eqv12_11 : eqv12 11 = (v02, 1) := rfl

-- degrees, stated for the unfolded `Subtype.mk` form that `simp [v00, ...]` produces
theorem deg_mk00 : degree 1 (⟨(0, 0), by decide⟩ : Vertex 1) = 2 := by decide
theorem deg_mk10 : degree 1 (⟨(1, 0), by decide⟩ : Vertex 1) = 4 := by decide
theorem deg_mk01 : degree 1 (⟨(0, 1), by decide⟩ : Vertex 1) = 4 := by decide
theorem deg_mk20 : degree 1 (⟨(2, 0), by decide⟩ : Vertex 1) = 2 := by decide
theorem deg_mk11 : degree 1 (⟨(1, 1), by decide⟩ : Vertex 1) = 4 := by decide
theorem deg_mk02 : degree 1 (⟨(0, 2), by decide⟩ : Vertex 1) = 2 := by decide

theorem ne_0_1 : (⟨(0, 0), by decide⟩ : Vertex 1) ≠ ⟨(1, 0), by decide⟩ := by decide
theorem ne_0_2 : (⟨(0, 0), by decide⟩ : Vertex 1) ≠ ⟨(0, 1), by decide⟩ := by decide
theorem ne_0_3 : (⟨(0, 0), by decide⟩ : Vertex 1) ≠ ⟨(2, 0), by decide⟩ := by decide
theorem ne_0_4 : (⟨(0, 0), by decide⟩ : Vertex 1) ≠ ⟨(1, 1), by decide⟩ := by decide
theorem ne_0_5 : (⟨(0, 0), by decide⟩ : Vertex 1) ≠ ⟨(0, 2), by decide⟩ := by decide
theorem ne_1_0 : (⟨(1, 0), by decide⟩ : Vertex 1) ≠ ⟨(0, 0), by decide⟩ := by decide
theorem ne_1_2 : (⟨(1, 0), by decide⟩ : Vertex 1) ≠ ⟨(0, 1), by decide⟩ := by decide
theorem ne_1_3 : (⟨(1, 0), by decide⟩ : Vertex 1) ≠ ⟨(2, 0), by decide⟩ := by decide
theorem ne_1_4 : (⟨(1, 0), by decide⟩ : Vertex 1) ≠ ⟨(1, 1), by decide⟩ := by decide
theorem ne_1_5 : (⟨(1, 0), by decide⟩ : Vertex 1) ≠ ⟨(0, 2), by decide⟩ := by decide
theorem ne_2_0 : (⟨(0, 1), by decide⟩ : Vertex 1) ≠ ⟨(0, 0), by decide⟩ := by decide
theorem ne_2_1 : (⟨(0, 1), by decide⟩ : Vertex 1) ≠ ⟨(1, 0), by decide⟩ := by decide
theorem ne_2_3 : (⟨(0, 1), by decide⟩ : Vertex 1) ≠ ⟨(2, 0), by decide⟩ := by decide
theorem ne_2_4 : (⟨(0, 1), by decide⟩ : Vertex 1) ≠ ⟨(1, 1), by decide⟩ := by decide
theorem ne_2_5 : (⟨(0, 1), by decide⟩ : Vertex 1) ≠ ⟨(0, 2), by decide⟩ := by decide
theorem ne_3_0 : (⟨(2, 0), by decide⟩ : Vertex 1) ≠ ⟨(0, 0), by decide⟩ := by decide
theorem ne_3_1 : (⟨(2, 0), by decide⟩ : Vertex 1) ≠ ⟨(1, 0), by decide⟩ := by decide
theorem ne_3_2 : (⟨(2, 0), by decide⟩ : Vertex 1) ≠ ⟨(0, 1), by decide⟩ := by decide
theorem ne_3_4 : (⟨(2, 0), by decide⟩ : Vertex 1) ≠ ⟨(1, 1), by decide⟩ := by decide
theorem ne_3_5 : (⟨(2, 0), by decide⟩ : Vertex 1) ≠ ⟨(0, 2), by decide⟩ := by decide
theorem ne_4_0 : (⟨(1, 1), by decide⟩ : Vertex 1) ≠ ⟨(0, 0), by decide⟩ := by decide
theorem ne_4_1 : (⟨(1, 1), by decide⟩ : Vertex 1) ≠ ⟨(1, 0), by decide⟩ := by decide
theorem ne_4_2 : (⟨(1, 1), by decide⟩ : Vertex 1) ≠ ⟨(0, 1), by decide⟩ := by decide
theorem ne_4_3 : (⟨(1, 1), by decide⟩ : Vertex 1) ≠ ⟨(2, 0), by decide⟩ := by decide
theorem ne_4_5 : (⟨(1, 1), by decide⟩ : Vertex 1) ≠ ⟨(0, 2), by decide⟩ := by decide
theorem ne_5_0 : (⟨(0, 2), by decide⟩ : Vertex 1) ≠ ⟨(0, 0), by decide⟩ := by decide
theorem ne_5_1 : (⟨(0, 2), by decide⟩ : Vertex 1) ≠ ⟨(1, 0), by decide⟩ := by decide
theorem ne_5_2 : (⟨(0, 2), by decide⟩ : Vertex 1) ≠ ⟨(0, 1), by decide⟩ := by decide
theorem ne_5_3 : (⟨(0, 2), by decide⟩ : Vertex 1) ≠ ⟨(2, 0), by decide⟩ := by decide
theorem ne_5_4 : (⟨(0, 2), by decide⟩ : Vertex 1) ≠ ⟨(1, 1), by decide⟩ := by decide

/-! ### The 144 entries -/

theorem ite_eq_of {α : Type*} {c : Prop} {inst : Decidable c} {x y z : α}
    (h1 : c → x = z) (h2 : ¬c → y = z) : @ite α c inst x y = z := by
  cases inst with
  | isFalse hc => exact h2 hc
  | isTrue hc => exact h1 hc

local macro "close_entry" : tactic => `(tactic| (
  refine ite_eq_of (fun h => ?pos) (fun h => ?neg)
  case pos => first
    | rfl
    | (exfalso; exact absurd h ne_0_1)
    | (exfalso; exact absurd h ne_0_2)
    | (exfalso; exact absurd h ne_0_3)
    | (exfalso; exact absurd h ne_0_4)
    | (exfalso; exact absurd h ne_0_5)
    | (exfalso; exact absurd h ne_1_0)
    | (exfalso; exact absurd h ne_1_2)
    | (exfalso; exact absurd h ne_1_3)
    | (exfalso; exact absurd h ne_1_4)
    | (exfalso; exact absurd h ne_1_5)
    | (exfalso; exact absurd h ne_2_0)
    | (exfalso; exact absurd h ne_2_1)
    | (exfalso; exact absurd h ne_2_3)
    | (exfalso; exact absurd h ne_2_4)
    | (exfalso; exact absurd h ne_2_5)
    | (exfalso; exact absurd h ne_3_0)
    | (exfalso; exact absurd h ne_3_1)
    | (exfalso; exact absurd h ne_3_2)
    | (exfalso; exact absurd h ne_3_4)
    | (exfalso; exact absurd h ne_3_5)
    | (exfalso; exact absurd h ne_4_0)
    | (exfalso; exact absurd h ne_4_1)
    | (exfalso; exact absurd h ne_4_2)
    | (exfalso; exact absurd h ne_4_3)
    | (exfalso; exact absurd h ne_4_5)
    | (exfalso; exact absurd h ne_5_0)
    | (exfalso; exact absurd h ne_5_1)
    | (exfalso; exact absurd h ne_5_2)
    | (exfalso; exact absurd h ne_5_3)
    | (exfalso; exact absurd h ne_5_4)
    | (simp [eqv12, vt12, Equiv.ofBijective_apply, Matrix.one_apply]; done)
  case neg => first
    | rfl
    | (exfalso; exact absurd rfl h)
    | (simp [eqv12, vt12, Equiv.ofBijective_apply, Matrix.one_apply]; done)
    | (simp [eqv12, vt12, Equiv.ofBijective_apply, Matrix.one_apply]; ring)
    | (norm_num [Matrix.one_apply, eqv12_0, eqv12_1, eqv12_2, eqv12_3, eqv12_4, eqv12_5, eqv12_6, eqv12_7, eqv12_8, eqv12_9, eqv12_10, eqv12_11]; done)
    | (norm_num [Matrix.one_apply, eqv12_0, eqv12_1, eqv12_2, eqv12_3, eqv12_4, eqv12_5, eqv12_6, eqv12_7, eqv12_8, eqv12_9, eqv12_10, eqv12_11]; ring)))

theorem HC_sub (θ : ℝ) :
    (HC 1 θ).submatrix eqv12 eqv12 = HC12 (cC θ) (sC θ) Complex.I := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.submatrix_apply, eqv12_0, eqv12_1, eqv12_2, eqv12_3, eqv12_4, eqv12_5,
      eqv12_6, eqv12_7, eqv12_8, eqv12_9, eqv12_10, eqv12_11,
      HC, connectionOperatorWithAxis, HC12, Adj, EdgeB, edgeUnitaryWithAxis,
      fluxEdges_one, fluxIndex_one_0, fluxIndex_one_1, fluxIndex_one_2,
      faceAxis_zero, faceAxis_one, faceAxis_two,
      vIdx_one_00, vIdx_one_10, vIdx_one_01, vIdx_one_20, vIdx_one_11, vIdx_one_02,
      v00, v10, v01, v20, v11, v02,
      deg_mk00, deg_mk10, deg_mk01, deg_mk20, deg_mk11, deg_mk02,
      ne_0_1, ne_0_2, ne_0_3, ne_0_4, ne_0_5, ne_1_0, ne_1_2, ne_1_3, ne_1_4, ne_1_5, ne_2_0, ne_2_1, ne_2_3, ne_2_4, ne_2_5, ne_3_0, ne_3_1, ne_3_2, ne_3_4, ne_3_5, ne_4_0, ne_4_1, ne_4_2, ne_4_3, ne_4_5, ne_5_0, ne_5_1, ne_5_2, ne_5_3, ne_5_4,
      conj_cC, conj_sC, Complex.star_def, Complex.conj_I, map_neg, map_mul,
      rotX, rotY, rotZ, rotXh, rotYh, rotZh]
    <;> first
      | close_entry
      | (try ring)

theorem HCprime_sub (θ : ℝ) :
    (HCprime 1 θ).submatrix eqv12 eqv12 = HCp12 (cC θ) (sC θ) Complex.I := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.submatrix_apply, eqv12_0, eqv12_1, eqv12_2, eqv12_3, eqv12_4, eqv12_5,
      eqv12_6, eqv12_7, eqv12_8, eqv12_9, eqv12_10, eqv12_11,
      HCprime, connectionOperatorWithAxis, HCp12, Adj, EdgeB, edgeUnitaryWithAxis,
      fluxEdges_one,
      vIdx_one_00, vIdx_one_10, vIdx_one_01, vIdx_one_20, vIdx_one_11, vIdx_one_02,
      v00, v10, v01, v20, v11, v02,
      deg_mk00, deg_mk10, deg_mk01, deg_mk20, deg_mk11, deg_mk02,
      ne_0_1, ne_0_2, ne_0_3, ne_0_4, ne_0_5, ne_1_0, ne_1_2, ne_1_3, ne_1_4, ne_1_5, ne_2_0, ne_2_1, ne_2_3, ne_2_4, ne_2_5, ne_3_0, ne_3_1, ne_3_2, ne_3_4, ne_3_5, ne_4_0, ne_4_1, ne_4_2, ne_4_3, ne_4_5, ne_5_0, ne_5_1, ne_5_2, ne_5_3, ne_5_4,
      conj_cC, conj_sC, Complex.star_def, Complex.conj_I, map_neg, map_mul,
      rotZ, rotZh]
    <;> first
      | close_entry
      | (try ring)

/-- **Base case (PROOF.md §2).** -/
theorem traceDefect_one (θ : ℝ) :
    traceDefect 1 θ = -32 * ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2 := by
  rw [traceDefect_one_unfold, tr4_reindex eqv12 (HC 1 θ),
    tr4_reindex eqv12 (HCprime 1 θ), HC_sub, HCprime_sub]
  exact alg_base (cC θ) (sC θ) Complex.I Complex.I_sq

end EvgenyTheorem
