import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! SU(2) connection matrices and Pauli-matrix identities for the spectral-moment formalization. -/

namespace EvgenyTheorem

open Complex Matrix

abbrev C2 := Fin 2

def pauliX : Matrix C2 C2 ℂ :=
  !![0, 1; 1, 0]

def pauliY : Matrix C2 C2 ℂ :=
  !![0, -Complex.I; Complex.I, 0]

def pauliZ : Matrix C2 C2 ℂ :=
  !![1, 0; 0, -1]

noncomputable def connection (θ : ℝ) : Matrix C2 C2 ℂ :=
  !![Complex.exp (Complex.I * (θ / 2)), 0;
     0, Complex.exp (-Complex.I * (θ / 2))]

noncomputable def localTrace (θ : ℝ) : ℝ :=
  2 * Real.cos θ

theorem pauliX_sq : pauliX * pauliX = (1 : Matrix C2 C2 ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliY_sq : pauliY * pauliY = (1 : Matrix C2 C2 ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ_sq : pauliZ * pauliZ = (1 : Matrix C2 C2 ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem connection_diag (θ : ℝ) :
    connection θ 0 0 = Complex.exp (Complex.I * (θ / 2)) := by
  rfl

theorem connection_diag' (θ : ℝ) :
    connection θ 1 1 = Complex.exp (-Complex.I * (θ / 2)) := by
  rfl


noncomputable def su2Rotation (σ : Matrix C2 C2 ℂ) (θ : ℝ) : Matrix C2 C2 ℂ :=
  (Complex.ofReal (Real.cos (θ / 2))) • (1 : Matrix C2 C2 ℂ) -
    (Complex.I * Complex.ofReal (Real.sin (θ / 2))) • σ

theorem su2Rotation_z :
    su2Rotation pauliZ (-θ) = connection θ := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [su2Rotation, pauliZ, connection, Matrix.smul_apply]
    have harg : (-((θ : ℂ)) / 2) = -((θ : ℂ) / 2) := by ring
    rw [harg, Complex.cos_neg, Complex.sin_neg]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Complex.cos_add_sin_I ((θ : ℂ) / 2))
  · simp [su2Rotation, pauliZ, connection, Matrix.smul_apply]
  · simp [su2Rotation, pauliZ, connection, Matrix.smul_apply]
  · simp [su2Rotation, pauliZ, connection, Matrix.smul_apply]
    have harg : (-((θ : ℂ)) / 2) = -((θ : ℂ) / 2) := by ring
    rw [harg, Complex.cos_neg, Complex.sin_neg]
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
      (Complex.cos_sub_sin_I ((θ : ℂ) / 2))


theorem su2Rotation_inverse (σ : Matrix C2 C2 ℂ)
    (hσ : σ * σ = (1 : Matrix C2 C2 ℂ)) (θ : ℝ) :
    su2Rotation σ θ * su2Rotation σ (-θ) = (1 : Matrix C2 C2 ℂ) := by
  rw [su2Rotation, su2Rotation]
  have harg : (-θ) / 2 = -(θ / 2) := by ring
  rw [harg, Real.cos_neg, Real.sin_neg]
  simp only [Complex.ofReal_neg, mul_neg, neg_smul, sub_neg_eq_add]
  let c : ℂ := Complex.ofReal (Real.cos (θ / 2))
  let s : ℂ := Complex.ofReal (Real.sin (θ / 2))
  change (c • (1 : Matrix C2 C2 ℂ) - (Complex.I * s) • σ) *
      (c • (1 : Matrix C2 C2 ℂ) + (Complex.I * s) • σ) = 1
  simp only [sub_mul, mul_add, smul_mul, mul_smul, one_mul, mul_one]
  simp only [mul_smul_comm, smul_smul, mul_one]
  rw [hσ]
  ring_nf
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  rw [hI]
  dsimp [c, s]
  abel_nf
  simp only [one_smul, neg_smul, neg_neg, mul_one]
  ring_nf
  simp only [neg_smul, neg_neg]
  rw [← add_smul]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow]
  rw [← Complex.ofReal_add]
  have htrig :
      Real.cos (θ * (1 / 2)) ^ 2 + Real.sin (θ * (1 / 2)) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (θ * (1 / 2))]
  rw [htrig]
  norm_num



/-! ### Unitarity building blocks

`su2Rotation σ θ` is unitary for `σ ∈ {pauliX, pauliY, pauliZ}`: its
conjugate transpose equals `su2Rotation σ (-θ)`, which combined with
`su2Rotation_inverse` gives `U * Uᴴ = 1`. This is the operator-level fact
underlying `docs/EXACT_VERIFICATION.md` §3 and `docs/PROOF.md` §3 — every
edge matrix in the construction is unitary. -/

theorem su2Rotation_pauliX_conjTranspose (θ : ℝ) :
    (su2Rotation pauliX θ)ᴴ = su2Rotation pauliX (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Rotation, pauliX, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Complex.star_def, ← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal,
      map_ofNat, neg_div, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_neg] <;> ring

theorem su2Rotation_pauliY_conjTranspose (θ : ℝ) :
    (su2Rotation pauliY θ)ᴴ = su2Rotation pauliY (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Rotation, pauliY, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Complex.star_def, ← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal,
      map_ofNat, neg_div, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_neg] <;> ring

theorem su2Rotation_pauliZ_conjTranspose (θ : ℝ) :
    (su2Rotation pauliZ θ)ᴴ = su2Rotation pauliZ (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Rotation, pauliZ, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Complex.star_def, ← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal,
      map_ofNat, neg_div, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_neg] <;> ring

end EvgenyTheorem


