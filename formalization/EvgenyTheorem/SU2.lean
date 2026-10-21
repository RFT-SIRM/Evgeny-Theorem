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



namespace EvgenyTheorem

/-- A Hermitian matrix in quaternionic SU(2) block form has zero
off-diagonal entry. This is an algebraic helper for the corner-spin
argument; it does not assert that concrete powers satisfy the form. -/
theorem quaternionForm_hermitian_offdiag_zero
    {M : Matrix C2 C2 ℂ}
    (hform : M (1 : C2) (0 : C2) = - star (M (0 : C2) (1 : C2)))
    (hH : Matrix.conjTranspose M = M) :
    M (0 : C2) (1 : C2) = 0 := by
  have h := congrFun (congrFun hH (0 : C2)) (1 : C2)
  have h01 : star (M (1 : C2) (0 : C2)) = M (0 : C2) (1 : C2) := by
    simpa [Matrix.conjTranspose_apply] using h
  rw [hform] at h01
  simp only [star_neg, star_star] at h01
  have hz : M (0 : C2) (1 : C2) + M (0 : C2) (1 : C2) = 0 := by
    calc
      M (0 : C2) (1 : C2) + M (0 : C2) (1 : C2) =
          (-M (0 : C2) (1 : C2)) + M (0 : C2) (1 : C2) :=
        congrArg (fun z : ℂ => z + M (0 : C2) (1 : C2)) h01.symm
      _ = 0 := neg_add_cancel _
  have hzero : (2 : ℂ) * M (0 : C2) (1 : C2) = 0 := by
    calc
      (2 : ℂ) * M (0 : C2) (1 : C2) =
          M (0 : C2) (1 : C2) + M (0 : C2) (1 : C2) := by ring
      _ = 0 := hz
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
end EvgenyTheorem

namespace EvgenyTheorem

/-- Quaternionic SU(2) block form: the lower-left entry is minus the
conjugate of the upper-right entry, and the diagonal entries are conjugates. -/
def SU2QuaternionForm (M : Matrix C2 C2 ℂ) : Prop :=
  M (1 : C2) (0 : C2) = - star (M (0 : C2) (1 : C2)) ∧
  M (1 : C2) (1 : C2) = star (M (0 : C2) (0 : C2))

theorem SU2QuaternionForm_zero : SU2QuaternionForm (0 : Matrix C2 C2 ℂ) := by
  constructor <;> simp [SU2QuaternionForm]

theorem SU2QuaternionForm_one : SU2QuaternionForm (1 : Matrix C2 C2 ℂ) := by
  constructor <;> simp [SU2QuaternionForm, Matrix.one_apply]

theorem SU2QuaternionForm_smul_one {c : ℂ} (hc : star c = c) :
    SU2QuaternionForm (c • (1 : Matrix C2 C2 ℂ)) := by
  constructor <;> simp [SU2QuaternionForm, Matrix.smul_apply, Matrix.one_apply, hc]

theorem SU2QuaternionForm_neg {M : Matrix C2 C2 ℂ}
    (hM : SU2QuaternionForm M) : SU2QuaternionForm (-M) := by
  rcases hM with ⟨h01, h00⟩
  constructor <;> simp [SU2QuaternionForm, h01, h00, star_neg, Matrix.neg_apply]

/-- Quaternionic block form is closed under addition. -/
theorem SU2QuaternionForm_add {A B : Matrix C2 C2 ℂ}
    (hA : SU2QuaternionForm A) (hB : SU2QuaternionForm B) :
    SU2QuaternionForm (A + B) := by
  rcases hA with ⟨hA01, hA00⟩
  rcases hB with ⟨hB01, hB00⟩
  constructor <;>
    simp [SU2QuaternionForm, Matrix.add_apply, hA01, hA00,
      hB01, hB00, star_add] <;> ring

/-- Quaternionic block form is preserved by conjugate transpose. -/
theorem SU2QuaternionForm_conjTranspose {M : Matrix C2 C2 ℂ}
    (hM : SU2QuaternionForm M) :
    SU2QuaternionForm (Matrix.conjTranspose M) := by
  rcases hM with ⟨h01, h00⟩
  constructor <;>
    simp [SU2QuaternionForm, Matrix.conjTranspose_apply,
      h01, h00, star_neg, star_star]

theorem SU2QuaternionForm_mul {A B : Matrix C2 C2 ℂ}
    (hA : SU2QuaternionForm A) (hB : SU2QuaternionForm B) :
    SU2QuaternionForm (A * B) := by
  rcases hA with ⟨ha01, ha00⟩
  rcases hB with ⟨hb01, hb00⟩
  constructor <;>
    simp [SU2QuaternionForm, Matrix.mul_apply, Fin.sum_univ_two,
      ha01, ha00, hb01, hb00, star_mul, star_neg, star_star] <;> ring


/-- The Pauli-X rotation has the quaternionic 2×2 block form. -/
theorem su2Rotation_pauliX_quaternionForm (θ : ℝ) :
    SU2QuaternionForm (su2Rotation pauliX θ) := by
  constructor <;>
    simp [SU2QuaternionForm, su2Rotation, pauliX, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply, Complex.star_def,
      ← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal,
      map_ofNat, neg_div, Complex.cos_neg, Complex.sin_neg,
      Complex.ofReal_neg] <;> ring



/-- Every natural power preserves the quaternionic SU(2) block form. -/
theorem SU2QuaternionForm_pow {M : Matrix C2 C2 ℂ}
    (hM : SU2QuaternionForm M) (n : ℕ) :
    SU2QuaternionForm (M ^ n) := by
  induction n with
  | zero =>
      simpa using SU2QuaternionForm_one
  | succ n ih =>
      rw [pow_succ]
      exact SU2QuaternionForm_mul ih hM


/-- The Pauli-Y rotation has the quaternionic 2×2 block form. -/
theorem su2Rotation_pauliY_quaternionForm (θ : ℝ) :
    SU2QuaternionForm (su2Rotation pauliY θ) := by
  constructor <;>
    simp [SU2QuaternionForm, su2Rotation, pauliY, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply, Complex.star_def,
      ← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal,
      map_ofNat, neg_div, Complex.cos_neg, Complex.sin_neg,
      Complex.ofReal_neg] <;> ring


/-- The Pauli-Z rotation has the quaternionic 2×2 block form. -/
theorem su2Rotation_pauliZ_quaternionForm (θ : ℝ) :
    SU2QuaternionForm (su2Rotation pauliZ θ) := by
  constructor <;>
    simp [SU2QuaternionForm, su2Rotation, pauliZ, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply, Complex.star_def,
      ← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal,
      map_ofNat, neg_div, Complex.cos_neg, Complex.sin_neg,
      Complex.ofReal_neg] <;> ring


/-- Finite sums preserve quaternionic spin-block form. This is the algebraic
closure step needed when a block of a matrix product is expanded over its
intermediate geometric vertices. -/
theorem SU2QuaternionForm_sum_finset {ι : Type*} (s : Finset ι)
    (f : ι → Matrix C2 C2 ℂ)
    (hf : ∀ i ∈ s, SU2QuaternionForm (f i)) :
    SU2QuaternionForm (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using SU2QuaternionForm_zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply SU2QuaternionForm_add
      · exact hf a (Finset.mem_insert_self a s)
      · apply ih
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)


/-- A finite sum of products preserves quaternionic spin-block form when
both factors in every summand have that form. This packages the closure step
used when expanding a block of a matrix product over intermediate vertices. -/
theorem SU2QuaternionForm_sum_mul {ι : Type*} (s : Finset ι)
    (A B : ι → Matrix C2 C2 ℂ)
    (hA : ∀ i ∈ s, SU2QuaternionForm (A i))
    (hB : ∀ i ∈ s, SU2QuaternionForm (B i)) :
    SU2QuaternionForm (∑ i ∈ s, A i * B i) := by
  apply SU2QuaternionForm_sum_finset
  intro i hi
  exact SU2QuaternionForm_mul (hA i hi) (hB i hi)


/-- Extract the 2×2 spin block at geometric indices p and q from a matrix
whose state space is a product of geometric vertices and spin indices. -/
def spinBlock {X : Type*} (M : Matrix (X × C2) (X × C2) ℂ) (p q : X) :
    Matrix C2 C2 ℂ :=
  fun i j => M (p, i) (q, j)

/-- The spin block of a product is the sum over intermediate geometric vertices
of the products of the corresponding spin blocks. The spin index remains inside
each 2×2 matrix product, so no matrix factors are reordered. -/
theorem spinBlock_mul {X : Type*} [Fintype X]
    (A B : Matrix (X × C2) (X × C2) ℂ) (p q : X) :
    spinBlock (A * B) p q = ∑ x : X, spinBlock A p x * spinBlock B x q := by
  classical
  ext i j
  simp [spinBlock, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.sum_apply]

/-- If every geometric spin block of M has quaternionic form, then the same is
true for every geometric spin block of every natural power of M. This is the
power-closure lemma needed before using Hermiticity to cancel same-coordinate,
different-spin corner entries. -/
theorem spinBlock_pow_quaternionForm {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix (X × C2) (X × C2) ℂ)
    (hM : ∀ p q, SU2QuaternionForm (spinBlock M p q)) :
    ∀ n p q, SU2QuaternionForm (spinBlock (M ^ n) p q) := by
  intro n
  induction n with
  | zero =>
      intro p q
      by_cases hpq : p = q
      · subst q
        have hblock :
            spinBlock (1 : Matrix (X × C2) (X × C2) ℂ) p p =
              (1 : Matrix C2 C2 ℂ) := by
          ext i j
          simp [spinBlock, Matrix.one_apply, Prod.ext_iff]
        simp only [pow_zero]
        rw [hblock]
        exact SU2QuaternionForm_one
      · have hblock :
            spinBlock (1 : Matrix (X × C2) (X × C2) ℂ) p q =
              (0 : Matrix C2 C2 ℂ) := by
          ext i j
          simp [spinBlock, Matrix.one_apply, Prod.ext_iff, hpq]
        simp only [pow_zero]
        rw [hblock]
        exact SU2QuaternionForm_zero
  | succ n ih =>
      intro p q
      rw [pow_succ, spinBlock_mul]
      apply SU2QuaternionForm_sum_finset (s := Finset.univ)
      intro x hx
      exact SU2QuaternionForm_mul (ih p x) (hM x q)


end EvgenyTheorem

