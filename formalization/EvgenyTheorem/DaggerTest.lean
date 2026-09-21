import EvgenyTheorem.Operator

namespace EvgenyTheorem

theorem su2Rotation_dagger
    (σ : Matrix C2 C2 ℂ) (hσ : Matrix.conjTranspose σ = σ) (θ : ℝ) :
    Matrix.conjTranspose (su2Rotation σ θ) = su2Rotation σ (-θ) := by
  simp [su2Rotation, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hσ]
  rw [← Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  ring

end EvgenyTheorem
