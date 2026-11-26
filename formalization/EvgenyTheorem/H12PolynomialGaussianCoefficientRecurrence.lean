import EvgenyTheorem.H12PolynomialGaussianCoefficientMap

namespace EvgenyTheorem

abbrev H12GaussianCoefficientFamily :=
  H12Exponent →
    Matrix H12GaussianIndex3 H12GaussianIndex3 GaussianInt

def h12GaussianCoefficientFamilyOf
    (M : Matrix H12GaussianIndex3 H12GaussianIndex3 H12GaussianPoly) :
    H12GaussianCoefficientFamily :=
  fun e i j => MvPolynomial.coeff e (M i j)

noncomputable def h12GaussianCoefficientConvolution
    (A B : H12GaussianCoefficientFamily) (e : H12Exponent) :
    Matrix H12GaussianIndex3 H12GaussianIndex3 GaussianInt :=
  fun i j =>
    ∑ k : H12GaussianIndex3, ∑ d ∈ Finset.antidiagonal e,
      A d.1 i k * B d.2 k j

theorem h12GaussianCoefficientFamily_mul
    (M N :
      Matrix H12GaussianIndex3 H12GaussianIndex3 H12GaussianPoly)
    (e : H12Exponent) :
    h12GaussianCoefficientFamilyOf (M * N) e =
      h12GaussianCoefficientConvolution
        (h12GaussianCoefficientFamilyOf M)
        (h12GaussianCoefficientFamilyOf N) e := by
  classical
  apply Matrix.ext
  intro i j
  simp only [h12GaussianCoefficientFamilyOf,
    h12GaussianCoefficientConvolution,
    Matrix.mul_apply, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_mul]

noncomputable def h12GaussianCoefficientPower
    (M : Matrix H12GaussianIndex3 H12GaussianIndex3 H12GaussianPoly) :
    ℕ → H12GaussianCoefficientFamily
  | 0 => fun e => if e = 0 then 1 else 0
  | n + 1 => fun e =>
      h12GaussianCoefficientConvolution
        (h12GaussianCoefficientPower M n)
        (h12GaussianCoefficientFamilyOf M) e

theorem h12GaussianCoefficientPower_correct
    (M : Matrix H12GaussianIndex3 H12GaussianIndex3 H12GaussianPoly)
    (n : ℕ) :
    h12GaussianCoefficientPower M n =
      h12GaussianCoefficientFamilyOf (M ^ n) := by
  classical
  induction n with
  | zero =>
      funext e
      apply Matrix.ext
      intro i j
      by_cases he : e = 0
      · subst e
        by_cases hij : i = j
        · subst j
          simp [h12GaussianCoefficientPower,
            h12GaussianCoefficientFamilyOf,
            MvPolynomial.coeff_zero_one]
        · simp [h12GaussianCoefficientPower,
            h12GaussianCoefficientFamilyOf, hij]
      · by_cases hij : i = j
        · subst j
          simp [h12GaussianCoefficientPower,
            h12GaussianCoefficientFamilyOf,
            MvPolynomial.coeff_one, he, Ne.symm he]
        · simp [h12GaussianCoefficientPower,
            h12GaussianCoefficientFamilyOf, hij, he]
  | succ n ih =>
      funext e
      change h12GaussianCoefficientConvolution
        (h12GaussianCoefficientPower M n)
        (h12GaussianCoefficientFamilyOf M) e =
        h12GaussianCoefficientFamilyOf (M ^ (n + 1)) e
      rw [pow_succ, h12GaussianCoefficientFamily_mul]
      rw [← ih]

theorem h12GaussianCoefficientTracePower_correct
    (M : Matrix H12GaussianIndex3 H12GaussianIndex3 H12GaussianPoly)
    (n : ℕ) (e : H12Exponent) :
    MvPolynomial.coeff e (Matrix.trace (M ^ n)) =
      ∑ i : H12GaussianIndex3,
        h12GaussianCoefficientPower M n e i i := by
  classical
  calc
    MvPolynomial.coeff e (Matrix.trace (M ^ n)) =
        ∑ i : H12GaussianIndex3,
          h12GaussianCoefficientFamilyOf (M ^ n) e i i := by
      simp only [Matrix.trace, Matrix.diag_apply,
        MvPolynomial.coeff_sum, h12GaussianCoefficientFamilyOf]
    _ = ∑ i : H12GaussianIndex3,
          h12GaussianCoefficientPower M n e i i := by
      rw [← h12GaussianCoefficientPower_correct]

theorem h12GaussianD3FaceTraceCoefficient (e : H12Exponent) :
    MvPolynomial.coeff e
      (Matrix.trace
        (h12GaussianPMatrixFor faceAxis (oNum 3) ^ 12)) =
      ∑ i : H12GaussianIndex3,
        h12GaussianCoefficientPower
          (h12GaussianPMatrixFor faceAxis (oNum 3)) 12 e i i :=
  h12GaussianCoefficientTracePower_correct _ _ _

theorem h12GaussianD3ConstantTraceCoefficient (e : H12Exponent) :
    MvPolynomial.coeff e
      (Matrix.trace
        (h12GaussianPMatrixFor (fun _ => 2) (oNum 3) ^ 12)) =
      ∑ i : H12GaussianIndex3,
        h12GaussianCoefficientPower
          (h12GaussianPMatrixFor (fun _ => 2) (oNum 3)) 12 e i i :=
  h12GaussianCoefficientTracePower_correct _ _ _

end EvgenyTheorem
