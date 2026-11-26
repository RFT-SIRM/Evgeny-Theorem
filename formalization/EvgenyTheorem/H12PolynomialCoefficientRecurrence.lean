import EvgenyTheorem.H12PolynomialTrace

namespace EvgenyTheorem

/-- Exponent vector for a polynomial in `c` and `s`. -/
abbrev H12Exponent := Fin 2 →₀ ℕ

/-- The coefficient matrices of a polynomial-valued matrix. -/
abbrev H12CoefficientFamily (ι : Type*) :=
  H12Exponent → Matrix ι ι ℂ

/-- Extract every `(c^a s^b)` coefficient from every matrix entry. -/
def h12CoefficientFamilyOf {ι : Type*}
    (M : Matrix ι ι H12ComplexPoly) : H12CoefficientFamily ι :=
  fun e i j => MvPolynomial.coeff e (M i j)

/-- Coefficient convolution corresponding to multiplication of two
polynomial-valued matrices. This definition uses only finite sums over the
matrix index and the exponent antidiagonal. -/
noncomputable def h12CoefficientConvolution {ι : Type*} [Fintype ι]
    (A B : H12CoefficientFamily ι) (e : H12Exponent) :
    Matrix ι ι ℂ :=
  fun i j =>
    ∑ k : ι, ∑ d ∈ Finset.antidiagonal e,
      A d.1 i k * B d.2 k j

/-- Taking coefficients commutes with polynomial-matrix multiplication. -/
theorem h12CoefficientFamily_mul {ι : Type*} [Fintype ι]
    (M N : Matrix ι ι H12ComplexPoly) (e : H12Exponent) :
    h12CoefficientFamilyOf (M * N) e =
      h12CoefficientConvolution
        (h12CoefficientFamilyOf M) (h12CoefficientFamilyOf N) e := by
  classical
  ext i j
  simp only [h12CoefficientFamilyOf, h12CoefficientConvolution,
    Matrix.mul_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_mul]

/-- Recursive coefficient-only representation of a matrix power. At each
step it convolves the previous coefficient matrices with the three-degree
(or, here, actual finite-degree) coefficient family of the base matrix. -/
noncomputable def h12CoefficientPower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι H12ComplexPoly) :
    ℕ → H12CoefficientFamily ι
  | 0 => fun e => if e = 0 then 1 else 0
  | n + 1 => fun e =>
      h12CoefficientConvolution
        (h12CoefficientPower M n) (h12CoefficientFamilyOf M) e

/-- The coefficient-only recursion is exactly the coefficient family of the
ordinary polynomial matrix power. No evaluation or noncomputable polynomial
normalization is used in this theorem. -/
theorem h12CoefficientPower_correct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι H12ComplexPoly) (n : ℕ) :
    h12CoefficientPower M n = h12CoefficientFamilyOf (M ^ n) := by
  classical
  induction n with
  | zero =>
      funext e
      ext i j
      by_cases he : e = 0
      · subst e
        by_cases hij : i = j
        · subst j
          simp [h12CoefficientPower, h12CoefficientFamilyOf,
            Matrix.one_apply, MvPolynomial.coeff_zero_one]
        · simp [h12CoefficientPower, h12CoefficientFamilyOf,
            Matrix.one_apply, hij]
      · by_cases hij : i = j
        · subst j
          simp [h12CoefficientPower, h12CoefficientFamilyOf,
            Matrix.one_apply, MvPolynomial.coeff_one, he, Ne.symm he]
        · simp [h12CoefficientPower, h12CoefficientFamilyOf,
            Matrix.one_apply, hij, he]
  | succ n ih =>
      funext e
      change h12CoefficientConvolution
        (h12CoefficientPower M n) (h12CoefficientFamilyOf M) e =
        h12CoefficientFamilyOf (M ^ (n + 1)) e
      rw [pow_succ, h12CoefficientFamily_mul]
      rw [← ih]

/-- Coefficients of the trace of a matrix power are the diagonal sum of the
coefficient-only power matrices. -/
theorem h12CoefficientTracePower_correct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι H12ComplexPoly) (n : ℕ) (e : H12Exponent) :
    MvPolynomial.coeff e (Matrix.trace (M ^ n)) =
      ∑ i : ι, h12CoefficientPower M n e i i := by
  classical
  calc
    MvPolynomial.coeff e (Matrix.trace (M ^ n)) =
        ∑ i : ι, h12CoefficientFamilyOf (M ^ n) e i i := by
      simp only [Matrix.trace, Matrix.diag_apply,
        MvPolynomial.coeff_sum, h12CoefficientFamilyOf]
    _ = ∑ i : ι, h12CoefficientPower M n e i i := by
      rw [← h12CoefficientPower_correct]

/-- The level-three face-axis trace coefficients are now exposed through the
finite coefficient recurrence. -/
theorem h12D3FaceTraceCoefficient (e : H12Exponent) :
    MvPolynomial.coeff e
      (Matrix.trace (h12PMatrix 3 faceAxis (oNum 3) ^ 12)) =
      ∑ i : Pt 3 × C2,
        h12CoefficientPower (h12PMatrix 3 faceAxis (oNum 3)) 12 e i i :=
  h12CoefficientTracePower_correct _ _ _

/-- The level-three constant-axis trace coefficients use the same recurrence. -/
theorem h12D3ConstantTraceCoefficient (e : H12Exponent) :
    MvPolynomial.coeff e
      (Matrix.trace (h12PMatrix 3 (fun _ => 2) (oNum 3) ^ 12)) =
      ∑ i : Pt 3 × C2,
        h12CoefficientPower (h12PMatrix 3 (fun _ => 2) (oNum 3)) 12 e i i :=
  h12CoefficientTracePower_correct _ _ _

end EvgenyTheorem
