import EvgenyTheorem.H12PolynomialGaussianBridge
import EvgenyTheorem.H12PolynomialCoefficientRecurrence

namespace EvgenyTheorem

theorem h12GaussianCoeff_map
    (e : Fin 2 →₀ ℕ) (p : H12GaussianPoly) :
    MvPolynomial.coeff e (h12GaussianPolyToComplex p) =
      GaussianInt.toComplex (MvPolynomial.coeff e p) := by
  change MvPolynomial.coeff e
    (MvPolynomial.map GaussianInt.toComplex p) = _
  rw [MvPolynomial.coeff_map]

noncomputable def h12GaussianPMatrixFor
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    Matrix H12GaussianIndex3 H12GaussianIndex3 H12GaussianPoly :=
  fun x y => h12GaussianPHeO 3 ax o x.1.1 y.1.1 x.2 y.2

theorem h12GaussianPMatrixFor_map
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    (h12GaussianPMatrixFor ax o).map h12GaussianPolyToComplex =
      h12PMatrix 3 ax o := by
  apply Matrix.ext
  intro x y
  change h12GaussianPolyToComplex
    (h12GaussianPHeO 3 ax o x.1.1 y.1.1 x.2 y.2) =
      h12PHeO 3 ax o x.1.1 y.1.1 x.2 y.2
  exact h12GaussianPHeO_map 3 ax o x.1.1 y.1.1 x.2 y.2

theorem h12GaussianPMatrixFor_pow_map
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (n : ℕ) :
    (h12GaussianPMatrixFor ax o ^ n).map h12GaussianPolyToComplex =
      (h12PMatrix 3 ax o) ^ n := by
  induction n with
  | zero =>
      apply Matrix.ext
      intro x y
      have hmap1 :
          h12GaussianPolyToComplex (1 : H12GaussianPoly) = 1 :=
        h12GaussianPolyToComplex.map_one
      have hmap0 :
          h12GaussianPolyToComplex (0 : H12GaussianPoly) = 0 :=
        h12GaussianPolyToComplex.map_zero
      by_cases hxy : x = y
      · subst y
        simp [Matrix.one_apply, hmap1]
      · simp [Matrix.one_apply, hxy, hmap0]
  | succ n ih =>
      rw [pow_succ, pow_succ]
      apply Matrix.ext
      intro x y
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro z hz
      have hpow :
          h12GaussianPolyToComplex
              ((h12GaussianPMatrixFor ax o ^ n) x z) =
            ((h12PMatrix 3 ax o) ^ n) x z := by
        have h := congrArg
          (fun M :
            Matrix H12GaussianIndex3 H12GaussianIndex3 H12ComplexPoly =>
              M x z) ih
        simpa only [Matrix.map_apply] using h
      have hop :
          h12GaussianPolyToComplex
              (h12GaussianPMatrixFor ax o z y) =
            h12PMatrix 3 ax o z y := by
        have h := congrArg
          (fun M :
            Matrix H12GaussianIndex3 H12GaussianIndex3 H12ComplexPoly =>
              M z y) (h12GaussianPMatrixFor_map ax o)
        simpa only [Matrix.map_apply] using h
      rw [hpow, hop]


theorem h12GaussianTraceCoefficientToComplex
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (n : ℕ) (e : H12Exponent) :
    GaussianInt.toComplex
        (MvPolynomial.coeff e
          (Matrix.trace (h12GaussianPMatrixFor ax o ^ n))) =
      MvPolynomial.coeff e
        (Matrix.trace ((h12PMatrix 3 ax o) ^ n)) := by
  classical
  have htrace :
      h12GaussianPolyToComplex
          (Matrix.trace (h12GaussianPMatrixFor ax o ^ n)) =
        Matrix.trace ((h12PMatrix 3 ax o) ^ n) := by
    simp only [Matrix.trace, Matrix.diag_apply, map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have h := congrArg
      (fun M :
        Matrix H12GaussianIndex3 H12GaussianIndex3 H12ComplexPoly =>
          M x x) (h12GaussianPMatrixFor_pow_map ax o n)
    simpa only [Matrix.map_apply] using h
  calc
    GaussianInt.toComplex
        (MvPolynomial.coeff e
          (Matrix.trace (h12GaussianPMatrixFor ax o ^ n))) =
        MvPolynomial.coeff e
          (h12GaussianPolyToComplex
            (Matrix.trace (h12GaussianPMatrixFor ax o ^ n))) := by
      exact (h12GaussianCoeff_map e _).symm
    _ = MvPolynomial.coeff e
          (Matrix.trace ((h12PMatrix 3 ax o) ^ n)) := by
      rw [htrace]

theorem h12GaussianTraceCoefficientToRecurrence
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (n : ℕ) (e : H12Exponent) :
    GaussianInt.toComplex
        (MvPolynomial.coeff e
          (Matrix.trace (h12GaussianPMatrixFor ax o ^ n))) =
      ∑ i : H12GaussianIndex3,
        h12CoefficientPower (h12PMatrix 3 ax o) n e i i := by
  rw [h12GaussianTraceCoefficientToComplex]
  exact h12CoefficientTracePower_correct _ _ _

end EvgenyTheorem
