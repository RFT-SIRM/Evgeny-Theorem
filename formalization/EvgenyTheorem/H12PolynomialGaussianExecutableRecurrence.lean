import EvgenyTheorem.H12PolynomialGaussianAffineRecurrence

namespace EvgenyTheorem

/-- Computable predecessor of an exponent in one coordinate.
It does not use Finsupp.single or Finsupp subtraction. -/
def h12GaussianExponentPredExec
    (e : H12Exponent) (j : Fin 2) : H12Exponent where
  support := e.support.filter
    (fun i => if i = j then 1 < e i else 0 < e i)
  toFun := fun i => if i = j then e i - 1 else e i
  mem_support_toFun := by
    intro i
    by_cases hij : i = j
    · subst i
      simp only [Finset.mem_filter, if_pos]
      rw [Finsupp.mem_support_iff]
      constructor
      · rintro ⟨_, hlt⟩
        omega
      · intro hne
        constructor <;> omega
    · simp [Finset.mem_filter, hij, Finsupp.mem_support_iff]
      omega

theorem h12GaussianExponentPredExec_eq_sub
    (e : H12Exponent) (j : Fin 2) :
    h12GaussianExponentPredExec e j =
      e - Finsupp.single j 1 := by
  classical
  ext i
  by_cases hij : i = j
  · subst i
    simp [h12GaussianExponentPredExec]
  · simp [h12GaussianExponentPredExec, hij]

theorem h12GaussianSingleLeExponentExec_iff
    (e : H12Exponent) (j : Fin 2) :
    Finsupp.single j 1 ≤ e ↔ 0 < e j := by
  classical
  constructor
  · intro h
    have hj : 1 ≤ e j := by simpa using h j
    exact Nat.succ_le_iff.mp hj
  · intro h i
    by_cases hij : i = j
    · subst i
      simpa using (Nat.succ_le_iff.mpr h)
    · simp [hij]

/-- Executable version of the three-term affine convolution. -/
def h12GaussianAffineCoefficientConvolutionExec
    (A : H12GaussianCoefficientFamily)
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (e : H12Exponent) :
    Matrix H12GaussianIndex3 H12GaussianIndex3 GaussianInt :=
  fun i j =>
    ∑ k : H12GaussianIndex3,
      (A e i k * h12GaussianP0Matrix k j +
        (if 0 < e (0 : Fin 2) then
          A (h12GaussianExponentPredExec e 0) i k *
            h12GaussianPcMatrix k j else 0) +
        (if 0 < e (1 : Fin 2) then
          A (h12GaussianExponentPredExec e 1) i k *
            h12GaussianPsMatrixFor ax o k j else 0))

theorem h12GaussianAffineCoefficientConvolutionExec_correct
    (A : H12GaussianCoefficientFamily)
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (e : H12Exponent) :
    h12GaussianAffineCoefficientConvolutionExec A ax o e =
      h12GaussianAffineCoefficientConvolution A ax o e := by
  classical
  apply Matrix.ext
  intro i j
  simp only [h12GaussianAffineCoefficientConvolutionExec,
    h12GaussianAffineCoefficientConvolution,
    h12GaussianExponentPredExec_eq_sub,
    ← h12GaussianSingleLeExponentExec_iff]

/-- Executable coefficient-power recurrence.
The zero exponent test uses its two coordinates, not Finsupp equality. -/
def h12GaussianAffineCoefficientPowerExec
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    ℕ → H12GaussianCoefficientFamily
  | 0 => fun e =>
      if e (0 : Fin 2) = 0 ∧ e (1 : Fin 2) = 0 then 1 else 0
  | n + 1 => fun e =>
      h12GaussianAffineCoefficientConvolutionExec
        (h12GaussianAffineCoefficientPowerExec ax o n) ax o e

theorem h12GaussianAffineCoefficientPowerExec_correct
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (n : ℕ) :
    h12GaussianAffineCoefficientPowerExec ax o n =
      h12GaussianAffineCoefficientPower ax o n := by
  classical
  induction n with
  | zero =>
      funext e
      by_cases he : e = 0
      · subst e
        simp [h12GaussianAffineCoefficientPowerExec,
          h12GaussianAffineCoefficientPower]
      · have hcoord :
            ¬ (e (0 : Fin 2) = 0 ∧ e (1 : Fin 2) = 0) := by
          intro h
          apply he
          ext i
          fin_cases i
          · exact h.1
          · exact h.2
        simp [h12GaussianAffineCoefficientPowerExec,
          h12GaussianAffineCoefficientPower, he, hcoord]
  | succ n ih =>
      funext e
      change h12GaussianAffineCoefficientConvolutionExec
          (h12GaussianAffineCoefficientPowerExec ax o n) ax o e =
        h12GaussianAffineCoefficientConvolution
          (h12GaussianAffineCoefficientPower ax o n) ax o e
      rw [h12GaussianAffineCoefficientConvolutionExec_correct]
      rw [ih]

/-- The exponent of s², constructed without Finsupp.single. -/
def h12GaussianExponentS2Exec : H12Exponent where
  support := {1}
  toFun := fun i => if i = 1 then 2 else 0
  mem_support_toFun := by
    intro i
    fin_cases i <;> simp

/-- The executable level-three coefficient of c⁰s² in the D₃ trace difference. -/
def h12GaussianD3S2CoefficientExec : GaussianInt :=
  (∑ i : H12GaussianIndex3,
    h12GaussianAffineCoefficientPowerExec
      faceAxis (oNum 3) 12 h12GaussianExponentS2Exec i i) -
  (∑ i : H12GaussianIndex3,
    h12GaussianAffineCoefficientPowerExec
      (fun _ => 2) (oNum 3) 12 h12GaussianExponentS2Exec i i)

theorem h12GaussianAffineTraceCoefficientExec_correct
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (n : ℕ) (e : H12Exponent) :
    (∑ i : H12GaussianIndex3,
      h12GaussianAffineCoefficientPowerExec ax o n e i i) =
      MvPolynomial.coeff e
        (Matrix.trace (h12GaussianPMatrixFor ax o ^ n)) := by
  classical
  have hpow :
      h12GaussianAffineCoefficientPowerExec ax o n =
        h12GaussianCoefficientPower (h12GaussianPMatrixFor ax o) n :=
    (h12GaussianAffineCoefficientPowerExec_correct ax o n).trans
      ((h12GaussianAffineCoefficientPower_correct ax o n).trans
        (h12GaussianCoefficientPower_correct
          (h12GaussianPMatrixFor ax o) n).symm)
  calc
    (∑ i : H12GaussianIndex3,
      h12GaussianAffineCoefficientPowerExec ax o n e i i) =
      ∑ i : H12GaussianIndex3,
        h12GaussianCoefficientPower
          (h12GaussianPMatrixFor ax o) n e i i := by
            apply Finset.sum_congr rfl
            intro i hi
            exact congrArg
              (fun F : H12GaussianCoefficientFamily => F e i i) hpow
    _ = MvPolynomial.coeff e
        (Matrix.trace (h12GaussianPMatrixFor ax o ^ n)) :=
      (h12GaussianCoefficientTracePower_correct
        (h12GaussianPMatrixFor ax o) n e).symm

theorem h12GaussianD3S2CoefficientExec_eq_trace_coeff :
    h12GaussianD3S2CoefficientExec =
      MvPolynomial.coeff h12GaussianExponentS2Exec
        (Matrix.trace
          (h12GaussianPMatrixFor faceAxis (oNum 3) ^ 12)) -
      MvPolynomial.coeff h12GaussianExponentS2Exec
        (Matrix.trace
          (h12GaussianPMatrixFor (fun _ => 2) (oNum 3) ^ 12)) := by
  unfold h12GaussianD3S2CoefficientExec
  rw [h12GaussianAffineTraceCoefficientExec_correct,
    h12GaussianAffineTraceCoefficientExec_correct]


end EvgenyTheorem

