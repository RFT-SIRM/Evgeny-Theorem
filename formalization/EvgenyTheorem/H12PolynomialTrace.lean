import EvgenyTheorem.H12PolynomialOperator
import EvgenyTheorem.H12PolynomialBridge

namespace EvgenyTheorem

/-- Polynomial matrix representing the orientation-parametrized operator. -/
noncomputable def h12PMatrix
    (m : ℕ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    Matrix (Pt m × C2) (Pt m × C2) H12ComplexPoly :=
  fun x y => h12PHeO m ax o x.1.1 y.1.1 x.2 y.2

/-- Evaluation of the polynomial operator gives the original operator. -/
theorem h12_eval_pMatrix
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    (h12PMatrix m ax o).map (h12ComplexEval θ) =
      pOpO m θ ax o := by
  ext x y
  exact h12_eval_pHeO m θ ax o
    x.1.1 y.1.1 x.2 y.2

/-- Evaluation commutes with every natural power of the operator. -/
theorem h12_eval_pMatrix_pow
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (n : ℕ) :
    (h12PMatrix m ax o ^ n).map (h12ComplexEval θ) =
      pOpO m θ ax o ^ n := by
  induction n with
  | zero =>
      simp [h12PMatrix]
  | succ n ih =>
      rw [pow_succ, pow_succ]
      ext x y
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro z hz
      have hpow :
          h12ComplexEval θ ((h12PMatrix m ax o ^ n) x z) =
            (pOpO m θ ax o ^ n) x z := by
        have h := congrArg
          (fun M : Matrix (Pt m × C2) (Pt m × C2) ℂ => M x z) ih
        simpa only [Matrix.map_apply] using h
      have hop :
          h12ComplexEval θ (h12PMatrix m ax o z y) =
            pOpO m θ ax o z y := by
        have h := congrArg
          (fun M : Matrix (Pt m × C2) (Pt m × C2) ℂ => M z y)
          (h12_eval_pMatrix m θ ax o)
        simpa only [Matrix.map_apply] using h
      rw [hpow, hop]

/-- Evaluation commutes with the trace of every operator power. -/
theorem h12_eval_trace_pMatrix_pow
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (n : ℕ) :
    h12ComplexEval θ (Matrix.trace (h12PMatrix m ax o ^ n)) =
      Matrix.trace (pOpO m θ ax o ^ n) := by
  classical
  simp only [Matrix.trace, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have h := congrArg
    (fun M : Matrix (Pt m × C2) (Pt m × C2) ℂ => M x x)
    (h12_eval_pMatrix_pow m θ ax o n)
  simpa [Matrix.map_apply] using h

/-- Exact polynomial representation of the level-three H12 defect. -/
noncomputable def h12D3TracePolynomial : H12ComplexPoly :=
  Matrix.trace (h12PMatrix 3 faceAxis (oNum 3) ^ 12) -
  Matrix.trace (h12PMatrix 3 (fun _ => 2) (oNum 3) ^ 12)

/-- The evaluated level-three polynomial trace is exactly D_3. -/
theorem h12_eval_D3TracePolynomial (θ : ℝ) :
    h12ComplexEval θ h12D3TracePolynomial =
      defectO12 3 θ faceAxis (fun _ => 2) (oNum 3) := by
  simp only [h12D3TracePolynomial, map_sub, defectO12]
  rw [h12_eval_trace_pMatrix_pow, h12_eval_trace_pMatrix_pow]

end EvgenyTheorem
