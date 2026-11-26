import EvgenyTheorem.H12PolynomialTrace

namespace EvgenyTheorem

/-- Q₃ evaluated at c = cos(θ/2), s = sin(θ/2). -/
noncomputable def h12ComplexQ3 (θ : ℝ) : ℂ :=
  h12ComplexEval θ
    (MvPolynomial.map (Int.castRingHom ℂ) h12Q3)

/-- Q₁₂ evaluated at c = cos(θ/2), s = sin(θ/2). -/
noncomputable def h12ComplexQ12 (θ : ℝ) : ℂ :=
  h12ComplexEval θ
    (MvPolynomial.map (Int.castRingHom ℂ) h12Q12)

/-- A = Q₃ - Q₁₂ evaluated at c = cos(θ/2), s = sin(θ/2). -/
noncomputable def h12ComplexA (θ : ℝ) : ℂ :=
  h12ComplexEval θ
    (MvPolynomial.map (Int.castRingHom ℂ) h12A)

theorem h12ComplexA_eq_Q3_sub_Q12 (θ : ℝ) :
    h12ComplexA θ = h12ComplexQ3 θ - h12ComplexQ12 θ := by
  have hpoly : h12A = h12Q3 - h12Q12 := h12Q3_sub_Q12.symm
  simp [h12ComplexA, h12ComplexQ3, h12ComplexQ12, hpoly]

/--
Final H12 polynomial formula, assembled from exactly the two remaining
base identities: the explicit level-three defect and the explicit affine
residual constant. The all-level recurrence itself is the already-proved
`defectO12_num_affine_closed_form_from_level3_unconditional`.
-/
theorem defectO12_num_explicit_polynomial_from_level3
    (θ : ℝ) (n : ℕ)
    (hD3 :
      defectO12 3 θ faceAxis (fun _ => 2) (oNum 3) =
        32 * (Complex.ofReal (Real.sin (θ / 2))) ^ 2 * h12ComplexQ3 θ)
    (hC12 :
      defectO12_num_residual_constant θ =
        -64 * (Complex.ofReal (Real.sin (θ / 2))) ^ 2 * h12ComplexQ12 θ) :
    defectO12 (n + 3) θ faceAxis (fun _ => 2) (oNum (n + 3)) =
      32 * (Complex.ofReal (Real.sin (θ / 2))) ^ 2 *
        ((3 : ℂ) ^ n * h12ComplexA θ + h12ComplexQ12 θ) := by
  rw [defectO12_num_affine_closed_form_from_level3_unconditional θ n]
  rw [hD3, hC12, h12ComplexA_eq_Q3_sub_Q12]
  ring

/-- Equivalent Q₃/Q₁₂ form of the same all-level closed formula. -/
theorem defectO12_num_explicit_polynomial_Q3_Q12
    (θ : ℝ) (n : ℕ)
    (hD3 :
      defectO12 3 θ faceAxis (fun _ => 2) (oNum 3) =
        32 * (Complex.ofReal (Real.sin (θ / 2))) ^ 2 * h12ComplexQ3 θ)
    (hC12 :
      defectO12_num_residual_constant θ =
        -64 * (Complex.ofReal (Real.sin (θ / 2))) ^ 2 * h12ComplexQ12 θ) :
    defectO12 (n + 3) θ faceAxis (fun _ => 2) (oNum (n + 3)) =
      32 * (Complex.ofReal (Real.sin (θ / 2))) ^ 2 *
        ((3 : ℂ) ^ n * (h12ComplexQ3 θ - h12ComplexQ12 θ) +
          h12ComplexQ12 θ) := by
  rw [defectO12_num_explicit_polynomial_from_level3 θ n hD3 hC12]
  rw [h12ComplexA_eq_Q3_sub_Q12]

end EvgenyTheorem
