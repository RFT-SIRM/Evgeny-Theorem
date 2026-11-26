import EvgenyTheorem.H12PolynomialBridge
import Mathlib.Algebra.MvPolynomial.Basic

namespace EvgenyTheorem

abbrev H12Poly := MvPolynomial (Fin 2) ℤ

/-- Formal variables c and s, in that order. -/
noncomputable def h12c : H12Poly := MvPolynomial.X 0
noncomputable def h12s : H12Poly := MvPolynomial.X 1

/-- Exact level-three polynomial Q₃(c,s). -/
noncomputable def h12Q3 : H12Poly :=
    -12 * h12c ^ 6
  + 24 * h12c ^ 5 * h12s
  + 1032 * h12c ^ 5
  - 2040 * h12c ^ 4 * h12s
  - 80120 * h12c ^ 4
  + 42894 * h12c ^ 3 * h12s
  + 2400282 * h12c ^ 3
  - 67494 * h12c ^ 2 * h12s
  - 30361019 * h12c ^ 2
  - 2479593 * h12c * h12s
  + 275590614 * h12c
  + 3481440 * h12s
  - 566815997

/-- Exact residual polynomial Q₁₂(c,s). -/
noncomputable def h12Q12 : H12Poly :=
    6 * h12c ^ 6
  + 6 * h12c ^ 5 * h12s
  + 240 * h12c ^ 5
  - 456 * h12c ^ 4 * h12s
  - 8858 * h12c ^ 4
  + 2466 * h12c ^ 3 * h12s
  - 33138 * h12c ^ 3
  + 618 * h12c ^ 2 * h12s
  + 1612501 * h12c ^ 2
  + 571254 * h12c * h12s
  - 18512844 * h12c
  - 3259668 * h12s
  + 13167067

/-- The affine-growth coefficient A(c,s) = Q₃(c,s) - Q₁₂(c,s). -/
noncomputable def h12A : H12Poly :=
    -18 * h12c ^ 6
  + 18 * h12c ^ 5 * h12s
  + 792 * h12c ^ 5
  - 1584 * h12c ^ 4 * h12s
  - 71262 * h12c ^ 4
  + 40428 * h12c ^ 3 * h12s
  + 2433420 * h12c ^ 3
  - 68112 * h12c ^ 2 * h12s
  - 31973520 * h12c ^ 2
  - 3050847 * h12c * h12s
  + 294103458 * h12c
  + 6741108 * h12s
  - 579983064

/-- Lean verifies every coefficient of Q₃ - Q₁₂ = A exactly. -/
theorem h12Q3_sub_Q12 :
    h12Q3 - h12Q12 = h12A := by
  unfold h12Q3 h12Q12 h12A h12c h12s
  ring

/-- The affine closed form has the equivalent Q₃/Q₁₂ and A/Q₁₂
presentations, for every natural exponent. -/
theorem h12_affine_polynomial_form (n : ℕ) :
    (3 : H12Poly) ^ n * h12Q3 -
        ((3 : H12Poly) ^ n - 1) * h12Q12 =
      (3 : H12Poly) ^ n * h12A + h12Q12 := by
  rw [← h12Q3_sub_Q12]
  ring

/-- The common factor 32 s² preserves the exact affine identity. -/
theorem h12_scaled_affine_polynomial_form (n : ℕ) :
    32 * h12s ^ 2 *
        ((3 : H12Poly) ^ n * h12Q3 -
          ((3 : H12Poly) ^ n - 1) * h12Q12) =
      32 * h12s ^ 2 *
        ((3 : H12Poly) ^ n * h12A + h12Q12) := by
  rw [h12_affine_polynomial_form]

end EvgenyTheorem
