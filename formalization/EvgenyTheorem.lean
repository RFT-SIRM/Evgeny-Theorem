import EvgenyTheorem.Graph.Sierpinski
import EvgenyTheorem.SU2
import Mathlib

namespace EvgenyTheorem

/-- Raw fourth-moment trace defect from the project statement. -/
noncomputable def delta (m : ℕ) (θ : ℝ) : ℝ :=
  -16 * ((3 : ℝ) ^ (m - 1) + 1) * Real.sin (θ / 2) ^ 2

/-- Normalized invariant. -/
noncomputable def I (m : ℕ) (θ : ℝ) : ℝ :=
  delta m θ / ((3 : ℝ) ^ (m + 1) + 3)

theorem delta_eq (m : ℕ) (θ : ℝ) :
    delta m θ =
      -16 * ((3 : ℝ) ^ (m - 1) + 1) * Real.sin (θ / 2) ^ 2 := by
  rfl

theorem I_eq (m : ℕ) (θ : ℝ) :
    I m θ =
      (-16 * ((3 : ℝ) ^ (m - 1) + 1) * Real.sin (θ / 2) ^ 2) /
        ((3 : ℝ) ^ (m + 1) + 3) := by
  rfl

/-- Example at m = 1, θ = π/2. -/
theorem delta_one_pi_div_two :
    delta 1 (Real.pi / 2) = -16 := by
  rw [delta]
  have h : Real.pi / 2 / 2 = Real.pi / 4 := by ring
  rw [h, Real.sin_pi_div_four]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    norm_num
  rw [div_pow, hsqrt]
  norm_num

/--
Operator-level bridge.

This is intentionally a proposition, not an axiom: the final formal proof
must construct `traceDefect` from the concrete Sierpiński-gasket graph,
SU(2) edge connection, operators H_C and H_C', and Tr(H^4), and then prove
this identity for every m and θ.
-/
def TraceDefectIdentity (traceDefect : ℕ → ℝ → ℝ) : Prop :=
  ∀ m θ, traceDefect m θ = delta m θ

/-- Closed form follows once the concrete trace identity is proved. -/
theorem evgeny_theorem
    (traceDefect : ℕ → ℝ → ℝ)
    (h : TraceDefectIdentity traceDefect)
    (m : ℕ) (θ : ℝ) :
    traceDefect m θ =
      -16 * ((3 : ℝ) ^ (m - 1) + 1) * Real.sin (θ / 2) ^ 2 := by
  rw [h m θ]
  rfl

/-- Normalized consequence. -/
theorem normalized_evgeny_theorem
    (traceDefect : ℕ → ℝ → ℝ)
    (h : TraceDefectIdentity traceDefect)
    (m : ℕ) (θ : ℝ) :
    traceDefect m θ / ((3 : ℝ) ^ (m + 1) + 3) = I m θ := by
  rw [h m θ]
  rfl

end EvgenyTheorem
