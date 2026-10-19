import EvgenyTheorem.TildeEntries
import EvgenyTheorem.Graph.Sierpinski
import EvgenyTheorem.SanityChecks
import EvgenyTheorem.SU2
import EvgenyTheorem.Operator
import EvgenyTheorem.Locality
import EvgenyTheorem.CornerLocality
import EvgenyTheorem.Orientation
import EvgenyTheorem.Algebra
import EvgenyTheorem.Setup
import EvgenyTheorem.BaseCaseTheorem
import EvgenyTheorem.TraceExpand
import EvgenyTheorem.ListOrder
import EvgenyTheorem.VertexOrder
import EvgenyTheorem.VertexIndex
import EvgenyTheorem.FlipB
import EvgenyTheorem.FlipC
import EvgenyTheorem.FlipFaces
import EvgenyTheorem.FlipCount
import EvgenyTheorem.SGStruct
import EvgenyTheorem.EdgeStep
import EvgenyTheorem.PointModel1
import EvgenyTheorem.PointModel2
import EvgenyTheorem.EdgeCopies
import EvgenyTheorem.EdgeSplit
import EvgenyTheorem.DegSplit
import EvgenyTheorem.FluxSplit
import EvgenyTheorem.OpSplit1
import EvgenyTheorem.OpSplit2
import EvgenyTheorem.OpSplit3
import EvgenyTheorem.GlueAlg
import EvgenyTheorem.GlueTrace
import EvgenyTheorem.GlueCornerCube
import EvgenyTheorem.FinalOrient
import EvgenyTheorem.FinalArith
import EvgenyTheorem.FinalTilde
import EvgenyTheorem.FinalTheorem
import EvgenyTheorem.AlgebraTilde
import EvgenyTheorem.CornerFaces
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

Abstract form of the statement: a function `traceDefect : ℕ → ℝ → ℝ` satisfies the closed form at
every level. This is a proposition, not an axiom. For the concrete operators `HC`, `HCprime` the closed form is
proved below (`traceDefect_eq_delta`, from `traceDefect_closed`) for every level `m ≥ 1`; it is not claimed at `m = 0`.
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

/-- **Evgeny's Theorem, operator level (machine-checked).** For every level `m ≥ 1` and every angle `θ`,
the fourth-moment trace defect of the concrete operators `HC`, `HCprime` on `SG(m)` equals the closed
form `delta m θ`. The closed form is not claimed at `m = 0`. -/
theorem traceDefect_eq_delta (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) :
    traceDefect m θ = (delta m θ : ℂ) := by
  rw [traceDefect_closed θ m hm]
  first
    | (simp [delta]; done)
    | (simp [delta]; ring)
    | (unfold delta; push_cast; ring)

theorem traceDefect_re_eq_delta (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) :
    (traceDefect m θ).re = delta m θ := by
  rw [traceDefect_eq_delta m hm θ]
  exact Complex.ofReal_re _

theorem traceDefect_im_eq_zero (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) :
    (traceDefect m θ).im = 0 := by
  rw [traceDefect_eq_delta m hm θ]
  exact Complex.ofReal_im _

/-- A shift by two recursive flux blocks also preserves the cyclic axis label. -/
theorem faceAxis_shift_by_two_three_pow (m i : ℕ) (hm : 1 ≤ m) :
    faceAxis (2 * 3 ^ m + i) = faceAxis i := by
  have hsum : 3 ^ m + (3 ^ m + i) = 2 * 3 ^ m + i := by omega
  rw [← hsum]
  exact (faceAxis_shift_by_three_pow m (3 ^ m + i) hm).trans
    (faceAxis_shift_by_three_pow m i hm)

/-- The axis label of an edge is unchanged when the edge is copied into block B. -/
theorem edgeAxis_succ_B (m : ℕ) (e : Point × Point)
    (he : e ∈ fluxEdges m) (hm : 1 ≤ m) :
    edgeAxis (m + 1) (shiftEdge (2 ^ m) 1 0 e) = edgeAxis m e := by
  unfold edgeAxis
  rw [fluxIndex_succ_B he]
  exact faceAxis_shift_by_three_pow m (fluxIndex m e) hm

/-- The axis label of an edge is unchanged when the edge is copied into block C. -/
theorem edgeAxis_succ_C (m : ℕ) (e : Point × Point)
    (he : e ∈ fluxEdges m) (hm : 1 ≤ m) :
    edgeAxis (m + 1) (shiftEdge (2 ^ m) 0 1 e) = edgeAxis m e := by
  unfold edgeAxis
  rw [fluxIndex_succ_C he]
  exact faceAxis_shift_by_two_three_pow m (fluxIndex m e) hm

end EvgenyTheorem
