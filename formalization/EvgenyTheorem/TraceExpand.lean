import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

namespace EvgenyTheorem

open Matrix

/-- Cyclic rotation of a four-fold product under the trace. -/
theorem trace_cyc4 {n : Type*} [Fintype n] (a b c d : Matrix n n ℂ) :
    Matrix.trace (a * b * c * d) = Matrix.trace (d * a * b * c) := by
  have h : a * b * c * d = (a * b * c) * d := rfl
  have h' : d * a * b * c = d * (a * b * c) := by
    simp only [Matrix.mul_assoc]
  rw [h, h', Matrix.trace_mul_comm]

/-- **L1a.** Expansion of the fourth power of `D - A` under the trace
(`D` need not commute with `A`). -/
theorem trace_sub_pow4 {n : Type*} [Fintype n] [DecidableEq n] (D A : Matrix n n ℂ) :
    Matrix.trace ((D - A) * (D - A) * (D - A) * (D - A)) =
      Matrix.trace (D * D * D * D) - 4 * Matrix.trace (D * D * D * A)
        + 4 * Matrix.trace (D * D * A * A) + 2 * Matrix.trace (D * A * D * A)
        - 4 * Matrix.trace (D * A * A * A) + Matrix.trace (A * A * A * A) := by
  have e : (D - A) * (D - A) * (D - A) * (D - A) =
      D * D * D * D - (D * D * D * A + D * D * A * D + D * A * D * D + A * D * D * D)
        + (D * D * A * A + D * A * D * A + D * A * A * D + A * D * D * A + A * D * A * D
            + A * A * D * D)
        - (D * A * A * A + A * D * A * A + A * A * D * A + A * A * A * D)
        + A * A * A * A := by
    noncomm_ring
  have h1 : Matrix.trace (D * D * A * D) = Matrix.trace (D * D * D * A) := trace_cyc4 D D A D
  have h2 : Matrix.trace (D * A * D * D) = Matrix.trace (D * D * A * D) := trace_cyc4 D A D D
  have h3 : Matrix.trace (A * D * D * D) = Matrix.trace (D * A * D * D) := trace_cyc4 A D D D
  have h4 : Matrix.trace (D * A * A * D) = Matrix.trace (D * D * A * A) := trace_cyc4 D A A D
  have h5 : Matrix.trace (A * A * D * D) = Matrix.trace (D * A * A * D) := trace_cyc4 A A D D
  have h6 : Matrix.trace (A * D * D * A) = Matrix.trace (A * A * D * D) := trace_cyc4 A D D A
  have h7 : Matrix.trace (A * D * A * D) = Matrix.trace (D * A * D * A) := trace_cyc4 A D A D
  have h8 : Matrix.trace (A * D * A * A) = Matrix.trace (A * A * D * A) := trace_cyc4 A D A A
  have h9 : Matrix.trace (A * A * D * A) = Matrix.trace (A * A * A * D) := trace_cyc4 A A D A
  have h10 : Matrix.trace (A * A * A * D) = Matrix.trace (D * A * A * A) := trace_cyc4 A A A D
  rw [e]
  simp only [Matrix.trace_add, Matrix.trace_sub]
  rw [h3, h2, h1, h6, h5, h4, h7, h8, h9, h10]
  ring

end EvgenyTheorem
