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

/-- Cyclic invariance of the trace for an arbitrary split of a finite product.
This packages cyclic rotation of an ordered word without assuming its factors commute. -/
theorem trace_cyclic_list {n : Type*} [Fintype n] [DecidableEq n]
    (xs ys : List (Matrix n n ℂ)) :
    Matrix.trace ((xs ++ ys).prod) = Matrix.trace ((ys ++ xs).prod) := by
  classical
  rw [List.prod_append, List.prod_append]
  exact Matrix.trace_mul_comm _ _

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


/-- Sum of a list of right-multiplied matrices: multiplication distributes over
the finite sum without reordering any factor. -/
theorem matrix_list_sum_map_mul_right {n : Type*} [Fintype n] [DecidableEq n]
    (xs : List (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    (xs.map (fun X => X * A)).sum = xs.sum * A := by
  induction xs with
  | nil => simp
  | cons X xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, add_mul]

/-- Ordered expansion of a noncommutative power. At each step the new factor
is appended on the right, so the list retains factor order and repeated terms
retain their multiplicity. -/
def orderedWordExpansion {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) : ℕ → List (Matrix n n ℂ)
  | 0 => [1]
  | p + 1 =>
      (orderedWordExpansion A B p).map (fun X => X * A) ++
      (orderedWordExpansion A B p).map (fun X => X * B)

/-- The ordered word list sums to the corresponding power. This is valid for
noncommuting matrices A and B; no permutation or collection of words is used. -/
theorem sum_orderedWordExpansion {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (p : ℕ) :
    (orderedWordExpansion A B p).sum = (A + B) ^ p := by
  induction p with
  | zero => simp [orderedWordExpansion]
  | succ p ih =>
      simp only [orderedWordExpansion, List.sum_append,
        matrix_list_sum_map_mul_right, ih]
      rw [pow_succ, mul_add]

/-- Trace-level form of the ordered expansion. The right-hand side is a list
sum rather than a set or a cyclic-class sum, so duplicate words are counted
with their full multiplicity. -/
theorem trace_sum_list {n : Type*} [Fintype n] [DecidableEq n]
    (xs : List (Matrix n n ℂ)) :
    Matrix.trace xs.sum = (xs.map Matrix.trace).sum := by
  induction xs with
  | nil => simp
  | cons X xs ih =>
      simp only [List.sum_cons, List.map_cons, List.sum_cons,
        Matrix.trace_add, ih]

/-- General trace expansion for the power of A + B that preserves the original
order and multiplicities of all 2^p factor-choice words. -/
theorem trace_orderedWordExpansion {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (p : ℕ) :
    Matrix.trace ((A + B) ^ p) =
      ((orderedWordExpansion A B p).map Matrix.trace).sum := by
  rw [← sum_orderedWordExpansion A B p]
  exact trace_sum_list (orderedWordExpansion A B p)



/-- Iterating a level-three affine recurrence gives an exact closed form.
The finite sum is the geometric correction term; no assumption about the
origin of the recurrence is built into this lemma. -/
theorem affine_recurrence_closed_form
    (delta : ℕ → ℂ) (C : ℂ)
    (hrec : ∀ m, 3 ≤ m → delta m = 3 * delta (m - 1) + C)
    (n : ℕ) :
    delta (n + 3) =
      (3 : ℂ) ^ n * delta 3 +
        (∑ i in Finset.range n, (3 : ℂ) ^ i) * C := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hstep := hrec (n + 4) (by omega)
      have hindex : n + 4 - 1 = n + 3 := by omega
      rw [hindex] at hstep
      rw [show n + 1 + 3 = n + 4 by omega, hstep, ih]
      rw [Finset.sum_range_succ]
      simp only [pow_succ]
      ring

end EvgenyTheorem
