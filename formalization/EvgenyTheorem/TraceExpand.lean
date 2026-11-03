import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic

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



/-- Exact cyclic-orbit grouping of the sixth ordered-word trace expansion.
The 64 ordered choice words are grouped into their 14 cyclic classes with
orbit weights 1, 6, 3, or 2 as appropriate. This is a purely algebraic
identity for arbitrary matrices; no words are commuted or discarded. -/
theorem trace_orderedWordExpansion_six_cyclic
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    ((orderedWordExpansion A B 6).map Matrix.trace).sum =
      Matrix.trace (A * A * A * A * A * A)
      + 6 * Matrix.trace (A * A * A * A * A * B)
      + 6 * Matrix.trace (A * A * A * A * B * B)
      + 6 * Matrix.trace (A * A * A * B * A * B)
      + 6 * Matrix.trace (A * A * A * B * B * B)
      + 3 * Matrix.trace (A * A * B * A * A * B)
      + 6 * Matrix.trace (A * A * B * A * B * B)
      + 6 * Matrix.trace (A * A * B * B * A * B)
      + 6 * Matrix.trace (A * A * B * B * B * B)
      + 2 * Matrix.trace (A * B * A * B * A * B)
      + 6 * Matrix.trace (A * B * A * B * B * B)
      + 3 * Matrix.trace (A * B * B * A * B * B)
      + 6 * Matrix.trace (A * B * B * B * B * B)
      + Matrix.trace (B * B * B * B * B * B) := by
  have hrot_100000 : Matrix.trace (B * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, A, A, A, A])

  have hrot_010000 : Matrix.trace (A * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B] [A, A, A, A])

  have hrot_110000 : Matrix.trace (B * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B] [A, A, A, A])

  have hrot_001000 : Matrix.trace (A * A * B * A * A * A) =
      Matrix.trace (A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, A, B] [A, A, A])

  have hrot_101000 : Matrix.trace (B * A * B * A * A * A) =
      Matrix.trace (A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, A, B] [A, A, A])

  have hrot_011000 : Matrix.trace (A * B * B * A * A * A) =
      Matrix.trace (A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B, B] [A, A, A])

  have hrot_111000 : Matrix.trace (B * B * B * A * A * A) =
      Matrix.trace (A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B, B] [A, A, A])

  have hrot_000100 : Matrix.trace (A * A * A * B * A * A) =
      Matrix.trace (A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, A, A, B] [A, A])

  have hrot_100100 : Matrix.trace (B * A * A * B * A * A) =
      Matrix.trace (A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, A, B, A, A])

  have hrot_010100 : Matrix.trace (A * B * A * B * A * A) =
      Matrix.trace (A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B, A, B] [A, A])

  have hrot_110100 : Matrix.trace (B * B * A * B * A * A) =
      Matrix.trace (A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B, A, B] [A, A])

  have hrot_001100 : Matrix.trace (A * A * B * B * A * A) =
      Matrix.trace (A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, A, B, B] [A, A])

  have hrot_101100 : Matrix.trace (B * A * B * B * A * A) =
      Matrix.trace (A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, A, B, B] [A, A])

  have hrot_011100 : Matrix.trace (A * B * B * B * A * A) =
      Matrix.trace (A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B, B, B] [A, A])

  have hrot_111100 : Matrix.trace (B * B * B * B * A * A) =
      Matrix.trace (A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B, B, B] [A, A])

  have hrot_000010 : Matrix.trace (A * A * A * A * B * A) =
      Matrix.trace (A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, A, A, A, B] [A])

  have hrot_100010 : Matrix.trace (B * A * A * A * B * A) =
      Matrix.trace (A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, A, A, B, A])

  have hrot_010010 : Matrix.trace (A * B * A * A * B * A) =
      Matrix.trace (A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B] [A, A, B, A])

  have hrot_110010 : Matrix.trace (B * B * A * A * B * A) =
      Matrix.trace (A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B] [A, A, B, A])

  have hrot_001010 : Matrix.trace (A * A * B * A * B * A) =
      Matrix.trace (A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, A, B, A, B] [A])

  have hrot_101010 : Matrix.trace (B * A * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, B, A, B, A])

  have hrot_011010 : Matrix.trace (A * B * B * A * B * A) =
      Matrix.trace (A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B, B, A, B] [A])

  have hrot_111010 : Matrix.trace (B * B * B * A * B * A) =
      Matrix.trace (A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B, B] [A, B, A])

  have hrot_000110 : Matrix.trace (A * A * A * B * B * A) =
      Matrix.trace (A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, A, A, B, B] [A])

  have hrot_100110 : Matrix.trace (B * A * A * B * B * A) =
      Matrix.trace (A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, A, B, B, A])

  have hrot_010110 : Matrix.trace (A * B * A * B * B * A) =
      Matrix.trace (A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B, A, B, B] [A])

  have hrot_110110 : Matrix.trace (B * B * A * B * B * A) =
      Matrix.trace (A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B] [A, B, B, A])

  have hrot_001110 : Matrix.trace (A * A * B * B * B * A) =
      Matrix.trace (A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, A, B, B, B] [A])

  have hrot_101110 : Matrix.trace (B * A * B * B * B * A) =
      Matrix.trace (A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, A, B, B, B] [A])

  have hrot_011110 : Matrix.trace (A * B * B * B * B * A) =
      Matrix.trace (A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B, B, B, B] [A])

  have hrot_111110 : Matrix.trace (B * B * B * B * B * A) =
      Matrix.trace (A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B, B, B, B] [A])

  have hrot_100001 : Matrix.trace (B * A * A * A * A * B) =
      Matrix.trace (A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, A, A, A, B])

  have hrot_010001 : Matrix.trace (A * B * A * A * A * B) =
      Matrix.trace (A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B] [A, A, A, B])

  have hrot_110001 : Matrix.trace (B * B * A * A * A * B) =
      Matrix.trace (A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B] [A, A, A, B])

  have hrot_101001 : Matrix.trace (B * A * B * A * A * B) =
      Matrix.trace (A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, A, B] [A, A, B])

  have hrot_011001 : Matrix.trace (A * B * B * A * A * B) =
      Matrix.trace (A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B, B] [A, A, B])

  have hrot_111001 : Matrix.trace (B * B * B * A * A * B) =
      Matrix.trace (A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B, B] [A, A, B])

  have hrot_100101 : Matrix.trace (B * A * A * B * A * B) =
      Matrix.trace (A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, A, B, A, B])

  have hrot_110101 : Matrix.trace (B * B * A * B * A * B) =
      Matrix.trace (A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B] [A, B, A, B])

  have hrot_101101 : Matrix.trace (B * A * B * B * A * B) =
      Matrix.trace (A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, B, B, A, B])

  have hrot_011101 : Matrix.trace (A * B * B * B * A * B) =
      Matrix.trace (A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B, B, B] [A, B])

  have hrot_111101 : Matrix.trace (B * B * B * B * A * B) =
      Matrix.trace (A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B, B, B] [A, B])

  have hrot_100011 : Matrix.trace (B * A * A * A * B * B) =
      Matrix.trace (A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, A, A, B, B])

  have hrot_010011 : Matrix.trace (A * B * A * A * B * B) =
      Matrix.trace (A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [A, B] [A, A, B, B])

  have hrot_110011 : Matrix.trace (B * B * A * A * B * B) =
      Matrix.trace (A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B] [A, A, B, B])

  have hrot_101011 : Matrix.trace (B * A * B * A * B * B) =
      Matrix.trace (A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, B, A, B, B])

  have hrot_111011 : Matrix.trace (B * B * B * A * B * B) =
      Matrix.trace (A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B, B] [A, B, B])

  have hrot_100111 : Matrix.trace (B * A * A * B * B * B) =
      Matrix.trace (A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, A, B, B, B])

  have hrot_110111 : Matrix.trace (B * B * A * B * B * B) =
      Matrix.trace (A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B, B] [A, B, B, B])

  have hrot_101111 : Matrix.trace (B * A * B * B * B * B) =
      Matrix.trace (A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list [B] [A, B, B, B, B])
  simp [orderedWordExpansion, List.map_append, List.sum_append,
    hrot_100000,
    hrot_010000,
    hrot_110000,
    hrot_001000,
    hrot_101000,
    hrot_011000,
    hrot_111000,
    hrot_000100,
    hrot_100100,
    hrot_010100,
    hrot_110100,
    hrot_001100,
    hrot_101100,
    hrot_011100,
    hrot_111100,
    hrot_000010,
    hrot_100010,
    hrot_010010,
    hrot_110010,
    hrot_001010,
    hrot_101010,
    hrot_011010,
    hrot_111010,
    hrot_000110,
    hrot_100110,
    hrot_010110,
    hrot_110110,
    hrot_001110,
    hrot_101110,
    hrot_011110,
    hrot_111110,
    hrot_100001,
    hrot_010001,
    hrot_110001,
    hrot_101001,
    hrot_011001,
    hrot_111001,
    hrot_100101,
    hrot_110101,
    hrot_101101,
    hrot_011101,
    hrot_111101,
    hrot_100011,
    hrot_010011,
    hrot_110011,
    hrot_101011,
    hrot_111011,
    hrot_100111,
    hrot_110111,
    hrot_101111]
  <;> ring





/-- Iterating a level-three affine recurrence gives an exact closed form. -/
theorem affine_recurrence_closed_form
    (delta : ℕ → ℂ) (C : ℂ)
    (hrec : ∀ m, 3 ≤ m → delta m = 3 * delta (m - 1) + C)
    (n : ℕ) :
    delta (n + 3) =
      (3 : ℂ) ^ n * delta 3 + (((3 : ℂ) ^ n - 1) / 2) * C := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hstep := hrec (n + 4) (by omega)
      have hindex : n + 4 - 1 = n + 3 := by omega
      rw [hindex] at hstep
      rw [show n + 1 + 3 = n + 4 by omega, hstep, ih]
      simp only [pow_succ]
      ring


/-- The trace of a conjugate-transposed complex matrix is the conjugate of
the original trace. -/
theorem trace_conjTranspose_eq_star {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) :
    Matrix.trace (Matrix.conjTranspose M) = star (Matrix.trace M) := by
  simp [Matrix.trace, Matrix.conjTranspose_apply]

/-- Cyclic trace invariance for powers of a product: the factors may be
swapped as a pair, even though the matrices themselves need not commute. -/
theorem trace_mul_pow_swap {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (p : ℕ) :
    Matrix.trace ((A * B) ^ p) = Matrix.trace ((B * A) ^ p) := by
  have hshift : ∀ q : ℕ, B * (A * B) ^ q = (B * A) ^ q * B := by
    intro q
    induction q with
    | zero =>
        simp
    | succ q ih =>
        rw [pow_succ]
        calc
          B * ((A * B) ^ q * (A * B)) =
              (B * (A * B) ^ q) * A * B := by
                simp [Matrix.mul_assoc]
          _ = ((B * A) ^ q * B) * A * B := by rw [ih]
          _ = (B * A) ^ (q + 1) * B := by
                rw [pow_succ]
                simp [Matrix.mul_assoc]
  cases p with
  | zero =>
      simp
  | succ p =>
      rw [pow_succ, pow_succ]
      calc
        Matrix.trace ((A * B) ^ p * (A * B)) =
            Matrix.trace (((A * B) ^ p * A) * B) := by
              simp [Matrix.mul_assoc]
        _ = Matrix.trace (B * ((A * B) ^ p * A)) :=
              Matrix.trace_mul_comm _ _
        _ = Matrix.trace (((B * A) ^ p * B) * A) := by
              rw [← Matrix.mul_assoc B ((A * B) ^ p) A]
              rw [show B * (A * B) ^ p = (B * A) ^ p * B from hshift p]
        _ = Matrix.trace ((B * A) ^ p * (B * A)) := by
              congr 1
              simp [Matrix.mul_assoc]

/-- If A and B are self-adjoint, every power of their product has real trace.
This follows from adjoint reversal and the cyclic product-power identity above. -/
theorem trace_mul_pow_real_of_selfAdjoint {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ)
    (hA : Matrix.conjTranspose A = A)
    (hB : Matrix.conjTranspose B = B) (p : ℕ) :
    star (Matrix.trace ((A * B) ^ p)) = Matrix.trace ((A * B) ^ p) := by
  rw [← trace_conjTranspose_eq_star, Matrix.conjTranspose_pow,
    Matrix.conjTranspose_mul, hA, hB]
  exact trace_mul_pow_swap B A p

/-- Conjugate transpose reverses an ordered product when every factor is
self-adjoint. The order is retained explicitly; no factors are commuted. -/
theorem conjTranspose_list_prod_eq_reverse {n : Type*} [Fintype n] [DecidableEq n]
    (xs : List (Matrix n n ℂ))
    (hxs : ∀ M, M ∈ xs → Matrix.conjTranspose M = M) :
    Matrix.conjTranspose xs.prod = xs.reverse.prod := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : Matrix.conjTranspose x = x := hxs x (by simp)
      have htail : ∀ M, M ∈ xs → Matrix.conjTranspose M = M := by
        intro M hM
        exact hxs M (by simp [hM])
      simp only [List.prod_cons, Matrix.conjTranspose_mul, hx, ih htail]
      simp [List.reverse_cons, List.prod_append]

/-- Adjoint reversal pairs the trace of an ordered self-adjoint word with the
complex conjugate trace of its reversed word. This is the operator-level
identity needed before using reversal pairings in higher-moment word sums. -/
theorem trace_reverse_conj_of_selfAdjoint_list
    {n : Type*} [Fintype n] [DecidableEq n]
    (xs : List (Matrix n n ℂ))
    (hxs : ∀ M, M ∈ xs → Matrix.conjTranspose M = M) :
    star (Matrix.trace xs.prod) = Matrix.trace xs.reverse.prod := by
  rw [← trace_conjTranspose_eq_star]
  rw [conjTranspose_list_prod_eq_reverse xs hxs]





/-- Reindexing a finite sum by an involution swaps the two factors paired
across that involution. This is the kernel-level symmetry needed before the
cyclic-gap weights can be applied to concrete boundary sums. -/
theorem sum_involution_product_swap
    {W : Type*} [Fintype W] {α : Type*} [CommSemiring α]
    (σ : Equiv.Perm W) (hσ : ∀ x, σ (σ x) = x)
    (f g : W → α) :
    (∑ x, f x * g (σ x)) = ∑ x, g x * f (σ x) := by
  calc
    (∑ x, f x * g (σ x)) =
        ∑ x, (fun y => f y * g (σ y)) (σ x) := by
          symm
          exact Equiv.sum_comp σ (fun y => f y * g (σ y))
    _ = ∑ x, f (σ x) * g x := by
          simp [hσ]
    _ = ∑ x, g x * f (σ x) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact mul_comm _ _

/-- A word and its reversed word have a real combined trace whenever
all factors are self-adjoint. This lets reversal-paired contributions be
collected without commuting any factors. -/
theorem trace_reverse_pair_sum_real
    {n : Type*} [Fintype n] [DecidableEq n]
    (xs : List (Matrix n n ℂ))
    (hxs : ∀ M, M ∈ xs → Matrix.conjTranspose M = M) :
    star (Matrix.trace xs.prod + Matrix.trace xs.reverse.prod) =
      Matrix.trace xs.prod + Matrix.trace xs.reverse.prod := by
  rw [star_add, trace_reverse_conj_of_selfAdjoint_list xs hxs]
  have hrev : ∀ M, M ∈ xs.reverse → Matrix.conjTranspose M = M := by
    intro M hM
    apply hxs
    simpa using hM
  rw [trace_reverse_conj_of_selfAdjoint_list xs.reverse hrev]
  simpa only [List.reverse_reverse] using
    (add_comm (Matrix.trace xs.reverse.prod) (Matrix.trace xs.prod))

/-! ## Two-N cyclic-gap weights for the target moments

These are the finite orbit-weight identities for the lowest even stratum.
They formalize only the cyclic multiplicities: the hypotheses state the
complementary-gap symmetry of the corresponding boundary kernel. They do not
assert that the operator kernels are axis-independent. -/

/-- For p=6, complementary gaps have weights 6,6,3. -/
theorem twoN_gap_weights_six {α : Type*} [CommRing α] (E : ℕ → α)
    (h15 : E 1 = E 5) (h24 : E 2 = E 4) :
    6 * E 1 + 6 * E 2 + 3 * E 3 =
      3 * (E 1 + E 2 + E 3 + E 4 + E 5) := by
  rw [h15, h24]
  ring

/-- For p=8, complementary gaps have weights 8,8,8,4. -/
theorem twoN_gap_weights_eight {α : Type*} [CommRing α] (E : ℕ → α)
    (h17 : E 1 = E 7) (h26 : E 2 = E 6) (h35 : E 3 = E 5) :
    8 * E 1 + 8 * E 2 + 8 * E 3 + 4 * E 4 =
      4 * (E 1 + E 2 + E 3 + E 4 + E 5 + E 6 + E 7) := by
  rw [h17, h26, h35]
  ring

/-- For p=10, complementary gaps have weights 10,10,10,10,5. -/
theorem twoN_gap_weights_ten {α : Type*} [CommRing α] (E : ℕ → α)
    (h19 : E 1 = E 9) (h28 : E 2 = E 8) (h37 : E 3 = E 7)
    (h46 : E 4 = E 6) :
    10 * E 1 + 10 * E 2 + 10 * E 3 + 10 * E 4 + 5 * E 5 =
      5 * (E 1 + E 2 + E 3 + E 4 + E 5 + E 6 + E 7 + E 8 + E 9) := by
  rw [h19, h28, h37, h46]
  ring


/-- If a moment defect has the affine-in-3^m form
`a * 3^(m-3) + c` at two consecutive levels, then its
three-to-one residual is exactly `-2*c`. This is an algebraic
consequence of the candidate form; it does not assert that an operator
trace defect has that form. -/
theorem residual_eq_neg_two_constant_of_affine_three_pow
    {α : Type*} [CommRing α] (D : ℕ → α) (a c : α) (m : ℕ)
    (hm : 4 ≤ m)
    (hD : D m = a * (3 : α) ^ (m - 3) + c)
    (hPrev : D (m - 1) = a * (3 : α) ^ (m - 4) + c) :
    D m - 3 * D (m - 1) = -2 * c := by
  rw [hD, hPrev]
  have hexp : m - 3 = (m - 4) + 1 := by omega
  rw [hexp, pow_succ]
  ring


/-- A constant three-to-one residual implies the affine-in-3^m closed form.
This is the converse direction to residual_eq_neg_two_constant_of_affine_three_pow.
It is a sequence theorem over ℚ; applying it to operator traces still requires
proving the residual recurrence for those traces. -/
theorem affine_three_pow_of_recurrence
    (D : ℕ → ℚ) (R : ℚ)
    (hrec : ∀ n, 4 ≤ n → D n = 3 * D (n - 1) + R) :
    ∀ k, D (k + 3) = (D 3 + R / 2) * 3 ^ k - R / 2 := by
  intro k
  induction k with
  | zero =>
      ring
  | succ k ih =>
      have hn : 4 ≤ k + 4 := by omega
      rw [hrec (k + 4) hn]
      have hidx : k + 4 - 1 = k + 3 := by omega
      rw [hidx, ih, pow_succ]
      ring


/-- Converse: the affine closed form forces a constant three-to-one residual.
Together with affine_three_pow_of_recurrence, this characterizes the sequence
formula exactly; it still does not establish the recurrence for operator traces. -/
theorem recurrence_of_affine_three_pow
    (D : ℕ → ℚ) (R : ℚ)
    (hform : ∀ k, D (k + 3) = (D 3 + R / 2) * 3 ^ k - R / 2) :
    ∀ n, 4 ≤ n → D n = 3 * D (n - 1) + R := by
  intro n hn
  let k := n - 4
  have hindex : n = k + 4 := by
    dsimp [k]
    omega
  have hprev : (k + 4) - 1 = k + 3 := by omega
  rw [hindex, hprev, hform (k + 1), hform k, pow_succ]
  ring


set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Exact cyclic-orbit grouping of the eighth ordered-word trace expansion.
The 256 ordered choice words are grouped into their 36 cyclic classes using
the inventory's exact orbit sizes. This is a purely algebraic identity:
no factors are commuted, no class is discarded, and all periodic classes
retain their actual shorter orbit weights. -/
theorem trace_orderedWordExpansion_eight_cyclic
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    ((orderedWordExpansion A B 8).map Matrix.trace).sum =
      1 * Matrix.trace (A * A * A * A * A * A * A * A)
      + 8 * Matrix.trace (A * A * A * A * A * A * A * B)
      + 8 * Matrix.trace (A * A * A * A * A * A * B * B)
      + 8 * Matrix.trace (A * A * A * A * A * B * A * B)
      + 8 * Matrix.trace (A * A * A * A * A * B * B * B)
      + 8 * Matrix.trace (A * A * A * A * B * A * A * B)
      + 8 * Matrix.trace (A * A * A * A * B * A * B * B)
      + 8 * Matrix.trace (A * A * A * A * B * B * A * B)
      + 8 * Matrix.trace (A * A * A * A * B * B * B * B)
      + 4 * Matrix.trace (A * A * A * B * A * A * A * B)
      + 8 * Matrix.trace (A * A * A * B * A * A * B * B)
      + 8 * Matrix.trace (A * A * A * B * A * B * A * B)
      + 8 * Matrix.trace (A * A * A * B * A * B * B * B)
      + 8 * Matrix.trace (A * A * A * B * B * A * A * B)
      + 8 * Matrix.trace (A * A * A * B * B * A * B * B)
      + 8 * Matrix.trace (A * A * A * B * B * B * A * B)
      + 8 * Matrix.trace (A * A * A * B * B * B * B * B)
      + 8 * Matrix.trace (A * A * B * A * A * B * A * B)
      + 8 * Matrix.trace (A * A * B * A * A * B * B * B)
      + 8 * Matrix.trace (A * A * B * A * B * A * B * B)
      + 8 * Matrix.trace (A * A * B * A * B * B * A * B)
      + 8 * Matrix.trace (A * A * B * A * B * B * B * B)
      + 4 * Matrix.trace (A * A * B * B * A * A * B * B)
      + 8 * Matrix.trace (A * A * B * B * A * B * A * B)
      + 8 * Matrix.trace (A * A * B * B * A * B * B * B)
      + 8 * Matrix.trace (A * A * B * B * B * A * B * B)
      + 8 * Matrix.trace (A * A * B * B * B * B * A * B)
      + 8 * Matrix.trace (A * A * B * B * B * B * B * B)
      + 2 * Matrix.trace (A * B * A * B * A * B * A * B)
      + 8 * Matrix.trace (A * B * A * B * A * B * B * B)
      + 8 * Matrix.trace (A * B * A * B * B * A * B * B)
      + 8 * Matrix.trace (A * B * A * B * B * B * B * B)
      + 8 * Matrix.trace (A * B * B * A * B * B * B * B)
      + 4 * Matrix.trace (A * B * B * B * A * B * B * B)
      + 8 * Matrix.trace (A * B * B * B * B * B * B * B)
      + 1 * Matrix.trace (B * B * B * B * B * B * B * B) := by
  have hrot_00000010 : Matrix.trace (A * A * A * A * A * A * B * A) =
      Matrix.trace (A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00000100 : Matrix.trace (A * A * A * A * A * B * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_00000110 : Matrix.trace (A * A * A * A * A * B * B * A) =
      Matrix.trace (A * A * A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00001000 : Matrix.trace (A * A * A * A * B * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_00001010 : Matrix.trace (A * A * A * A * B * A * B * A) =
      Matrix.trace (A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00001100 : Matrix.trace (A * A * A * A * B * B * A * A) =
      Matrix.trace (A * A * A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_00001110 : Matrix.trace (A * A * A * A * B * B * B * A) =
      Matrix.trace (A * A * A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00010000 : Matrix.trace (A * A * A * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_00010010 : Matrix.trace (A * A * A * B * A * A * B * A) =
      Matrix.trace (A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00010100 : Matrix.trace (A * A * A * B * A * B * A * A) =
      Matrix.trace (A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_00010110 : Matrix.trace (A * A * A * B * A * B * B * A) =
      Matrix.trace (A * A * A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00011000 : Matrix.trace (A * A * A * B * B * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_00011010 : Matrix.trace (A * A * A * B * B * A * B * A) =
      Matrix.trace (A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00011100 : Matrix.trace (A * A * A * B * B * B * A * A) =
      Matrix.trace (A * A * A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_00011110 : Matrix.trace (A * A * A * B * B * B * B * A) =
      Matrix.trace (A * A * A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00100000 : Matrix.trace (A * A * B * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_00100001 : Matrix.trace (A * A * B * A * A * A * A * B) =
      Matrix.trace (A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_00100010 : Matrix.trace (A * A * B * A * A * A * B * A) =
      Matrix.trace (A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_00100011 : Matrix.trace (A * A * B * A * A * A * B * B) =
      Matrix.trace (A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_00100100 : Matrix.trace (A * A * B * A * A * B * A * A) =
      Matrix.trace (A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_00100110 : Matrix.trace (A * A * B * A * A * B * B * A) =
      Matrix.trace (A * A * A * B * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00101000 : Matrix.trace (A * A * B * A * B * A * A * A) =
      Matrix.trace (A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_00101001 : Matrix.trace (A * A * B * A * B * A * A * B) =
      Matrix.trace (A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_00101010 : Matrix.trace (A * A * B * A * B * A * B * A) =
      Matrix.trace (A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00101100 : Matrix.trace (A * A * B * A * B * B * A * A) =
      Matrix.trace (A * A * A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_00101110 : Matrix.trace (A * A * B * A * B * B * B * A) =
      Matrix.trace (A * A * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00110000 : Matrix.trace (A * A * B * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B] : List (Matrix n n ℂ)) ([A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_00110001 : Matrix.trace (A * A * B * B * A * A * A * B) =
      Matrix.trace (A * A * A * B * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B] : List (Matrix n n ℂ)) ([A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_00110010 : Matrix.trace (A * A * B * B * A * A * B * A) =
      Matrix.trace (A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00110100 : Matrix.trace (A * A * B * B * A * B * A * A) =
      Matrix.trace (A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_00110110 : Matrix.trace (A * A * B * B * A * B * B * A) =
      Matrix.trace (A * A * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00111000 : Matrix.trace (A * A * B * B * B * A * A * A) =
      Matrix.trace (A * A * A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_00111001 : Matrix.trace (A * A * B * B * B * A * A * B) =
      Matrix.trace (A * A * B * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_00111010 : Matrix.trace (A * A * B * B * B * A * B * A) =
      Matrix.trace (A * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, B, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_00111100 : Matrix.trace (A * A * B * B * B * B * A * A) =
      Matrix.trace (A * A * A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_00111110 : Matrix.trace (A * A * B * B * B * B * B * A) =
      Matrix.trace (A * A * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_01000000 : Matrix.trace (A * B * A * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_01000001 : Matrix.trace (A * B * A * A * A * A * A * B) =
      Matrix.trace (A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_01000010 : Matrix.trace (A * B * A * A * A * A * B * A) =
      Matrix.trace (A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_01000011 : Matrix.trace (A * B * A * A * A * A * B * B) =
      Matrix.trace (A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_01000100 : Matrix.trace (A * B * A * A * A * B * A * A) =
      Matrix.trace (A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_01000101 : Matrix.trace (A * B * A * A * A * B * A * B) =
      Matrix.trace (A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_01000110 : Matrix.trace (A * B * A * A * A * B * B * A) =
      Matrix.trace (A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_01000111 : Matrix.trace (A * B * A * A * A * B * B * B) =
      Matrix.trace (A * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_01001000 : Matrix.trace (A * B * A * A * B * A * A * A) =
      Matrix.trace (A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_01001001 : Matrix.trace (A * B * A * A * B * A * A * B) =
      Matrix.trace (A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_01001010 : Matrix.trace (A * B * A * A * B * A * B * A) =
      Matrix.trace (A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_01001011 : Matrix.trace (A * B * A * A * B * A * B * B) =
      Matrix.trace (A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_01001100 : Matrix.trace (A * B * A * A * B * B * A * A) =
      Matrix.trace (A * A * A * B * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_01001101 : Matrix.trace (A * B * A * A * B * B * A * B) =
      Matrix.trace (A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_01001110 : Matrix.trace (A * B * A * A * B * B * B * A) =
      Matrix.trace (A * A * B * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_01001111 : Matrix.trace (A * B * A * A * B * B * B * B) =
      Matrix.trace (A * A * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_01010000 : Matrix.trace (A * B * A * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_01010001 : Matrix.trace (A * B * A * B * A * A * A * B) =
      Matrix.trace (A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_01010010 : Matrix.trace (A * B * A * B * A * A * B * A) =
      Matrix.trace (A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_01010011 : Matrix.trace (A * B * A * B * A * A * B * B) =
      Matrix.trace (A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_01010100 : Matrix.trace (A * B * A * B * A * B * A * A) =
      Matrix.trace (A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_01010110 : Matrix.trace (A * B * A * B * A * B * B * A) =
      Matrix.trace (A * A * B * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_01011000 : Matrix.trace (A * B * A * B * B * A * A * A) =
      Matrix.trace (A * A * A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_01011001 : Matrix.trace (A * B * A * B * B * A * A * B) =
      Matrix.trace (A * A * B * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_01011010 : Matrix.trace (A * B * A * B * B * A * B * A) =
      Matrix.trace (A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_01011100 : Matrix.trace (A * B * A * B * B * B * A * A) =
      Matrix.trace (A * A * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_01011101 : Matrix.trace (A * B * A * B * B * B * A * B) =
      Matrix.trace (A * B * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, B, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_01011110 : Matrix.trace (A * B * A * B * B * B * B * A) =
      Matrix.trace (A * A * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_01100000 : Matrix.trace (A * B * B * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B] : List (Matrix n n ℂ)) ([A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_01100001 : Matrix.trace (A * B * B * A * A * A * A * B) =
      Matrix.trace (A * A * A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B] : List (Matrix n n ℂ)) ([A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_01100010 : Matrix.trace (A * B * B * A * A * A * B * A) =
      Matrix.trace (A * A * A * B * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B] : List (Matrix n n ℂ)) ([A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_01100011 : Matrix.trace (A * B * B * A * A * A * B * B) =
      Matrix.trace (A * A * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B] : List (Matrix n n ℂ)) ([A, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_01100100 : Matrix.trace (A * B * B * A * A * B * A * A) =
      Matrix.trace (A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_01100101 : Matrix.trace (A * B * B * A * A * B * A * B) =
      Matrix.trace (A * A * B * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B] : List (Matrix n n ℂ)) ([A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_01100110 : Matrix.trace (A * B * B * A * A * B * B * A) =
      Matrix.trace (A * A * B * B * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B] : List (Matrix n n ℂ)) ([A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_01100111 : Matrix.trace (A * B * B * A * A * B * B * B) =
      Matrix.trace (A * A * B * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B] : List (Matrix n n ℂ)) ([A, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_01101000 : Matrix.trace (A * B * B * A * B * A * A * A) =
      Matrix.trace (A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_01101001 : Matrix.trace (A * B * B * A * B * A * A * B) =
      Matrix.trace (A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_01101010 : Matrix.trace (A * B * B * A * B * A * B * A) =
      Matrix.trace (A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_01101011 : Matrix.trace (A * B * B * A * B * A * B * B) =
      Matrix.trace (A * B * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B] : List (Matrix n n ℂ)) ([A, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_01101100 : Matrix.trace (A * B * B * A * B * B * A * A) =
      Matrix.trace (A * A * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_01101101 : Matrix.trace (A * B * B * A * B * B * A * B) =
      Matrix.trace (A * B * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_01101110 : Matrix.trace (A * B * B * A * B * B * B * A) =
      Matrix.trace (A * A * B * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_01110000 : Matrix.trace (A * B * B * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B] : List (Matrix n n ℂ)) ([A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_01110001 : Matrix.trace (A * B * B * B * A * A * A * B) =
      Matrix.trace (A * A * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B] : List (Matrix n n ℂ)) ([A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_01110010 : Matrix.trace (A * B * B * B * A * A * B * A) =
      Matrix.trace (A * A * B * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B] : List (Matrix n n ℂ)) ([A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_01110011 : Matrix.trace (A * B * B * B * A * A * B * B) =
      Matrix.trace (A * A * B * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B] : List (Matrix n n ℂ)) ([A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_01110100 : Matrix.trace (A * B * B * B * A * B * A * A) =
      Matrix.trace (A * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_01110101 : Matrix.trace (A * B * B * B * A * B * A * B) =
      Matrix.trace (A * B * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B] : List (Matrix n n ℂ)) ([A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_01110110 : Matrix.trace (A * B * B * B * A * B * B * A) =
      Matrix.trace (A * A * B * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, A, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_01111000 : Matrix.trace (A * B * B * B * B * A * A * A) =
      Matrix.trace (A * A * A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_01111001 : Matrix.trace (A * B * B * B * B * A * A * B) =
      Matrix.trace (A * A * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_01111010 : Matrix.trace (A * B * B * B * B * A * B * A) =
      Matrix.trace (A * A * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, B, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_01111011 : Matrix.trace (A * B * B * B * B * A * B * B) =
      Matrix.trace (A * B * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, B] : List (Matrix n n ℂ)) ([A, B, B] : List (Matrix n n ℂ)))

  have hrot_01111100 : Matrix.trace (A * B * B * B * B * B * A * A) =
      Matrix.trace (A * A * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_01111101 : Matrix.trace (A * B * B * B * B * B * A * B) =
      Matrix.trace (A * B * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, B, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_01111110 : Matrix.trace (A * B * B * B * B * B * B * A) =
      Matrix.trace (A * A * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_10000000 : Matrix.trace (B * A * A * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_10000001 : Matrix.trace (B * A * A * A * A * A * A * B) =
      Matrix.trace (A * A * A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_10000010 : Matrix.trace (B * A * A * A * A * A * B * A) =
      Matrix.trace (A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_10000011 : Matrix.trace (B * A * A * A * A * A * B * B) =
      Matrix.trace (A * A * A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_10000100 : Matrix.trace (B * A * A * A * A * B * A * A) =
      Matrix.trace (A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_10000101 : Matrix.trace (B * A * A * A * A * B * A * B) =
      Matrix.trace (A * A * A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_10000110 : Matrix.trace (B * A * A * A * A * B * B * A) =
      Matrix.trace (A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_10000111 : Matrix.trace (B * A * A * A * A * B * B * B) =
      Matrix.trace (A * A * A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_10001000 : Matrix.trace (B * A * A * A * B * A * A * A) =
      Matrix.trace (A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_10001001 : Matrix.trace (B * A * A * A * B * A * A * B) =
      Matrix.trace (A * A * A * B * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_10001010 : Matrix.trace (B * A * A * A * B * A * B * A) =
      Matrix.trace (A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_10001011 : Matrix.trace (B * A * A * A * B * A * B * B) =
      Matrix.trace (A * A * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_10001100 : Matrix.trace (B * A * A * A * B * B * A * A) =
      Matrix.trace (A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_10001101 : Matrix.trace (B * A * A * A * B * B * A * B) =
      Matrix.trace (A * A * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_10001110 : Matrix.trace (B * A * A * A * B * B * B * A) =
      Matrix.trace (A * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_10001111 : Matrix.trace (B * A * A * A * B * B * B * B) =
      Matrix.trace (A * A * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_10010000 : Matrix.trace (B * A * A * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_10010001 : Matrix.trace (B * A * A * B * A * A * A * B) =
      Matrix.trace (A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_10010010 : Matrix.trace (B * A * A * B * A * A * B * A) =
      Matrix.trace (A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_10010011 : Matrix.trace (B * A * A * B * A * A * B * B) =
      Matrix.trace (A * A * B * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_10010100 : Matrix.trace (B * A * A * B * A * B * A * A) =
      Matrix.trace (A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_10010101 : Matrix.trace (B * A * A * B * A * B * A * B) =
      Matrix.trace (A * A * B * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_10010110 : Matrix.trace (B * A * A * B * A * B * B * A) =
      Matrix.trace (A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_10010111 : Matrix.trace (B * A * A * B * A * B * B * B) =
      Matrix.trace (A * A * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_10011000 : Matrix.trace (B * A * A * B * B * A * A * A) =
      Matrix.trace (A * A * A * B * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_10011001 : Matrix.trace (B * A * A * B * B * A * A * B) =
      Matrix.trace (A * A * B * B * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_10011010 : Matrix.trace (B * A * A * B * B * A * B * A) =
      Matrix.trace (A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_10011011 : Matrix.trace (B * A * A * B * B * A * B * B) =
      Matrix.trace (A * A * B * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_10011100 : Matrix.trace (B * A * A * B * B * B * A * A) =
      Matrix.trace (A * A * B * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_10011101 : Matrix.trace (B * A * A * B * B * B * A * B) =
      Matrix.trace (A * A * B * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_10011110 : Matrix.trace (B * A * A * B * B * B * B * A) =
      Matrix.trace (A * A * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_10011111 : Matrix.trace (B * A * A * B * B * B * B * B) =
      Matrix.trace (A * A * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_10100000 : Matrix.trace (B * A * B * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_10100001 : Matrix.trace (B * A * B * A * A * A * A * B) =
      Matrix.trace (A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_10100010 : Matrix.trace (B * A * B * A * A * A * B * A) =
      Matrix.trace (A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_10100011 : Matrix.trace (B * A * B * A * A * A * B * B) =
      Matrix.trace (A * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([A, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_10100100 : Matrix.trace (B * A * B * A * A * B * A * A) =
      Matrix.trace (A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_10100101 : Matrix.trace (B * A * B * A * A * B * A * B) =
      Matrix.trace (A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_10100110 : Matrix.trace (B * A * B * A * A * B * B * A) =
      Matrix.trace (A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_10100111 : Matrix.trace (B * A * B * A * A * B * B * B) =
      Matrix.trace (A * A * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([A, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_10101000 : Matrix.trace (B * A * B * A * B * A * A * A) =
      Matrix.trace (A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_10101001 : Matrix.trace (B * A * B * A * B * A * A * B) =
      Matrix.trace (A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_10101010 : Matrix.trace (B * A * B * A * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_10101011 : Matrix.trace (B * A * B * A * B * A * B * B) =
      Matrix.trace (A * B * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_10101100 : Matrix.trace (B * A * B * A * B * B * A * A) =
      Matrix.trace (A * A * B * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_10101101 : Matrix.trace (B * A * B * A * B * B * A * B) =
      Matrix.trace (A * B * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_10101110 : Matrix.trace (B * A * B * A * B * B * B * A) =
      Matrix.trace (A * B * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_10101111 : Matrix.trace (B * A * B * A * B * B * B * B) =
      Matrix.trace (A * B * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_10110000 : Matrix.trace (B * A * B * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B] : List (Matrix n n ℂ)) ([A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_10110001 : Matrix.trace (B * A * B * B * A * A * A * B) =
      Matrix.trace (A * A * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B] : List (Matrix n n ℂ)) ([A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_10110010 : Matrix.trace (B * A * B * B * A * A * B * A) =
      Matrix.trace (A * A * B * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B] : List (Matrix n n ℂ)) ([A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_10110011 : Matrix.trace (B * A * B * B * A * A * B * B) =
      Matrix.trace (A * A * B * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B] : List (Matrix n n ℂ)) ([A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_10110100 : Matrix.trace (B * A * B * B * A * B * A * A) =
      Matrix.trace (A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_10110101 : Matrix.trace (B * A * B * B * A * B * A * B) =
      Matrix.trace (A * B * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B] : List (Matrix n n ℂ)) ([A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_10110110 : Matrix.trace (B * A * B * B * A * B * B * A) =
      Matrix.trace (A * B * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_10110111 : Matrix.trace (B * A * B * B * A * B * B * B) =
      Matrix.trace (A * B * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, B, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_10111000 : Matrix.trace (B * A * B * B * B * A * A * A) =
      Matrix.trace (A * A * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_10111001 : Matrix.trace (B * A * B * B * B * A * A * B) =
      Matrix.trace (A * A * B * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_10111010 : Matrix.trace (B * A * B * B * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, B] : List (Matrix n n ℂ)) ([A, B, A] : List (Matrix n n ℂ)))

  have hrot_10111011 : Matrix.trace (B * A * B * B * B * A * B * B) =
      Matrix.trace (A * B * B * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_10111100 : Matrix.trace (B * A * B * B * B * B * A * A) =
      Matrix.trace (A * A * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_10111101 : Matrix.trace (B * A * B * B * B * B * A * B) =
      Matrix.trace (A * B * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, B, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_10111110 : Matrix.trace (B * A * B * B * B * B * B * A) =
      Matrix.trace (A * B * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_10111111 : Matrix.trace (B * A * B * B * B * B * B * B) =
      Matrix.trace (A * B * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_11000000 : Matrix.trace (B * B * A * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_11000001 : Matrix.trace (B * B * A * A * A * A * A * B) =
      Matrix.trace (A * A * A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_11000010 : Matrix.trace (B * B * A * A * A * A * B * A) =
      Matrix.trace (A * A * A * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_11000011 : Matrix.trace (B * B * A * A * A * A * B * B) =
      Matrix.trace (A * A * A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_11000100 : Matrix.trace (B * B * A * A * A * B * A * A) =
      Matrix.trace (A * A * A * B * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_11000101 : Matrix.trace (B * B * A * A * A * B * A * B) =
      Matrix.trace (A * A * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_11000110 : Matrix.trace (B * B * A * A * A * B * B * A) =
      Matrix.trace (A * A * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_11000111 : Matrix.trace (B * B * A * A * A * B * B * B) =
      Matrix.trace (A * A * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_11001000 : Matrix.trace (B * B * A * A * B * A * A * A) =
      Matrix.trace (A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_11001001 : Matrix.trace (B * B * A * A * B * A * A * B) =
      Matrix.trace (A * A * B * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_11001010 : Matrix.trace (B * B * A * A * B * A * B * A) =
      Matrix.trace (A * A * B * A * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_11001011 : Matrix.trace (B * B * A * A * B * A * B * B) =
      Matrix.trace (A * A * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_11001100 : Matrix.trace (B * B * A * A * B * B * A * A) =
      Matrix.trace (A * A * B * B * A * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_11001101 : Matrix.trace (B * B * A * A * B * B * A * B) =
      Matrix.trace (A * A * B * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_11001110 : Matrix.trace (B * B * A * A * B * B * B * A) =
      Matrix.trace (A * A * B * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_11001111 : Matrix.trace (B * B * A * A * B * B * B * B) =
      Matrix.trace (A * A * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, A, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_11010000 : Matrix.trace (B * B * A * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_11010001 : Matrix.trace (B * B * A * B * A * A * A * B) =
      Matrix.trace (A * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_11010010 : Matrix.trace (B * B * A * B * A * A * B * A) =
      Matrix.trace (A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_11010011 : Matrix.trace (B * B * A * B * A * A * B * B) =
      Matrix.trace (A * A * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_11010100 : Matrix.trace (B * B * A * B * A * B * A * A) =
      Matrix.trace (A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_11010101 : Matrix.trace (B * B * A * B * A * B * A * B) =
      Matrix.trace (A * B * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_11010110 : Matrix.trace (B * B * A * B * A * B * B * A) =
      Matrix.trace (A * B * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_11010111 : Matrix.trace (B * B * A * B * A * B * B * B) =
      Matrix.trace (A * B * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, B, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_11011000 : Matrix.trace (B * B * A * B * B * A * A * A) =
      Matrix.trace (A * A * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_11011001 : Matrix.trace (B * B * A * B * B * A * A * B) =
      Matrix.trace (A * A * B * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_11011010 : Matrix.trace (B * B * A * B * B * A * B * A) =
      Matrix.trace (A * B * A * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B] : List (Matrix n n ℂ)) ([A, B, A] : List (Matrix n n ℂ)))

  have hrot_11011011 : Matrix.trace (B * B * A * B * B * A * B * B) =
      Matrix.trace (A * B * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_11011100 : Matrix.trace (B * B * A * B * B * B * A * A) =
      Matrix.trace (A * A * B * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_11011101 : Matrix.trace (B * B * A * B * B * B * A * B) =
      Matrix.trace (A * B * B * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_11011110 : Matrix.trace (B * B * A * B * B * B * B * A) =
      Matrix.trace (A * B * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_11011111 : Matrix.trace (B * B * A * B * B * B * B * B) =
      Matrix.trace (A * B * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B] : List (Matrix n n ℂ)) ([A, B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_11100000 : Matrix.trace (B * B * B * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_11100001 : Matrix.trace (B * B * B * A * A * A * A * B) =
      Matrix.trace (A * A * A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_11100010 : Matrix.trace (B * B * B * A * A * A * B * A) =
      Matrix.trace (A * A * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_11100011 : Matrix.trace (B * B * B * A * A * A * B * B) =
      Matrix.trace (A * A * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_11100100 : Matrix.trace (B * B * B * A * A * B * A * A) =
      Matrix.trace (A * A * B * A * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_11100101 : Matrix.trace (B * B * B * A * A * B * A * B) =
      Matrix.trace (A * A * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_11100110 : Matrix.trace (B * B * B * A * A * B * B * A) =
      Matrix.trace (A * A * B * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_11100111 : Matrix.trace (B * B * B * A * A * B * B * B) =
      Matrix.trace (A * A * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_11101000 : Matrix.trace (B * B * B * A * B * A * A * A) =
      Matrix.trace (A * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_11101001 : Matrix.trace (B * B * B * A * B * A * A * B) =
      Matrix.trace (A * A * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_11101010 : Matrix.trace (B * B * B * A * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_11101011 : Matrix.trace (B * B * B * A * B * A * B * B) =
      Matrix.trace (A * B * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_11101100 : Matrix.trace (B * B * B * A * B * B * A * A) =
      Matrix.trace (A * A * B * B * B * A * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_11101101 : Matrix.trace (B * B * B * A * B * B * A * B) =
      Matrix.trace (A * B * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_11101110 : Matrix.trace (B * B * B * A * B * B * B * A) =
      Matrix.trace (A * B * B * B * A * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_11101111 : Matrix.trace (B * B * B * A * B * B * B * B) =
      Matrix.trace (A * B * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B] : List (Matrix n n ℂ)) ([A, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_11110000 : Matrix.trace (B * B * B * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B] : List (Matrix n n ℂ)) ([A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_11110001 : Matrix.trace (B * B * B * B * A * A * A * B) =
      Matrix.trace (A * A * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B] : List (Matrix n n ℂ)) ([A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_11110010 : Matrix.trace (B * B * B * B * A * A * B * A) =
      Matrix.trace (A * A * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B] : List (Matrix n n ℂ)) ([A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_11110011 : Matrix.trace (B * B * B * B * A * A * B * B) =
      Matrix.trace (A * A * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B] : List (Matrix n n ℂ)) ([A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_11110100 : Matrix.trace (B * B * B * B * A * B * A * A) =
      Matrix.trace (A * A * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_11110101 : Matrix.trace (B * B * B * B * A * B * A * B) =
      Matrix.trace (A * B * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B] : List (Matrix n n ℂ)) ([A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_11110110 : Matrix.trace (B * B * B * B * A * B * B * A) =
      Matrix.trace (A * B * B * A * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B] : List (Matrix n n ℂ)) ([A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_11110111 : Matrix.trace (B * B * B * B * A * B * B * B) =
      Matrix.trace (A * B * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B] : List (Matrix n n ℂ)) ([A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_11111000 : Matrix.trace (B * B * B * B * B * A * A * A) =
      Matrix.trace (A * A * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_11111001 : Matrix.trace (B * B * B * B * B * A * A * B) =
      Matrix.trace (A * A * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_11111010 : Matrix.trace (B * B * B * B * B * A * B * A) =
      Matrix.trace (A * B * A * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B] : List (Matrix n n ℂ)) ([A, B, A] : List (Matrix n n ℂ)))

  have hrot_11111011 : Matrix.trace (B * B * B * B * B * A * B * B) =
      Matrix.trace (A * B * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B] : List (Matrix n n ℂ)) ([A, B, B] : List (Matrix n n ℂ)))

  have hrot_11111100 : Matrix.trace (B * B * B * B * B * B * A * A) =
      Matrix.trace (A * A * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_11111101 : Matrix.trace (B * B * B * B * B * B * A * B) =
      Matrix.trace (A * B * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_11111110 : Matrix.trace (B * B * B * B * B * B * B * A) =
      Matrix.trace (A * B * B * B * B * B * B * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B, B, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))
  simp [orderedWordExpansion, List.map_append, List.sum_append]
  rw [
    hrot_00000010,
    hrot_00000100,
    hrot_00000110,
    hrot_00001000,
    hrot_00001010,
    hrot_00001100,
    hrot_00001110,
    hrot_00010000,
    hrot_00010010,
    hrot_00010100,
    hrot_00010110,
    hrot_00011000,
    hrot_00011010,
    hrot_00011100,
    hrot_00011110,
    hrot_00100000,
    hrot_00100001,
    hrot_00100010,
    hrot_00100011,
    hrot_00100100,
    hrot_00100110,
    hrot_00101000,
    hrot_00101001,
    hrot_00101010,
    hrot_00101100,
    hrot_00101110,
    hrot_00110000,
    hrot_00110001,
    hrot_00110010,
    hrot_00110100,
    hrot_00110110,
    hrot_00111000,
    hrot_00111001,
    hrot_00111010,
    hrot_00111100,
    hrot_00111110,
    hrot_01000000,
    hrot_01000001,
    hrot_01000010,
    hrot_01000011,
    hrot_01000100,
    hrot_01000101,
    hrot_01000110,
    hrot_01000111,
    hrot_01001000,
    hrot_01001001,
    hrot_01001010,
    hrot_01001011,
    hrot_01001100,
    hrot_01001101,
    hrot_01001110,
    hrot_01001111,
    hrot_01010000,
    hrot_01010001,
    hrot_01010010,
    hrot_01010011,
    hrot_01010100,
    hrot_01010110,
    hrot_01011000,
    hrot_01011001,
    hrot_01011010,
    hrot_01011100,
    hrot_01011101,
    hrot_01011110,
    hrot_01100000,
    hrot_01100001,
    hrot_01100010,
    hrot_01100011,
    hrot_01100100,
    hrot_01100101,
    hrot_01100110,
    hrot_01100111,
    hrot_01101000,
    hrot_01101001,
    hrot_01101010,
    hrot_01101011,
    hrot_01101100,
    hrot_01101101,
    hrot_01101110,
    hrot_01110000,
    hrot_01110001,
    hrot_01110010,
    hrot_01110011,
    hrot_01110100,
    hrot_01110101,
    hrot_01110110,
    hrot_01111000,
    hrot_01111001,
    hrot_01111010,
    hrot_01111011,
    hrot_01111100,
    hrot_01111101,
    hrot_01111110,
    hrot_10000000,
    hrot_10000001,
    hrot_10000010,
    hrot_10000011,
    hrot_10000100,
    hrot_10000101,
    hrot_10000110,
    hrot_10000111,
    hrot_10001000,
    hrot_10001001,
    hrot_10001010,
    hrot_10001011,
    hrot_10001100,
    hrot_10001101,
    hrot_10001110,
    hrot_10001111,
    hrot_10010000,
    hrot_10010001,
    hrot_10010010,
    hrot_10010011,
    hrot_10010100,
    hrot_10010101,
    hrot_10010110,
    hrot_10010111,
    hrot_10011000,
    hrot_10011001,
    hrot_10011010,
    hrot_10011011,
    hrot_10011100,
    hrot_10011101,
    hrot_10011110,
    hrot_10011111,
    hrot_10100000,
    hrot_10100001,
    hrot_10100010,
    hrot_10100011,
    hrot_10100100,
    hrot_10100101,
    hrot_10100110,
    hrot_10100111,
    hrot_10101000,
    hrot_10101001,
    hrot_10101010,
    hrot_10101011,
    hrot_10101100,
    hrot_10101101,
    hrot_10101110,
    hrot_10101111,
    hrot_10110000,
    hrot_10110001,
    hrot_10110010,
    hrot_10110011,
    hrot_10110100,
    hrot_10110101,
    hrot_10110110,
    hrot_10110111,
    hrot_10111000,
    hrot_10111001,
    hrot_10111010,
    hrot_10111011,
    hrot_10111100,
    hrot_10111101,
    hrot_10111110,
    hrot_10111111,
    hrot_11000000,
    hrot_11000001,
    hrot_11000010,
    hrot_11000011,
    hrot_11000100,
    hrot_11000101,
    hrot_11000110,
    hrot_11000111,
    hrot_11001000,
    hrot_11001001,
    hrot_11001010,
    hrot_11001011,
    hrot_11001100,
    hrot_11001101,
    hrot_11001110,
    hrot_11001111,
    hrot_11010000,
    hrot_11010001,
    hrot_11010010,
    hrot_11010011,
    hrot_11010100,
    hrot_11010101,
    hrot_11010110,
    hrot_11010111,
    hrot_11011000,
    hrot_11011001,
    hrot_11011010,
    hrot_11011011,
    hrot_11011100,
    hrot_11011101,
    hrot_11011110,
    hrot_11011111,
    hrot_11100000,
    hrot_11100001,
    hrot_11100010,
    hrot_11100011,
    hrot_11100100,
    hrot_11100101,
    hrot_11100110,
    hrot_11100111,
    hrot_11101000,
    hrot_11101001,
    hrot_11101010,
    hrot_11101011,
    hrot_11101100,
    hrot_11101101,
    hrot_11101110,
    hrot_11101111,
    hrot_11110000,
    hrot_11110001,
    hrot_11110010,
    hrot_11110011,
    hrot_11110100,
    hrot_11110101,
    hrot_11110110,
    hrot_11110111,
    hrot_11111000,
    hrot_11111001,
    hrot_11111010,
    hrot_11111011,
    hrot_11111100,
    hrot_11111101,
    hrot_11111110
  ]
  ring








/-- Two-index expansion of a trace with diagonal middle and right factors.
No commutation of the kernel is assumed: the ordered factors
`K x y` and `K y x` remain distinct. This is the finite-sum identity
needed before support hypotheses can collapse a boundary trace. -/
theorem trace_kernel_diagonal_kernel_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (a d : n → ℂ) :
    Matrix.trace (K * Matrix.diagonal a * K * Matrix.diagonal d) =
      ∑ x, ∑ y, K x y * a y * K y x * d x := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply,
    Finset.mul_sum, mul_assoc]


/-- Collapse the two-index trace expansion to its diagonal terms when both
diagonal weights are supported on a locus where K has no off-diagonal
entries. This is the precise support-sensitive step used by boundary trace
reductions; no symmetry of K is assumed. -/
theorem trace_kernel_diagonal_kernel_diagonal_collapse
    {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (g : n → Prop) [DecidablePred g]
    (a d : n → ℂ)
    (ha : ∀ x, ¬ g x → a x = 0)
    (hd : ∀ x, ¬ g x → d x = 0)
    (hK : ∀ x y, g x → g y → x ≠ y → K x y = 0) :
    Matrix.trace (K * Matrix.diagonal a * K * Matrix.diagonal d) =
      ∑ x, if g x then K x x * a x * K x x * d x else 0 := by
  classical
  rw [trace_kernel_diagonal_kernel_diagonal]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hgx : g x
  · simp only [if_pos hgx]
    rw [Finset.sum_eq_single x]
    · intro y hy hne
      by_cases hgy : g y
      · have hxy : K x y = 0 := hK x y hgx hgy (Ne.symm hne)
        have hyx : K y x = 0 := hK y x hgy hgx hne
        simp [hxy, hyx]
      · simp [ha y hgy]
    · simp
  · simp [hgx, hd x hgx]


end EvgenyTheorem

namespace EvgenyTheorem

/-- The p-fold ordered expansion restricted to words with exactly `r`
uses of the second letter. The recurrence splits by the last factor:
words ending in A come first, followed by words ending in B. Therefore
the relative order and multiplicity of all matrix words in each stratum
are preserved, including when different words have equal matrix products. -/
def orderedWordExpansionByCount {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) : ℕ → ℕ → List (Matrix n n ℂ)
  | 0, 0 => [1]
  | 0, r + 1 => []
  | p + 1, 0 =>
      (orderedWordExpansionByCount A B p 0).map (fun X => X * A)
  | p + 1, r + 1 =>
      (orderedWordExpansionByCount A B p (r + 1)).map (fun X => X * A) ++
      (orderedWordExpansionByCount A B p r).map (fun X => X * B)

/-- The r-stratum contains exactly binomial(p,r) ordered word occurrences.
This counts multiplicities, not distinct matrix values. -/
theorem orderedWordExpansionByCount_length
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (p r : ℕ) :
    (orderedWordExpansionByCount A B p r).length = Nat.choose p r := by
  induction p generalizing r with
  | zero =>
      cases r with
      | zero => simp [orderedWordExpansionByCount]
      | succ r => simp [orderedWordExpansionByCount]
  | succ p ih =>
      cases r with
      | zero =>
          simp [orderedWordExpansionByCount, ih]
      | succ r =>
          simp only [orderedWordExpansionByCount, List.length_append,
            List.length_map, ih]
          rw [Nat.choose_succ_succ]
          exact Nat.add_comm _ _

/-- Small-degree census checks for the recursive count stratification. -/
theorem orderedWordExpansionByCount_small_length_checks
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    (orderedWordExpansionByCount A B 2 0).length = 1 ∧
    (orderedWordExpansionByCount A B 2 1).length = 2 ∧
    (orderedWordExpansionByCount A B 2 2).length = 1 ∧
    (orderedWordExpansionByCount A B 3 1).length = 3 ∧
    (orderedWordExpansionByCount A B 3 2).length = 3 := by
  simp [orderedWordExpansionByCount_length]

end EvgenyTheorem


namespace EvgenyTheorem

/-- A count stratum above the word length is empty, by its exact
binomial-length formula. -/
theorem orderedWordExpansionByCount_eq_nil_of_lt
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (p r : ℕ) (hpr : p < r) :
    orderedWordExpansionByCount A B p r = [] := by
  cases hW : orderedWordExpansionByCount A B p r with
  | nil => rfl
  | cons x xs =>
      have hlen := orderedWordExpansionByCount_length A B p r
      have hfalse : False := by
        simpa [hW, Nat.choose_eq_zero_of_lt hpr] using hlen
      exact hfalse.elim

/-- Summing the exact-count strata reconstructs the full noncommutative
power. The induction follows the last-factor recurrence; matrix factors
are never commuted and repeated word occurrences are retained. -/
theorem orderedWordExpansionByCount_sum_eq_pow
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (p : ℕ) :
    (∑ r ∈ Finset.range (p + 1),
      (orderedWordExpansionByCount A B p r).sum) = (A + B) ^ p := by
  induction p with
  | zero =>
      simp [orderedWordExpansionByCount]
  | succ p ih =>
      rw [Finset.sum_range_succ']
      simp only [orderedWordExpansionByCount, List.sum_append,
        matrix_list_sum_map_mul_right]
      have hzero :
          orderedWordExpansionByCount A B p (p + 1) = [] :=
        orderedWordExpansionByCount_eq_nil_of_lt A B p (p + 1)
          (Nat.lt_succ_self p)
      have hShift :
          (∑ r ∈ Finset.range (p + 1),
            (orderedWordExpansionByCount A B p (r + 1)).sum) =
          ∑ r ∈ Finset.range p,
            (orderedWordExpansionByCount A B p (r + 1)).sum := by
        rw [Finset.sum_range_succ]
        simp [hzero]
      have hA :
          (orderedWordExpansionByCount A B p 0).sum * A +
            (∑ r ∈ Finset.range (p + 1),
              (orderedWordExpansionByCount A B p (r + 1)).sum) * A =
          (∑ r ∈ Finset.range (p + 1),
            (orderedWordExpansionByCount A B p r).sum) * A := by
        calc
          _ = ((orderedWordExpansionByCount A B p 0).sum +
                ∑ r ∈ Finset.range p,
                  (orderedWordExpansionByCount A B p (r + 1)).sum) * A := by
            rw [hShift, ← add_mul]
          _ = (∑ r ∈ Finset.range (p + 1),
                (orderedWordExpansionByCount A B p r).sum) * A := by
            rw [Finset.sum_range_succ']
            congr 1
            exact add_comm _ _
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      calc
        _ = ((orderedWordExpansionByCount A B p 0).sum * A +
              (∑ r ∈ Finset.range (p + 1),
                (orderedWordExpansionByCount A B p (r + 1)).sum) * A) +
            (∑ r ∈ Finset.range (p + 1),
              (orderedWordExpansionByCount A B p r).sum) * B := by
          abel
        _ = (A + B) ^ (p + 1) := by
          rw [hA, ← mul_add, ih, ← pow_succ]


/-- Trace-level reconstruction from exact-count strata. The outer finite sum
is passed through the additive matrix trace, and each stratum list is passed
through the existing list trace identity. This keeps every ordered word
occurrence and its multiplicity; it does not yet group cyclic orbits. -/
theorem trace_orderedWordExpansionByCount_sum_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (p : ℕ) :
    Matrix.trace ((A + B) ^ p) =
      ∑ r ∈ Finset.range (p + 1),
        ((orderedWordExpansionByCount A B p r).map Matrix.trace).sum := by
  rw [← orderedWordExpansionByCount_sum_eq_pow]
  rw [Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact trace_sum_list (orderedWordExpansionByCount A B p r)


/-- The trace of a cyclic gap word. A gap of length a contributes the
ordered block K^a * N; the list order is retained in the product. -/
def cyclicGapTrace {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (gaps : List ℕ) : ℂ :=
  Matrix.trace ((gaps.map (fun a => K ^ a * N)).prod)

/-- Rotating the gap list rotates the corresponding matrix blocks inside
the trace. This uses only cyclicity of trace, not commutation of K and N. -/
theorem cyclicGapTrace_rotate
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (gaps : List ℕ) (k : ℕ) :
    cyclicGapTrace K N (gaps.rotate k) = cyclicGapTrace K N gaps := by
  classical
  unfold cyclicGapTrace
  rw [List.map_rotate]
  let blocks : List (Matrix n n ℂ) := gaps.map (fun a => K ^ a * N)
  change Matrix.trace ((blocks.rotate k).prod) = Matrix.trace blocks.prod
  let j := k % blocks.length
  have hsplit : blocks.take j ++ blocks.drop j = blocks :=
    List.take_append_drop j blocks
  calc
    Matrix.trace ((blocks.rotate k).prod) =
        Matrix.trace ((blocks.drop j).prod * (blocks.take j).prod) := by
          rw [List.rotate_eq_drop_append_take_mod, List.prod_append]
    _ = Matrix.trace ((blocks.take j).prod * (blocks.drop j).prod) := by
          exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace blocks.prod := by
          have hprod :
              (blocks.take j).prod * (blocks.drop j).prod = blocks.prod := by
            calc
              _ = (blocks.take j ++ blocks.drop j).prod := by
                rw [List.prod_append]
              _ = blocks.prod := by
                rw [List.take_append_drop]
          rw [← hprod]

/-- Distinct cyclic rotations of a gap list. Passing to a Finset removes
repeated rotations, so its cardinality is the true orbit size, including
periodic tuples whose stabilizer is nontrivial. -/
def cyclicGapOrbit (gaps : List ℕ) : Finset (List ℕ) :=
  (List.cyclicPermutations gaps).toFinset

/-- Every member of a cyclic gap orbit has the same trace. -/
theorem cyclicGapTrace_eq_of_mem_orbit
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) {gaps rotated : List ℕ}
    (hrotated : rotated ∈ cyclicGapOrbit gaps) :
    cyclicGapTrace K N rotated = cyclicGapTrace K N gaps := by
  classical
  have hrot : rotated ~r gaps := by
    simpa [cyclicGapOrbit] using hrotated
  rcases hrot with ⟨k, hk⟩
  calc
    cyclicGapTrace K N rotated =
        cyclicGapTrace K N (rotated.rotate k) := by
          symm
          exact cyclicGapTrace_rotate K N rotated k
    _ = cyclicGapTrace K N gaps := by rw [hk]

/-- Summing over a cyclic orbit counts each distinct gap tuple once.
The multiplier is the orbit cardinality, not the tuple length; this is
the source of the reduced weights for periodic p=10 compositions. -/
theorem cyclicGapTrace_sum_orbit_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (gaps : List ℕ) :
    (∑ g ∈ cyclicGapOrbit gaps, cyclicGapTrace K N g) =
      (cyclicGapOrbit gaps).card • cyclicGapTrace K N gaps := by
  classical
  calc
    (∑ g ∈ cyclicGapOrbit gaps, cyclicGapTrace K N g) =
        ∑ _g ∈ cyclicGapOrbit gaps, cyclicGapTrace K N gaps := by
          apply Finset.sum_congr rfl
          intro g hg
          exact cyclicGapTrace_eq_of_mem_orbit K N hg
    _ = (cyclicGapOrbit gaps).card • cyclicGapTrace K N gaps := by simp

/-- The two p=10 period-two four-gap representatives have two distinct
cyclic rotations, rather than four. This records the stabilizer correction
behind their weight five (10/4 times orbit size two). -/
theorem cyclicGapOrbit_four_period_two_card :
    (cyclicGapOrbit [1, 4, 1, 4]).card = 2 ∧
    (cyclicGapOrbit [2, 3, 2, 3]).card = 2 := by
  decide

/-- The p=10 six-gap period-three representatives have orbit size three,
which yields weight five (10/6 times orbit size three). -/
theorem cyclicGapOrbit_six_period_three_card :
    (cyclicGapOrbit [1, 1, 3, 1, 1, 3]).card = 3 ∧
    (cyclicGapOrbit [1, 2, 2, 1, 2, 2]).card = 3 := by
  decide

/-- The p=10 eight-gap period-four representative has four distinct
cyclic rotations, giving the reduced weight five (10/8 times four). -/
theorem cyclicGapOrbit_eight_period_four_card :
    (cyclicGapOrbit [1, 1, 1, 2, 1, 1, 1, 2]).card = 4 := by
  decide

/-- The all-equal p=10 ten-gap tuple has a one-element orbit. -/
theorem cyclicGapOrbit_ten_period_one_card :
    (cyclicGapOrbit (List.replicate 10 1)).card = 1 := by
  decide


/-- Symbolic binary words with exactly r occurrences of the second letter.
The recursion appends the final bit, matching the order of
`orderedWordExpansionByCount`: words ending in false precede those ending
in true. The list retains occurrences rather than quotienting by value. -/
def binaryWordExpansionByCount : ℕ → ℕ → List (List Bool)
  | 0, 0 => [[]]
  | 0, r + 1 => []
  | p + 1, 0 =>
      (binaryWordExpansionByCount p 0).map (fun w => w ++ [false])
  | p + 1, r + 1 =>
      (binaryWordExpansionByCount p (r + 1)).map (fun w => w ++ [false]) ++
      (binaryWordExpansionByCount p r).map (fun w => w ++ [true])

/-- Evaluate a symbolic binary word in the two noncommuting matrix letters.
The left-to-right product follows the word order exactly. -/
def binaryWordMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (w : List Bool) : Matrix n n ℂ :=
  (w.map (fun bit => if bit then B else A)).prod

/-- Appending one symbolic letter appends the corresponding matrix factor
on the right; no commutation is used. -/
theorem binaryWordMatrix_append
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (w : List Bool) (bit : Bool) :
    binaryWordMatrix A B (w ++ [bit]) =
      binaryWordMatrix A B w * (if bit then B else A) := by
  simp [binaryWordMatrix, List.map_append, List.prod_append]

/-- The exact-count matrix-word list is the image, occurrence by occurrence,
of the symbolic binary-word list under evaluation in A and B. This exposes
the positions of the B letters without losing multiplicities when two
different binary words evaluate to the same matrix. -/
theorem orderedWordExpansionByCount_eq_map_binaryWordExpansionByCount
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (p r : ℕ) :
    orderedWordExpansionByCount A B p r =
      (binaryWordExpansionByCount p r).map (binaryWordMatrix A B) := by
  induction p generalizing r with
  | zero =>
      cases r with
      | zero =>
          simp [binaryWordExpansionByCount, orderedWordExpansionByCount,
            binaryWordMatrix]
      | succ r =>
          simp [binaryWordExpansionByCount, orderedWordExpansionByCount]
  | succ p ih =>
      cases r with
      | zero =>
          simp only [orderedWordExpansionByCount, binaryWordExpansionByCount,
            ih 0, List.map_map]
          apply List.map_congr_left
          intro w hw
          exact (binaryWordMatrix_append A B w false).symm
      | succ r =>
          simp only [orderedWordExpansionByCount, binaryWordExpansionByCount,
            ih (r + 1), ih r, List.map_append, List.map_map]
          apply congrArg₂ List.append
          · apply List.map_congr_left
            intro w hw
            exact (binaryWordMatrix_append A B w false).symm
          · apply List.map_congr_left
            intro w hw
            exact (binaryWordMatrix_append A B w true).symm

/-- Trace-level symbolic form of an exact-count stratum. It is the starting
point for marking one of the r occurrences of B and cutting the word there. -/
theorem trace_orderedWordExpansionByCount_eq_binaryWordExpansionByCount
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (p r : ℕ) :
    ((orderedWordExpansionByCount A B p r).map Matrix.trace).sum =
      ((binaryWordExpansionByCount p r).map
        (fun w => Matrix.trace (binaryWordMatrix A B w))).sum := by
  rw [orderedWordExpansionByCount_eq_map_binaryWordExpansionByCount]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro w hw
  rfl


/-- A finite run of first-letter symbols, representing one gap before a
marked occurrence of the second letter. -/
def binaryFalseRun : ℕ → List Bool
  | 0 => []
  | a + 1 => false :: binaryFalseRun a

/-- Encode a list of nonnegative gaps as the canonical binary word
`false^a₁ true ... false^aᵣ true`. Thus each gap records the number of
A-factors immediately preceding its corresponding B-factor. -/
def binaryWordGapEncoding (gaps : List ℕ) : List Bool :=
  gaps.flatMap (fun a => binaryFalseRun a ++ [true])

/-- The false run has exactly its specified length. -/
theorem binaryFalseRun_length (a : ℕ) :
    (binaryFalseRun a).length = a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [binaryFalseRun, ih]

/-- The encoded word has one B for each gap and one A for each unit of
total gap size, so its length is sum(gaps) + length(gaps). -/
theorem binaryWordGapEncoding_length (gaps : List ℕ) :
    (binaryWordGapEncoding gaps).length = gaps.sum + gaps.length := by
  induction gaps with
  | nil => rfl
  | cons a rest ih =>
      change ((binaryFalseRun a ++ [true]) ++
        binaryWordGapEncoding rest).length =
        (a + rest.sum) + (rest.length + 1)
      simp only [List.length_append, binaryFalseRun_length,
        List.length_cons, List.length_nil, ih]
      omega

/-- The false run contains no true symbols. -/
theorem binaryFalseRun_filter_true (a : ℕ) :
    (binaryFalseRun a).filter id = [] := by
  induction a with
  | zero => rfl
  | succ a ih => simp [binaryFalseRun, ih]

/-- Filtering a false run for false symbols leaves it unchanged. -/
theorem binaryFalseRun_filter_false (a : ℕ) :
    (binaryFalseRun a).filter (fun b => !b) = binaryFalseRun a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [binaryFalseRun, ih]

/-- The true symbols in a canonical gap word are exactly its delimiters:
one final true symbol for each gap. -/
theorem binaryWordGapEncoding_filter_true (gaps : List ℕ) :
    (binaryWordGapEncoding gaps).filter id =
      List.replicate gaps.length true := by
  induction gaps with
  | nil => rfl
  | cons a rest ih =>
      change ((binaryFalseRun a ++ [true]) ++
        binaryWordGapEncoding rest).filter id =
        List.replicate (rest.length + 1) true
      simp [binaryFalseRun_filter_true, ih, List.replicate_succ]

/-- The false symbols in a canonical gap word are precisely the false runs
that encode its gap lengths. -/
theorem binaryWordGapEncoding_filter_false (gaps : List ℕ) :
    (binaryWordGapEncoding gaps).filter (fun b => !b) =
      gaps.flatMap binaryFalseRun := by
  induction gaps with
  | nil => rfl
  | cons a rest ih =>
      change ((binaryFalseRun a ++ [true]) ++
        binaryWordGapEncoding rest).filter (fun b => !b) =
        binaryFalseRun a ++ rest.flatMap binaryFalseRun
      simp [binaryFalseRun_filter_false, ih]

/-- Consequently, a gap encoding has exactly one true symbol per gap. -/
theorem binaryWordGapEncoding_true_count (gaps : List ℕ) :
    ((binaryWordGapEncoding gaps).filter id).length = gaps.length := by
  rw [binaryWordGapEncoding_filter_true]
  simp

/-- And it has exactly the sum of its gap lengths many false symbols. -/
theorem binaryWordGapEncoding_false_count (gaps : List ℕ) :
    ((binaryWordGapEncoding gaps).filter (fun b => !b)).length = gaps.sum := by
  rw [binaryWordGapEncoding_filter_false]
  induction gaps with
  | nil => rfl
  | cons a rest ih =>
      simp [binaryFalseRun_length, ih]


/-- The initial false run before a true delimiter is recovered by
taking the maximal prefix of false symbols. -/
theorem binaryFalseRun_takeWhile_before_true
    (a : ℕ) (tail : List Bool) :
    ((binaryFalseRun a ++ [true]) ++ tail).takeWhile
      (fun bit => !bit) = binaryFalseRun a := by
  induction a with
  | zero => simp [binaryFalseRun]
  | succ a ih =>
      change (false :: ((binaryFalseRun a ++ [true]) ++ tail)).takeWhile
        (fun bit => !bit) = false :: binaryFalseRun a
      change false :: (((binaryFalseRun a ++ [true]) ++ tail).takeWhile
        (fun bit => !bit)) = false :: binaryFalseRun a
      exact congrArg (List.cons false) ih

/-- Reading up to the first true delimiter in a nonempty gap encoding
recovers exactly its first false run. -/
theorem binaryWordGapEncoding_takeWhile_false_cons
    (a : ℕ) (rest : List ℕ) :
    (binaryWordGapEncoding (a :: rest)).takeWhile
      (fun bit => !bit) = binaryFalseRun a := by
  change ((binaryFalseRun a ++ [true]) ++
    binaryWordGapEncoding rest).takeWhile (fun bit => !bit) =
      binaryFalseRun a
  exact binaryFalseRun_takeWhile_before_true a _

/-- The canonical gap encoding is injective: its first false run determines
the first gap, and removing that run together with its true delimiter leaves
the encoding of the remaining gaps. Thus the list representation is unique. -/
theorem binaryWordGapEncoding_injective :
    Function.Injective binaryWordGapEncoding := by
  intro gaps₁ gaps₂ h
  induction gaps₁ generalizing gaps₂ with
  | nil =>
      cases gaps₂ with
      | nil => rfl
      | cons b tail =>
          have hcount := congrArg
            (fun w : List Bool => (w.filter id).length) h
          simp only [binaryWordGapEncoding_true_count,
            List.length_nil, List.length_cons] at hcount
          omega
  | cons a rest ih =>
      cases gaps₂ with
      | nil =>
          have hcount := congrArg
            (fun w : List Bool => (w.filter id).length) h
          simp only [binaryWordGapEncoding_true_count,
            List.length_nil, List.length_cons] at hcount
          omega
      | cons b tail =>
          have hfirst := congrArg
            (fun w : List Bool => w.takeWhile (fun bit => !bit)) h
          rw [binaryWordGapEncoding_takeWhile_false_cons a rest,
            binaryWordGapEncoding_takeWhile_false_cons b tail] at hfirst
          have hab : a = b := by
            have hlen := congrArg List.length hfirst
            simpa only [binaryFalseRun_length] using hlen
          subst b
          have h' :
              (binaryFalseRun a ++ [true]) ++
                  binaryWordGapEncoding rest =
                (binaryFalseRun a ++ [true]) ++
                  binaryWordGapEncoding tail := by
            change binaryWordGapEncoding (a :: rest) =
              binaryWordGapEncoding (a :: tail) at h
            exact h
          have htail := List.append_inj_right h' (by rfl)
          exact congrArg (fun xs : List ℕ => a :: xs) (ih htail)

/-- Decode a binary word by counting the false symbols since the previous
true delimiter. A pending run is emitted exactly when a true symbol is read;
an incomplete final run is deliberately ignored. -/
def binaryWordGapDecodeAux : ℕ → List Bool → List ℕ
  | _, [] => []
  | run, false :: rest => binaryWordGapDecodeAux (run + 1) rest
  | run, true :: rest => run :: binaryWordGapDecodeAux 0 rest

/-- Decode the completed false-runs of a binary word, starting with no
pending false symbols. -/
def binaryWordGapDecode (word : List Bool) : List ℕ :=
  binaryWordGapDecodeAux 0 word

/-- The number of decoded gaps is exactly the number of true delimiters,
even when the input has an unfinished false run at its end. -/
theorem binaryWordGapDecodeAux_length (run : ℕ) (word : List Bool) :
    (binaryWordGapDecodeAux run word).length =
      (word.filter id).length := by
  induction word generalizing run with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp [binaryWordGapDecodeAux, ih]

/-- In particular, decoding preserves the number of true symbols. -/
theorem binaryWordGapDecode_true_count (word : List Bool) :
    (binaryWordGapDecode word).length = (word.filter id).length := by
  simpa [binaryWordGapDecode] using
    (binaryWordGapDecodeAux_length 0 word)

/-- Scanning a false run followed by its true delimiter emits one gap,
adding the run length to any false symbols already accumulated. -/
theorem binaryWordGapDecodeAux_falseRun_block
    (run a : ℕ) (tail : List Bool) :
    binaryWordGapDecodeAux run
      ((binaryFalseRun a ++ [true]) ++ tail) =
        (run + a) :: binaryWordGapDecodeAux 0 tail := by
  induction a generalizing run with
  | zero =>
      simp [binaryFalseRun, binaryWordGapDecodeAux]
  | succ a ih =>
      change binaryWordGapDecodeAux (run + 1)
        ((binaryFalseRun a ++ [true]) ++ tail) =
          (run + (a + 1)) :: binaryWordGapDecodeAux 0 tail
      rw [ih]
      exact congrArg
        (fun k : ℕ => k :: binaryWordGapDecodeAux 0 tail) (by omega)

/-- Decoding a canonical gap encoding recovers the original list exactly.
This is a left-inverse statement on canonical words; reconstruction for
arbitrary words ending in true is a separate remaining obligation. -/
theorem binaryWordGapDecode_gapEncoding (gaps : List ℕ) :
    binaryWordGapDecode (binaryWordGapEncoding gaps) = gaps := by
  induction gaps with
  | nil => rfl
  | cons a rest ih =>
      change binaryWordGapDecodeAux 0
        ((binaryFalseRun a ++ [true]) ++
          binaryWordGapEncoding rest) = a :: rest
      rw [binaryWordGapDecodeAux_falseRun_block]
      simpa [binaryWordGapDecode] using ih


/-- The false symbols already accumulated when the scan reaches the end
of a word. This is the unfinished final run, which is not emitted as a gap. -/
def binaryWordGapPendingAux : ℕ → List Bool → ℕ
  | run, [] => run
  | run, false :: rest => binaryWordGapPendingAux (run + 1) rest
  | _, true :: rest => binaryWordGapPendingAux 0 rest

/-- Appending one false symbol to a false run increases its length by one. -/
theorem binaryFalseRun_append_false (a : ℕ) :
    binaryFalseRun a ++ [false] = binaryFalseRun (a + 1) := by
  induction a with
  | zero => rfl
  | succ a ih =>
      change (false :: binaryFalseRun a) ++ [false] =
        false :: binaryFalseRun (a + 1)
      simp only [List.cons_append]
      rw [ih]

/-- Exact reconstruction invariant for the gap scanner: the emitted
canonical blocks followed by the pending false run reconstruct the initial
false run together with the input word. -/
theorem binaryWordGapDecodeAux_reconstruct
    (run : ℕ) (word : List Bool) :
    binaryWordGapEncoding (binaryWordGapDecodeAux run word) ++
      binaryFalseRun (binaryWordGapPendingAux run word) =
    binaryFalseRun run ++ word := by
  induction word generalizing run with
  | nil =>
      simp [binaryWordGapDecodeAux, binaryWordGapPendingAux,
        binaryWordGapEncoding]
  | cons bit rest ih =>
      cases bit with
      | false =>
          change
            binaryWordGapEncoding (binaryWordGapDecodeAux (run + 1) rest) ++
              binaryFalseRun (binaryWordGapPendingAux (run + 1) rest) =
            binaryFalseRun run ++ (false :: rest)
          calc
            _ = binaryFalseRun (run + 1) ++ rest := ih (run + 1)
            _ = (binaryFalseRun run ++ [false]) ++ rest := by
              rw [← binaryFalseRun_append_false run]
            _ = binaryFalseRun run ++ (false :: rest) := by
              simp [List.append_assoc]
      | true =>
          change
            ((binaryFalseRun run ++ [true]) ++
              binaryWordGapEncoding (binaryWordGapDecodeAux 0 rest)) ++
              binaryFalseRun (binaryWordGapPendingAux 0 rest) =
            binaryFalseRun run ++ (true :: rest)
          calc
            _ = (binaryFalseRun run ++ [true]) ++
                (binaryWordGapEncoding (binaryWordGapDecodeAux 0 rest) ++
                  binaryFalseRun (binaryWordGapPendingAux 0 rest)) := by
              rw [List.append_assoc]
            _ = (binaryFalseRun run ++ [true]) ++
                (binaryFalseRun 0 ++ rest) := by
              rw [ih 0]
            _ = binaryFalseRun run ++ (true :: rest) := by
              simp [binaryFalseRun, List.append_assoc]

/-- Once a true delimiter has been read, the pending false run is empty.
In particular every word ending in true has no unfinished suffix. -/
theorem binaryWordGapPendingAux_append_true
    (run : ℕ) (pre : List Bool) :
    binaryWordGapPendingAux run (pre ++ [true]) = 0 := by
  induction pre generalizing run with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp [binaryWordGapPendingAux, ih]

/-- Every binary word ending in true is exactly reconstructed by decoding
its completed false runs and encoding the resulting gap list. -/
theorem binaryWordGapDecode_roundTrip_append_true (pre : List Bool) :
    binaryWordGapEncoding (binaryWordGapDecode (pre ++ [true])) =
      pre ++ [true] := by
  have h := binaryWordGapDecodeAux_reconstruct 0 (pre ++ [true])
  rw [binaryWordGapPendingAux_append_true 0 pre] at h
  simpa [binaryWordGapDecode, binaryFalseRun] using h


/-- A cut word ending in true decodes to one gap per true symbol,
and the sum of its gaps is exactly its number of false symbols. -/
theorem binaryWordGapDecode_stats_append_true (pre : List Bool) :
    (binaryWordGapDecode (pre ++ [true])).length =
        ((pre ++ [true]).filter id).length ∧
      (binaryWordGapDecode (pre ++ [true])).sum =
        (pre ++ [true]).length - ((pre ++ [true]).filter id).length := by
  constructor
  · exact binaryWordGapDecode_true_count _
  · have hround := binaryWordGapDecode_roundTrip_append_true pre
    have hlen := binaryWordGapEncoding_length
      (binaryWordGapDecode (pre ++ [true]))
    rw [hround] at hlen
    have hcount := binaryWordGapDecode_true_count (pre ++ [true])
    omega

/-- Evaluating a binary word beginning with one symbol multiplies its
evaluation on the left by the matrix assigned to that symbol. -/
theorem binaryWordMatrix_cons
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (bit : Bool) (w : List Bool) :
    binaryWordMatrix A B (bit :: w) =
      (if bit then B else A) * binaryWordMatrix A B w := by
  simp [binaryWordMatrix]

/-- Evaluation of a concatenation is the ordered product of the two
evaluations. This preserves the order of all noncommuting factors. -/
theorem binaryWordMatrix_append_words
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (u v : List Bool) :
    binaryWordMatrix A B (u ++ v) =
      binaryWordMatrix A B u * binaryWordMatrix A B v := by
  simp [binaryWordMatrix, List.map_append, List.prod_append]



/-- Move a distinguished true symbol to the end of a binary word.
If the original word is `pre ++ [true] ++ post`, this is the
cyclic cut `post ++ pre ++ [true]` at the marked position. -/
def binaryWordMarkedRotate (pre post : List Bool) : List Bool :=
  (post ++ pre) ++ [true]

/-- Cutting a binary word immediately after a marked true symbol preserves
its length. This is the list-level invariant needed for the gap composition. -/
theorem binaryWordMarkedRotate_length
    (pre post : List Bool) :
    (binaryWordMarkedRotate pre post).length =
      ((pre ++ [true]) ++ post).length := by
  simp [binaryWordMarkedRotate]
  omega

/-- The marked cut is exactly a cyclic left rotation of the original word.
The rotation amount is the length of the prefix through the marked true
symbol, equivalently the total word length minus the trailing suffix length. -/
theorem binaryWordMarkedRotate_eq_rotate
    (pre post : List Bool) :
    ((pre ++ [true]) ++ post).rotate
        (((pre ++ [true]) ++ post).length - post.length) =
      binaryWordMarkedRotate pre post := by
  have hshift :
      ((pre ++ [true]) ++ post).length - post.length =
        (pre ++ [true]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  calc
    ((pre ++ [true]) ++ post).rotate
        (((pre ++ [true]) ++ post).length - post.length) =
      ((pre ++ [true]) ++ post).rotate (pre ++ [true]).length := by
        rw [hshift]
    _ = post ++ (pre ++ [true]) :=
      List.rotate_append_length_eq (pre ++ [true]) post
    _ = binaryWordMarkedRotate pre post := by
      simpa [binaryWordMarkedRotate] using
        (List.append_assoc post pre [true]).symm


/-- The marked cut can be rotated back by the length of the trailing suffix.
The suffix length is the offset parameter; it lies strictly below the word
length because the marked true symbol is still present. -/
theorem binaryWordMarkedRotate_post_length_lt
    (pre post : List Bool) :
    post.length < ((pre ++ [true]) ++ post).length := by
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- Rotating the marked cut back by the trailing-suffix length recovers the
original word, with the distinguished true symbol at its original position. -/
theorem binaryWordMarkedRotate_rotate_back
    (pre post : List Bool) :
    (binaryWordMarkedRotate pre post).rotate post.length =
      ((pre ++ [true]) ++ post) := by
  simpa [binaryWordMarkedRotate, List.append_assoc] using
    (List.rotate_append_length_eq post (pre ++ [true]))

/-- The decoded gap list together with the suffix offset reconstructs the
original marked word exactly. This is the inverse reconstruction formula
needed for a bijection between marked words and (gap list, offset) data. -/
theorem binaryWordMarkedRotate_decode_reconstruct
    (pre post : List Bool) :
    (binaryWordGapEncoding
      (binaryWordGapDecode (binaryWordMarkedRotate pre post))).rotate
        post.length =
      ((pre ++ [true]) ++ post) := by
  have hround :
      binaryWordGapEncoding
        (binaryWordGapDecode (binaryWordMarkedRotate pre post)) =
          binaryWordMarkedRotate pre post := by
    simpa [binaryWordMarkedRotate] using
      (binaryWordGapDecode_roundTrip_append_true (post ++ pre))
  rw [hround]
  exact binaryWordMarkedRotate_rotate_back pre post


/-- Rotating a canonical gap word and then rotating back by the complementary
offset recovers the canonical word. The offset is required to be below the
word length, so the two rotation amounts add to exactly one full turn. -/
theorem binaryWordGapEncoding_rotate_back
    (gaps : List ℕ) (offset : ℕ)
    (hoffset : offset < (binaryWordGapEncoding gaps).length) :
    ((binaryWordGapEncoding gaps).rotate offset).rotate
        ((binaryWordGapEncoding gaps).length - offset) =
      binaryWordGapEncoding gaps := by
  calc
    _ = (binaryWordGapEncoding gaps).rotate
          (offset + ((binaryWordGapEncoding gaps).length - offset)) := by
      rw [List.rotate_rotate]
    _ = (binaryWordGapEncoding gaps).rotate
          (binaryWordGapEncoding gaps).length := by
      rw [Nat.add_sub_of_le hoffset.le]
    _ = binaryWordGapEncoding gaps :=
      List.rotate_length _

/-- Conversely, every legal rotation offset of a canonical gap word can be
cut back to the canonical end-marked form, and decoding recovers precisely
the original gap list. This is the reverse decoding direction for the
gap-list/offset correspondence. -/
theorem binaryWordGapEncoding_rotate_decode
    (gaps : List ℕ) (offset : ℕ)
    (hoffset : offset < (binaryWordGapEncoding gaps).length) :
    binaryWordGapDecode
      (((binaryWordGapEncoding gaps).rotate offset).rotate
        ((binaryWordGapEncoding gaps).length - offset)) = gaps := by
  rw [binaryWordGapEncoding_rotate_back gaps offset hoffset]
  exact binaryWordGapDecode_gapEncoding gaps


/-- Every nonempty canonical gap encoding ends with its final true
delimiter. -/
theorem binaryWordGapEncoding_getLast?
    (gaps : List ℕ) (hne : gaps ≠ []) :
    (binaryWordGapEncoding gaps).getLast? = some true := by
  induction gaps with
  | nil =>
      cases hne rfl
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [binaryWordGapEncoding]
      | cons b rest =>
          have htail : binaryWordGapEncoding (b :: rest) ≠ [] := by
            intro hnil
            have hcount := binaryWordGapEncoding_true_count (b :: rest)
            rw [hnil] at hcount
            simp at hcount
          change
            ((binaryFalseRun a ++ [true]) ++
              binaryWordGapEncoding (b :: rest)).getLast? = some true
          rw [List.getLast?_append_of_ne_nil _ htail]
          exact ih (by simp)

/-- For every legal offset k, rotating a canonical gap word admits a split
at the delimiter that has moved to position p-k-1. The suffix has length k,
and moving that delimiter to the end recovers the original canonical word,
so decoding the marked cut returns the original gap list. No quotient by
cyclic periodicity is taken: each legal offset remains separate data. -/
theorem binaryWordGapEncoding_rotate_decompose
    (gaps : List ℕ) (offset : ℕ)
    (hoffset : offset < (binaryWordGapEncoding gaps).length) :
    ∃ pre post,
      (binaryWordGapEncoding gaps).rotate offset =
        ((pre ++ [true]) ++ post) ∧
      post.length = offset ∧
      pre.length = (binaryWordGapEncoding gaps).length - offset - 1 ∧
      binaryWordGapDecode (binaryWordMarkedRotate pre post) = gaps := by
  let word := binaryWordGapEncoding gaps
  have hoffset' : offset < word.length := by
    simpa [word] using hoffset
  have hgaps : gaps ≠ [] := by
    intro hnil
    subst gaps
    simp [word, binaryWordGapEncoding] at hoffset'
  have hwordLast : word.getLast? = some true := by
    exact binaryWordGapEncoding_getLast? gaps hgaps
  have hdropLength : (word.drop offset).length = word.length - offset := by
    simp
  have hdropNe : word.drop offset ≠ [] := by
    intro hnil
    have hlen := hdropLength
    rw [hnil] at hlen
    simp at hlen
    omega
  have htakeDrop : word.take offset ++ word.drop offset = word :=
    List.take_append_drop offset word
  have hdropLast : (word.drop offset).getLast? = some true := by
    rw [← htakeDrop, List.getLast?_append_of_ne_nil _ hdropNe] at hwordLast
    exact hwordLast
  let pre := (word.drop offset).dropLast
  let post := word.take offset
  have hcut : pre ++ [true] = word.drop offset := by
    dsimp [pre]
    have hmem : true ∈ (word.drop offset).getLast? := by
      rw [hdropLast]
      simp
    exact List.dropLast_append_getLast? true hmem
  have hdecomp :
      word.rotate offset = ((pre ++ [true]) ++ post) := by
    calc
      word.rotate offset = word.drop offset ++ word.take offset :=
        List.rotate_eq_drop_append_take hoffset'.le
      _ = (pre ++ [true]) ++ post := by
        rw [← hcut]
  have hpostLength : post.length = offset := by
    simp [post, Nat.min_eq_left hoffset'.le]
  have hpreLength :
      pre.length = word.length - offset - 1 := by
    have hlen : pre.length + 1 = (word.drop offset).length := by
      have h := congrArg List.length hcut
      simpa using h
    rw [hdropLength] at hlen
    omega
  have hsplitLength :
      ((pre ++ [true]) ++ post).length = word.length := by
    calc
      ((pre ++ [true]) ++ post).length =
          (word.rotate offset).length :=
        (congrArg List.length hdecomp).symm
      _ = word.length := by simp
  have hshift :
      ((pre ++ [true]) ++ post).length - post.length =
        word.length - offset := by
    rw [hsplitLength, hpostLength]
  have hback :
      (word.rotate offset).rotate (word.length - offset) = word := by
    simpa [word] using
      binaryWordGapEncoding_rotate_back gaps offset hoffset
  have hmarked : binaryWordMarkedRotate pre post = word := by
    calc
      binaryWordMarkedRotate pre post =
          ((pre ++ [true]) ++ post).rotate
            (((pre ++ [true]) ++ post).length - post.length) :=
        (binaryWordMarkedRotate_eq_rotate pre post).symm
      _ = (word.rotate offset).rotate (word.length - offset) := by
        rw [hshift, ← hdecomp]
      _ = word := hback
  have hdecode :
      binaryWordGapDecode (binaryWordMarkedRotate pre post) = gaps := by
    rw [hmarked]
    simpa [word] using binaryWordGapDecode_gapEncoding gaps
  exact ⟨pre, post, hdecomp, hpostLength, hpreLength, hdecode⟩

/-- A decomposition at a fixed rotation offset is unique once the
trailing suffix length is fixed. This remains true when the underlying
binary word has a nontrivial rotational period. -/
theorem binaryWordGapEncoding_rotate_decompose_unique
    (gaps : List ℕ) (offset : ℕ)
    (pre₁ post₁ pre₂ post₂ : List Bool)
    (h₁ :
      (binaryWordGapEncoding gaps).rotate offset =
        ((pre₁ ++ [true]) ++ post₁))
    (h₂ :
      (binaryWordGapEncoding gaps).rotate offset =
        ((pre₂ ++ [true]) ++ post₂))
    (hpost₁ : post₁.length = offset)
    (hpost₂ : post₂.length = offset) :
    pre₁ = pre₂ ∧ post₁ = post₂ := by
  have hsplit :
      ((pre₁ ++ [true]) ++ post₁) =
        ((pre₂ ++ [true]) ++ post₂) :=
    h₁.symm.trans h₂
  have hparts := List.append_inj' hsplit (by
    rw [hpost₁, hpost₂])
  have hpreLength : pre₁.length = pre₂.length := by
    have h := congrArg List.length hparts.1
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    omega
  have hpre := List.append_inj_left hparts.1 hpreLength
  exact ⟨hpre, hparts.2⟩


/-- The gap list obtained after cutting a word at a marked true letter has
exactly the original number of true letters, and its total gap size is the
original number of false letters. The offset is represented by post.length
in binaryWordMarkedRotate; this theorem establishes the two composition
constraints needed for the marked-word/offset correspondence. -/
theorem binaryWordMarkedRotate_gap_stats
    (pre post : List Bool) :
    (binaryWordGapDecode (binaryWordMarkedRotate pre post)).length =
        (((pre ++ [true]) ++ post).filter id).length ∧
      (binaryWordGapDecode (binaryWordMarkedRotate pre post)).sum =
        ((pre ++ [true]) ++ post).length -
          (((pre ++ [true]) ++ post).filter id).length := by
  let gaps := binaryWordGapDecode (binaryWordMarkedRotate pre post)
  have hround :
      binaryWordGapEncoding gaps = binaryWordMarkedRotate pre post := by
    simpa [gaps, binaryWordMarkedRotate] using
      (binaryWordGapDecode_roundTrip_append_true (post ++ pre))
  have hcutCount :
      ((binaryWordMarkedRotate pre post).filter id).length =
        (post.filter id).length + (pre.filter id).length + 1 := by
    simp [binaryWordMarkedRotate, List.filter_append] <;> omega
  have hwordCount :
      (((pre ++ [true]) ++ post).filter id).length =
        (pre.filter id).length + 1 + (post.filter id).length := by
    simp [List.filter_append] <;> omega
  have hcount :
      ((binaryWordMarkedRotate pre post).filter id).length =
        (((pre ++ [true]) ++ post).filter id).length := by
    calc
      _ = (post.filter id).length + (pre.filter id).length + 1 :=
        hcutCount
      _ = (pre.filter id).length + 1 + (post.filter id).length := by omega
      _ = _ := hwordCount.symm
  have hgapCount :
      gaps.length = (((pre ++ [true]) ++ post).filter id).length := by
    calc
      gaps.length =
          ((binaryWordMarkedRotate pre post).filter id).length := by
        simpa [gaps] using
          (binaryWordGapDecode_true_count (binaryWordMarkedRotate pre post))
      _ = (((pre ++ [true]) ++ post).filter id).length := hcount
  have hstats :=
    binaryWordGapDecode_stats_append_true (post ++ pre)
  constructor
  · exact hgapCount
  · calc
      gaps.sum =
          (binaryWordMarkedRotate pre post).length -
            ((binaryWordMarkedRotate pre post).filter id).length := by
        simpa [gaps, binaryWordMarkedRotate] using hstats.2
      _ = ((pre ++ [true]) ++ post).length -
            (((pre ++ [true]) ++ post).filter id).length := by
        rw [binaryWordMarkedRotate_length, hcount]




/-- The two constructions are inverse on marked cuts: decode the word
obtained by moving the marked true delimiter to the end, use the suffix
length as the offset, and split the corresponding rotated canonical gap
encoding. The unique split is exactly the original (pre, post). -/
theorem binaryWordMarkedRotate_decode_decompose_inverse
    (pre post : List Bool) :
    ∃ pre' post',
      (binaryWordGapEncoding
        (binaryWordGapDecode (binaryWordMarkedRotate pre post))).rotate
          post.length =
        ((pre' ++ [true]) ++ post') ∧
      post'.length = post.length ∧
      pre' = pre ∧ post' = post := by
  let gaps := binaryWordGapDecode (binaryWordMarkedRotate pre post)
  have hstats :
      gaps.length = (((pre ++ [true]) ++ post).filter id).length ∧
      gaps.sum =
        ((pre ++ [true]) ++ post).length -
          (((pre ++ [true]) ++ post).filter id).length := by
    simpa [gaps] using binaryWordMarkedRotate_gap_stats pre post
  have hcount_le :
      (((pre ++ [true]) ++ post).filter id).length ≤
        ((pre ++ [true]) ++ post).length := by
    have hpartition :=
      List.length_eq_length_filter_add
        (l := ((pre ++ [true]) ++ post)) id
    omega
  have hencodeLength :
      (binaryWordGapEncoding gaps).length =
        ((pre ++ [true]) ++ post).length := by
    rw [binaryWordGapEncoding_length, hstats.2, hstats.1]
    exact Nat.sub_add_cancel hcount_le
  have hoffset :
      post.length < (binaryWordGapEncoding gaps).length := by
    rw [hencodeLength]
    exact binaryWordMarkedRotate_post_length_lt pre post
  obtain ⟨pre', post', hdecomp, hpost, _hpreLength, _hdecode⟩ :=
    binaryWordGapEncoding_rotate_decompose gaps post.length hoffset
  have hreconstruct :
      (binaryWordGapEncoding gaps).rotate post.length =
        ((pre ++ [true]) ++ post) := by
    simpa [gaps] using
      binaryWordMarkedRotate_decode_reconstruct pre post
  have hunique :=
    binaryWordGapEncoding_rotate_decompose_unique
      gaps post.length pre' post' pre post hdecomp hreconstruct hpost rfl
  exact ⟨pre', post', hdecomp, hpost, hunique.1, hunique.2⟩


/-- Gap data paired with a legal cyclic offset. -/
def binaryWordGapOffsetData : Type :=
  {x : List ℕ × ℕ // x.2 < (binaryWordGapEncoding x.1).length}

/-- The offset recovered from a marked cut is always legal for the
canonical encoding of its decoded gap list. The encoding has the same
length as the original marked word, by the exact true/false gap statistics. -/
theorem binaryWordMarkedCut_gapOffset_bound
    (pre post : List Bool) :
    post.length <
      (binaryWordGapEncoding
        (binaryWordGapDecode (binaryWordMarkedRotate pre post))).length := by
  let gaps := binaryWordGapDecode (binaryWordMarkedRotate pre post)
  have hstats := binaryWordMarkedRotate_gap_stats pre post
  have hcount_le :
      (((pre ++ [true]) ++ post).filter id).length ≤
        ((pre ++ [true]) ++ post).length := by
    have hpartition :=
      List.length_eq_length_filter_add
        (l := ((pre ++ [true]) ++ post)) id
    omega
  have hsum :
      gaps.sum =
        ((pre ++ [true]) ++ post).length -
          (((pre ++ [true]) ++ post).filter id).length := by
    simpa [gaps] using hstats.2
  have hcount :
      gaps.length = (((pre ++ [true]) ++ post).filter id).length := by
    simpa [gaps] using hstats.1
  have hlength :
      (binaryWordGapEncoding gaps).length =
        ((pre ++ [true]) ++ post).length := by
    rw [binaryWordGapEncoding_length, hsum, hcount]
    exact Nat.sub_add_cancel hcount_le
  rw [hlength]
  exact binaryWordMarkedRotate_post_length_lt pre post

/-- Send a marked cut (pre, post) to the decoded gap list and the suffix
length. The suffix length is retained as an actual offset, not quotiented
by cyclic periodicity. -/
def binaryWordMarkedCutToGapOffset
    (cut : List Bool × List Bool) : binaryWordGapOffsetData :=
  ⟨(binaryWordGapDecode
      (binaryWordMarkedRotate cut.1 cut.2), cut.2.length),
    binaryWordMarkedCut_gapOffset_bound cut.1 cut.2⟩

@[simp] theorem binaryWordMarkedCutToGapOffset_val
    (pre post : List Bool) :
    (binaryWordMarkedCutToGapOffset (pre, post)).val =
      (binaryWordGapDecode (binaryWordMarkedRotate pre post), post.length) :=
  rfl

/-- Construct a marked cut from a gap list and a legal offset by taking
the explicit split of the rotated canonical encoding. -/
noncomputable def binaryWordGapOffsetToMarkedCut
    (data : binaryWordGapOffsetData) : List Bool × List Bool :=
  let gaps := data.val.1
  let offset := data.val.2
  let hdecomp :=
    binaryWordGapEncoding_rotate_decompose gaps offset data.property
  (Classical.choose hdecomp,
    Classical.choose (Classical.choose_spec hdecomp))

/-- The chosen inverse cut satisfies the decomposition, offset, and
decoding laws supplied by the forward split theorem. -/
theorem binaryWordGapOffsetToMarkedCut_spec
    (gaps : List ℕ) (offset : ℕ)
    (hoffset : offset < (binaryWordGapEncoding gaps).length) :
    let cut :=
      binaryWordGapOffsetToMarkedCut ⟨(gaps, offset), hoffset⟩
    (binaryWordGapEncoding gaps).rotate offset =
        ((cut.1 ++ [true]) ++ cut.2) ∧
      cut.2.length = offset ∧
      binaryWordGapDecode (binaryWordMarkedRotate cut.1 cut.2) = gaps := by
  dsimp [binaryWordGapOffsetToMarkedCut]
  have hdecomp :=
    binaryWordGapEncoding_rotate_decompose gaps offset hoffset
  have hpre := Classical.choose_spec hdecomp
  have hpost := Classical.choose_spec hpre
  exact ⟨hpost.1, hpost.2.1, hpost.2.2.2⟩

/-- The marked-cut data and legal gap-list/offset data are equivalent.
The inverse laws use the fixed-offset split uniqueness theorem, so
periodic words still keep all offsets as distinct data. -/
noncomputable def binaryWordMarkedCutGapOffsetEquiv :
    (List Bool × List Bool) ≃ binaryWordGapOffsetData where
  toFun := binaryWordMarkedCutToGapOffset
  invFun := binaryWordGapOffsetToMarkedCut
  left_inv := by
    intro cut
    rcases cut with ⟨pre, post⟩
    let gaps := binaryWordGapDecode (binaryWordMarkedRotate pre post)
    have hoffset := binaryWordMarkedCut_gapOffset_bound pre post
    let data : binaryWordGapOffsetData :=
      ⟨(gaps, post.length), hoffset⟩
    have hdata :
        binaryWordMarkedCutToGapOffset (pre, post) = data := by
      apply Subtype.ext
      rfl
    let chosen := binaryWordGapOffsetToMarkedCut data
    have hspec :=
      binaryWordGapOffsetToMarkedCut_spec gaps post.length hoffset
    dsimp at hspec
    have hback :
        (binaryWordGapEncoding gaps).rotate post.length =
          ((pre ++ [true]) ++ post) := by
      simpa [gaps] using
        binaryWordMarkedRotate_decode_reconstruct pre post
    have hunique :=
      binaryWordGapEncoding_rotate_decompose_unique
        gaps post.length chosen.1 chosen.2 pre post
        hspec.1 hback hspec.2.1 rfl
    rw [hdata]
    change chosen = (pre, post)
    exact Prod.ext hunique.1 hunique.2
  right_inv := by
    intro data
    rcases data with ⟨⟨gaps, offset⟩, hoffset⟩
    let cut := binaryWordGapOffsetToMarkedCut ⟨(gaps, offset), hoffset⟩
    have hspec :=
      binaryWordGapOffsetToMarkedCut_spec gaps offset hoffset
    dsimp [cut] at hspec
    apply Subtype.ext
    change
      (binaryWordGapDecode (binaryWordMarkedRotate cut.1 cut.2),
        cut.2.length) = (gaps, offset)
    exact Prod.ext hspec.2.2 hspec.2.1


/-- The fixed-(p,r) gap-offset stratum: exactly r decoded gaps with
total size p-r, together with the legal offset already carried by the
unrestricted gap-offset data. -/
def binaryWordGapOffsetStratum (p r : ℕ) : Type :=
  {data : binaryWordGapOffsetData //
    r ≤ p ∧ data.val.1.length = r ∧ data.val.1.sum = p - r}

/-- The fixed-(p,r) marked-cut stratum: the reconstructed word has
length p and exactly r true letters, one of which is distinguished by
the cut between pre and post. -/
def binaryWordMarkedCutStratum (p r : ℕ) : Type :=
  {cut : List Bool × List Bool //
    r ≤ p ∧
    ((cut.1 ++ [true]) ++ cut.2).length = p ∧
    (((cut.1 ++ [true]) ++ cut.2).filter id).length = r}

/-- Restrict the unrestricted marked-cut/gap-offset equivalence to the
exact length and letter-count conditions. The restriction is transported
by Mathlib's subtypeEquiv, so both inverse laws come from the established
equivalence itself rather than manually unfolding subtype maps. -/
noncomputable def binaryWordMarkedCutGapOffsetStratumEquiv
    (p r : ℕ) :
    binaryWordMarkedCutStratum p r ≃ binaryWordGapOffsetStratum p r :=
  binaryWordMarkedCutGapOffsetEquiv.subtypeEquiv (fun cut => by
    rcases cut with ⟨pre, post⟩
    change
      (r ≤ p ∧
        ((pre ++ [true]) ++ post).length = p ∧
        (((pre ++ [true]) ++ post).filter id).length = r) ↔
      (r ≤ p ∧
        (binaryWordGapDecode (binaryWordMarkedRotate pre post)).length = r ∧
        (binaryWordGapDecode (binaryWordMarkedRotate pre post)).sum = p - r)
    have hstats := binaryWordMarkedRotate_gap_stats pre post
    constructor
    · rintro ⟨hrp, hlen, hcount⟩
      refine ⟨hrp, hstats.1.trans hcount, ?_⟩
      rw [hstats.2, hlen, hcount]
    · rintro ⟨hrp, hgaplen, hgapsum⟩
      have hround :
          binaryWordGapEncoding
            (binaryWordGapDecode (binaryWordMarkedRotate pre post)) =
              binaryWordMarkedRotate pre post := by
        simpa [binaryWordMarkedRotate] using
          (binaryWordGapDecode_roundTrip_append_true (post ++ pre))
      have hlen :
          ((pre ++ [true]) ++ post).length = p := by
        calc
          ((pre ++ [true]) ++ post).length =
              (binaryWordMarkedRotate pre post).length :=
            (binaryWordMarkedRotate_length pre post).symm
          _ = (binaryWordGapEncoding
                (binaryWordGapDecode (binaryWordMarkedRotate pre post))).length := by
            rw [hround]
          _ = (binaryWordGapDecode
                (binaryWordMarkedRotate pre post)).sum +
              (binaryWordGapDecode
                (binaryWordMarkedRotate pre post)).length :=
            binaryWordGapEncoding_length _
          _ = p := by
            rw [hgapsum, hgaplen]
            omega
      have hcount :
          (((pre ++ [true]) ++ post).filter id).length = r :=
        hstats.1.symm.trans hgaplen
      exact ⟨hrp, hlen, hcount⟩)



/-- Every coordinate of a natural-number list is bounded by its sum. -/
theorem binaryWordGapList_get_le_sum
    (gaps : List ℕ) (i : Fin gaps.length) :
    gaps.get i ≤ gaps.sum := by
  induction gaps with
  | nil =>
      exact Fin.elim0 i
  | cons a rest ih =>
      rcases i with ⟨i, hi⟩
      cases i with
      | zero =>
          simp
      | succ i =>
          have hi' : i < rest.length := by
            simp only [List.length_cons] at hi
            omega
          have hget := ih ⟨i, hi'⟩
          have hsum : rest.sum ≤ a + rest.sum := by omega
          simpa using le_trans hget hsum

/-- Turn a length-r gap list of total p-r into a function with bounded
coordinates. The upper bound p-r is forced by nonnegativity of all gaps. -/
def binaryWordGapListToFinVector
    (p r : ℕ) (gaps : List ℕ)
    (hlen : gaps.length = r) (hsum : gaps.sum = p - r) :
    Fin r → Fin (p - r + 1) :=
  fun i =>
    ⟨gaps.get (Fin.cast hlen.symm i), by
      calc
        gaps.get (Fin.cast hlen.symm i) ≤ gaps.sum :=
          binaryWordGapList_get_le_sum gaps _
        _ = p - r := hsum
        _ < p - r + 1 := by omega⟩

/-- Converting a fixed-length gap list to a Fin-indexed vector and back
recovers the list, using Mathlib's ofFn/get equivalence. -/
theorem binaryWordGapListToFinVector_ofFn
    (p r : ℕ) (gaps : List ℕ)
    (hlen : gaps.length = r) (hsum : gaps.sum = p - r) :
    List.ofFn (fun i : Fin r =>
      (binaryWordGapListToFinVector p r gaps hlen hsum i).val) = gaps := by
  unfold binaryWordGapListToFinVector
  calc
    List.ofFn (fun i : Fin r =>
        gaps.get (Fin.cast hlen.symm i)) =
      List.ofFn (fun i : Fin gaps.length => gaps.get i) :=
        (List.ofFn_congr hlen (fun i : Fin gaps.length => gaps.get i)).symm
    _ = gaps := List.ofFn_get gaps

/-- Finite model of fixed-(p,r) gap-offset data. A vector stores the r
nonnegative gap sizes, and Fin p stores the actual cyclic offset. Keeping
the offset as a Fin value (rather than taking cyclic orbits) retains all p
marked positions, including those in periodic words. -/
def binaryWordGapOffsetVectorStratum (p r : ℕ) : Type :=
  {x : (Fin r → Fin (p - r + 1)) × Fin p //
    r ≤ p ∧
      (List.ofFn (fun i : Fin r => (x.1 i).val)).sum = p - r}

/-- The vector/offset model is finite because it is a subtype of a product
of finite function and offset types. -/
noncomputable instance binaryWordGapOffsetVectorStratum_fintype
    (p r : ℕ) : Fintype (binaryWordGapOffsetVectorStratum p r) := by
  classical
  unfold binaryWordGapOffsetVectorStratum
  refine Fintype.subtype
    (Finset.univ.filter fun x :
      (Fin r → Fin (p - r + 1)) × Fin p =>
        r ≤ p ∧
          (List.ofFn (fun i : Fin r => (x.1 i).val)).sum = p - r) ?_
  intro x
  simp

/-- The fixed-(p,r) list-based gap-offset stratum is equivalent to the
finite vector/offset model. The offset bound is transported using the
exact encoding length p = sum(gaps) + length(gaps). -/
noncomputable def binaryWordGapOffsetVectorEquiv
    (p r : ℕ) :
    binaryWordGapOffsetStratum p r ≃ binaryWordGapOffsetVectorStratum p r where
  toFun x := by
    rcases x with ⟨⟨⟨gaps, offset⟩, hoffset⟩, hrp, hlen, hsum⟩
    let v := binaryWordGapListToFinVector p r gaps hlen hsum
    have hvlist :=
      binaryWordGapListToFinVector_ofFn p r gaps hlen hsum
    have hencoded : (binaryWordGapEncoding gaps).length = p := by
      rw [binaryWordGapEncoding_length, hsum, hlen]
      omega
    have hoffset' : offset < p := by
      rw [hencoded] at hoffset
      exact hoffset
    refine ⟨(v, ⟨offset, hoffset'⟩), hrp, ?_⟩
    change (List.ofFn (fun i : Fin r => (v i).val)).sum = p - r
    rw [hvlist]
    exact hsum
  invFun x := by
    rcases x with ⟨⟨v, offset⟩, hrp, hsum⟩
    let gaps := List.ofFn (fun i : Fin r => (v i).val)
    have hlen : gaps.length = r := by simp [gaps]
    have hsum' : gaps.sum = p - r := by simpa [gaps] using hsum
    have hencoded : (binaryWordGapEncoding gaps).length = p := by
      rw [binaryWordGapEncoding_length, hsum', hlen]
      omega
    refine ⟨⟨(gaps, (offset : ℕ)), ?_⟩, hrp, hlen, hsum'⟩
    rw [hencoded]
    exact offset.isLt
  left_inv x := by
    rcases x with ⟨⟨⟨gaps, offset⟩, hoffset⟩, hrp, hlen, hsum⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact binaryWordGapListToFinVector_ofFn p r gaps hlen hsum
    · rfl
  right_inv x := by
    rcases x with ⟨⟨v, offset⟩, hrp, hsum⟩
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply Fin.ext
      simp [binaryWordGapListToFinVector, List.get_ofFn]
    · exact Fin.ext rfl

/-- The exact gap-offset stratum is a finite type, transported from the
explicit vector/offset model above. -/
noncomputable instance binaryWordGapOffsetStratum_fintype
    (p r : ℕ) : Fintype (binaryWordGapOffsetStratum p r) :=
  Fintype.ofEquiv (binaryWordGapOffsetVectorStratum p r)
    (binaryWordGapOffsetVectorEquiv p r).symm

/-- The fixed-(p,r) marked-cut stratum is finite as well, by the already
proved restricted marked-cut/gap-offset equivalence. -/
noncomputable instance binaryWordMarkedCutStratum_fintype
    (p r : ℕ) : Fintype (binaryWordMarkedCutStratum p r) :=
  Fintype.ofEquiv (binaryWordGapOffsetStratum p r)
    (binaryWordMarkedCutGapOffsetStratumEquiv p r).symm


/-- The trace of a binary matrix word is unchanged when a marked true letter
is moved from the cut position to the final position. The proof is exactly
trace cyclicity for the two grouped factors `eval(pre) * B` and
`eval(post)`; no factors within either word are commuted. -/
theorem binaryWordMatrix_trace_marked_rotate
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (pre post : List Bool) :
    Matrix.trace (binaryWordMatrix A B ((pre ++ [true]) ++ post)) =
      Matrix.trace (binaryWordMatrix A B (binaryWordMarkedRotate pre post)) := by
  have hleft :
      binaryWordMatrix A B ((pre ++ [true]) ++ post) =
        (binaryWordMatrix A B pre * B) *
          binaryWordMatrix A B post := by
    calc
      _ = binaryWordMatrix A B (pre ++ [true]) *
            binaryWordMatrix A B post :=
        binaryWordMatrix_append_words A B (pre ++ [true]) post
      _ = (binaryWordMatrix A B pre * B) *
            binaryWordMatrix A B post := by
        rw [binaryWordMatrix_append_words]
        simp [binaryWordMatrix]
  have hright :
      binaryWordMatrix A B ((post ++ pre) ++ [true]) =
        binaryWordMatrix A B post *
          (binaryWordMatrix A B pre * B) := by
    calc
      _ = binaryWordMatrix A B (post ++ pre) *
            binaryWordMatrix A B [true] :=
        binaryWordMatrix_append_words A B (post ++ pre) [true]
      _ = (binaryWordMatrix A B post * binaryWordMatrix A B pre) * B := by
        rw [binaryWordMatrix_append_words]
        simp [binaryWordMatrix]
      _ = binaryWordMatrix A B post *
            (binaryWordMatrix A B pre * B) := by
        rw [Matrix.mul_assoc]
  calc
    Matrix.trace (binaryWordMatrix A B ((pre ++ [true]) ++ post)) =
        Matrix.trace
          ((binaryWordMatrix A B pre * B) *
            binaryWordMatrix A B post) := by rw [hleft]
    _ = Matrix.trace
          (binaryWordMatrix A B post *
            (binaryWordMatrix A B pre * B)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace
          (binaryWordMatrix A B (binaryWordMarkedRotate pre post)) := by
      rw [binaryWordMarkedRotate, hright]

/-- A single gap block evaluates to A^a * B, with no factor reordering. -/
theorem binaryWordMatrix_falseRun_block
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (a : ℕ) :
    binaryWordMatrix A B (binaryFalseRun a ++ [true]) =
      A ^ a * B := by
  induction a with
  | zero => simp [binaryFalseRun, binaryWordMatrix]
  | succ a ih =>
      change binaryWordMatrix A B
        (false :: (binaryFalseRun a ++ [true])) =
          A ^ (a + 1) * B
      calc
        _ = A * binaryWordMatrix A B (binaryFalseRun a ++ [true]) := by
          simpa using
            (binaryWordMatrix_cons A B false (binaryFalseRun a ++ [true]))
        _ = A * (A ^ a * B) := by rw [ih]
        _ = A ^ (a + 1) * B := by
          rw [pow_succ']
          simp [mul_assoc]

/-- A canonical gap word evaluates to the product of its ordered blocks
A^a * B. This is the algebraic bridge from gap compositions to the cyclic
trace expression; no cyclic permutation or commutation is used here. -/
theorem binaryWordMatrix_gapEncoding
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (gaps : List ℕ) :
    binaryWordMatrix A B (binaryWordGapEncoding gaps) =
      (gaps.map (fun a => A ^ a * B)).prod := by
  induction gaps with
  | nil => simp [binaryWordGapEncoding, binaryWordMatrix]
  | cons a rest ih =>
      change binaryWordMatrix A B
        ((binaryFalseRun a ++ [true]) ++ binaryWordGapEncoding rest) =
        (A ^ a * B) * (rest.map (fun a => A ^ a * B)).prod
      rw [binaryWordMatrix_append_words,
        binaryWordMatrix_falseRun_block, ih]

/-- The trace of the canonical binary gap word is exactly cyclicGapTrace.
The distinguished B is placed at the end, so this equality itself needs
no trace rotation; rotations are handled by cyclicGapTrace_rotate. -/
theorem binaryWordGapEncoding_trace_eq_cyclicGapTrace
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (gaps : List ℕ) :
    Matrix.trace (binaryWordMatrix K N (binaryWordGapEncoding gaps)) =
      cyclicGapTrace K N gaps := by
  rw [binaryWordMatrix_gapEncoding]
  rfl


/-- Every marked binary word has the same trace as the cyclic gap trace of
its decoded cut. The original matrix factors are not rearranged: first use
trace cyclicity for the single marked cut, then evaluate its canonical gap
encoding as the ordered product of K^a * N blocks. -/
theorem binaryWordMatrix_trace_marked_eq_cyclicGapTrace
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (pre post : List Bool) :
    Matrix.trace (binaryWordMatrix K N ((pre ++ [true]) ++ post)) =
      cyclicGapTrace K N
        (binaryWordGapDecode (binaryWordMarkedRotate pre post)) := by
  have hround :
      binaryWordGapEncoding
        (binaryWordGapDecode (binaryWordMarkedRotate pre post)) =
          binaryWordMarkedRotate pre post := by
    simpa [binaryWordMarkedRotate] using
      (binaryWordGapDecode_roundTrip_append_true (post ++ pre))
  calc
    Matrix.trace (binaryWordMatrix K N ((pre ++ [true]) ++ post)) =
        Matrix.trace (binaryWordMatrix K N
          (binaryWordMarkedRotate pre post)) :=
      binaryWordMatrix_trace_marked_rotate K N pre post
    _ = Matrix.trace (binaryWordMatrix K N
          (binaryWordGapEncoding
            (binaryWordGapDecode (binaryWordMarkedRotate pre post))) ) :=
      congrArg
        (fun w : List Bool => Matrix.trace (binaryWordMatrix K N w))
        hround.symm
    _ = cyclicGapTrace K N
          (binaryWordGapDecode (binaryWordMarkedRotate pre post)) :=
      binaryWordGapEncoding_trace_eq_cyclicGapTrace K N _


/-- The equivalence preserves the marked-word trace as the cyclic gap
trace of the corresponding decoded gap list. -/
theorem binaryWordMarkedCut_trace_eq_cyclicGapTrace
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (pre post : List Bool) :
    Matrix.trace
      (binaryWordMatrix K N ((pre ++ [true]) ++ post)) =
      cyclicGapTrace K N
        (binaryWordMarkedCutToGapOffset (pre, post)).val.1 := by
  simpa using
    (binaryWordMatrix_trace_marked_eq_cyclicGapTrace K N pre post)


/-- Reindex the finite trace sum over marked cuts by the exact
fixed-(p,r) marked-cut/gap-offset equivalence. Every marked position is
retained as a separate offset, including in periodic words. This is the
finite-sum form of the trace-preserving correspondence. -/
theorem binaryWordMarkedCutStratum_sum_trace_eq_gapOffsetStratum_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (p r : ℕ) :
    (∑ cut : binaryWordMarkedCutStratum p r,
      Matrix.trace
        (binaryWordMatrix K N ((cut.val.1 ++ [true]) ++ cut.val.2))) =
    ∑ data : binaryWordGapOffsetStratum p r,
      cyclicGapTrace K N data.val.val.1 := by
  classical
  let e := binaryWordMarkedCutGapOffsetStratumEquiv p r
  exact Fintype.sum_equiv e
    (fun cut =>
      Matrix.trace
        (binaryWordMatrix K N ((cut.val.1 ++ [true]) ++ cut.val.2)))
    (fun data => cyclicGapTrace K N data.val.val.1)
    (by
      intro cut
      rcases cut with ⟨⟨pre, post⟩, hcut⟩
      have hvalue :
          (e ⟨(pre, post), hcut⟩).val.val.1 =
            (binaryWordMarkedCutToGapOffset (pre, post)).val.1 := by
        rfl
      rw [hvalue]
      exact binaryWordMarkedCut_trace_eq_cyclicGapTrace K N pre post)



/-- Gap vectors without a marked cyclic offset. -/
def binaryWordGapVectorStratum (p r : ℕ) : Type :=
  {v : Fin r → Fin (p - r + 1) //
    r ≤ p ∧ (List.ofFn (fun i : Fin r => (v i).val)).sum = p - r}

/-- The gap-vector stratum is finite as a subtype of a finite function type. -/
noncomputable instance binaryWordGapVectorStratum_fintype
    (p r : ℕ) : Fintype (binaryWordGapVectorStratum p r) := by
  classical
  unfold binaryWordGapVectorStratum
  refine Fintype.subtype
    (Finset.univ.filter fun v : Fin r → Fin (p - r + 1) =>
      r ≤ p ∧ (List.ofFn (fun i : Fin r => (v i).val)).sum = p - r) ?_
  intro v
  simp

/-- Separating the offset from the gap vector is an exact product
decomposition. No cyclic quotient is taken: the second factor is Fin p. -/
def binaryWordGapOffsetVectorProdEquiv (p r : ℕ) :
    binaryWordGapOffsetVectorStratum p r ≃
      binaryWordGapVectorStratum p r × Fin p where
  toFun x := (⟨x.val.1, x.property⟩, x.val.2)
  invFun x := ⟨(x.1.val, x.2), x.1.property⟩
  left_inv x := by
    rcases x with ⟨⟨v, k⟩, h⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨v, h⟩, k⟩
    rfl

/-- The gap-offset trace sum is the iterated sum over gap vectors and all
p offsets. Each offset remains a separate summand, even for periodic gaps. -/
theorem binaryWordGapOffsetVectorStratum_sum_trace_eq_gap_sum_offsets
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (p r : ℕ) :
    (∑ data : binaryWordGapOffsetVectorStratum p r,
      cyclicGapTrace K N
        (List.ofFn (fun i : Fin r => (data.val.1 i).val))) =
    ∑ gaps : binaryWordGapVectorStratum p r,
      ∑ offset : Fin p,
        cyclicGapTrace K N
          (List.ofFn (fun i : Fin r => (gaps.val i).val)) := by
  classical
  let e := binaryWordGapOffsetVectorProdEquiv p r
  calc
    _ = ∑ pair : binaryWordGapVectorStratum p r × Fin p,
          cyclicGapTrace K N
            (List.ofFn (fun i : Fin r => (pair.1.val i).val)) := by
      exact Fintype.sum_equiv e
        (fun data => cyclicGapTrace K N
          (List.ofFn (fun i : Fin r => (data.val.1 i).val)))
        (fun pair => cyclicGapTrace K N
          (List.ofFn (fun i : Fin r => (pair.1.val i).val)))
        (by
          intro data
          rfl)
    _ = ∑ gaps : binaryWordGapVectorStratum p r,
          ∑ offset : Fin p,
            cyclicGapTrace K N
              (List.ofFn (fun i : Fin r => (gaps.val i).val)) := by
      rw [Fintype.sum_prod_type]


/-- The gap-offset trace sum has exactly p copies of each gap trace.
This is the explicit p-fold multiplicity on the gap side; offsets remain
distinct even when the encoded cyclic word is periodic. -/
theorem binaryWordGapOffsetVectorStratum_sum_trace_eq_card_mul_gap_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (p r : ℕ) :
    (∑ data : binaryWordGapOffsetVectorStratum p r,
      cyclicGapTrace K N
        (List.ofFn (fun i : Fin r => (data.val.1 i).val))) =
    (p : ℂ) *
      ∑ gaps : binaryWordGapVectorStratum p r,
        cyclicGapTrace K N
          (List.ofFn (fun i : Fin r => (gaps.val i).val)) := by
  classical
  rw [binaryWordGapOffsetVectorStratum_sum_trace_eq_gap_sum_offsets]
  calc
    _ = ∑ gaps : binaryWordGapVectorStratum p r,
          (p : ℂ) *
            cyclicGapTrace K N
              (List.ofFn (fun i : Fin r => (gaps.val i).val)) := by
      apply Finset.sum_congr rfl
      intro gaps hgaps
      simp
    _ = (p : ℂ) *
          ∑ gaps : binaryWordGapVectorStratum p r,
            cyclicGapTrace K N
              (List.ofFn (fun i : Fin r => (gaps.val i).val)) := by
      rw [Finset.mul_sum]




/-- Finite exact-weight binary words of length p. -/
def binaryWordFinStratum (p r : ℕ) : Type :=
  {w : Fin p → Bool //
    r ≤ p ∧ ((List.ofFn w).filter id).length = r}

/-- The exact-weight binary-word stratum is finite. -/
noncomputable instance binaryWordFinStratum_fintype (p r : ℕ) :
    Fintype (binaryWordFinStratum p r) := by
  classical
  unfold binaryWordFinStratum
  refine Fintype.subtype
    (Finset.univ.filter fun w : Fin p → Bool =>
      r ≤ p ∧ ((List.ofFn w).filter id).length = r) ?_
  intro w
  simp

/-- The r true positions of an exact-weight word form a finite type. -/
noncomputable instance binaryWordFinTruePositions_fintype
    (p r : ℕ) (w : binaryWordFinStratum p r) :
    Fintype {i : Fin p // w.val i = true} := by
  classical
  refine Fintype.subtype
    (Finset.univ.filter fun i : Fin p => w.val i = true) ?_
  intro i
  simp

/-- A fixed binary word has exactly as many true positions as its true-letter
count. This identifies the finite subtype of true indices with the filtered
list of true letters, without identifying equal values at different indices. -/
theorem binaryWordFin_true_positions_card (p r : ℕ)
    (w : binaryWordFinStratum p r) :
    Fintype.card {i : Fin p // w.val i = true} = r := by
  classical
  have hcard := List.Nodup.card_eq_countP
    (l := List.finRange p) (P := fun i : Fin p => w.val i = true)
    (List.nodup_finRange p)
  calc
    Fintype.card {i : Fin p // w.val i = true} =
        (Finset.univ.filter fun i : Fin p => w.val i = true).card := by
          rw [Fintype.card_subtype]
    _ = List.countP (fun i : Fin p => decide (w.val i = true))
          (List.finRange p) := by
          simpa only [List.toFinset_finRange] using hcard
    _ = List.countP (fun i : Fin p => w.val i) (List.finRange p) := by
          congr 1
          funext i
          cases h : w.val i <;> simp [h]
    _ = List.countP (id ∘ w.val) (List.finRange p) := by
          rfl
    _ = List.countP id (List.ofFn w.val) := by
          rw [List.ofFn_eq_map, List.countP_map]
    _ = ((List.ofFn w.val).filter id).length := by
          rw [List.countP_eq_length_filter]
    _ = r := w.property.2

/-- A binary word together with a chosen true position. -/
def binaryWordFinMarkedStratum (p r : ℕ) : Type :=
  Σ w : binaryWordFinStratum p r, {i : Fin p // w.val i = true}

/-- The marked-word type is finite. -/
noncomputable instance binaryWordFinMarkedStratum_fintype (p r : ℕ) :
    Fintype (binaryWordFinMarkedStratum p r) := by
  classical
  unfold binaryWordFinMarkedStratum
  infer_instance

/-- Summing a constant over the r true positions of a fixed exact-weight
word multiplies it by r. -/
theorem binaryWordFinMarkedStratum_sum_eq_r_mul
    (p r : ℕ) (f : binaryWordFinStratum p r → ℂ) :
    (∑ marked : binaryWordFinMarkedStratum p r, f marked.1) =
      (r : ℂ) * ∑ w : binaryWordFinStratum p r, f w := by
  classical
  change
    (∑ marked : (Σ w : binaryWordFinStratum p r,
      {i : Fin p // w.val i = true}), f marked.1) =
      (r : ℂ) * ∑ w : binaryWordFinStratum p r, f w
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ w : binaryWordFinStratum p r, (r : ℂ) * f w := by
      apply Finset.sum_congr rfl
      intro w hw
      have hcard : Fintype.card {i : Fin p // w.val i = true} = r :=
        binaryWordFin_true_positions_card p r w
      simp [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = (r : ℂ) * ∑ w : binaryWordFinStratum p r, f w := by
      rw [Finset.mul_sum]

/-- The marked cuts of a fixed-(p,r) word are equivalent to a word together
with one of its true positions. The chosen position is the length of the
prefix before the distinguished true symbol. -/
noncomputable def binaryWordMarkedCutFinEquiv (p r : ℕ) :
    binaryWordMarkedCutStratum p r ≃ binaryWordFinMarkedStratum p r where
  toFun cut := by
    rcases cut with ⟨⟨pre, post⟩, hcut⟩
    let word : List Bool := (pre ++ [true]) ++ post
    have hlen : word.length = p := hcut.2.1
    let w : Fin p → Bool :=
      fun i => word.get (Fin.cast hlen.symm i)
    have hrepr : List.ofFn w = word := by
      dsimp [w]
      calc
        List.ofFn (fun i : Fin p => word.get (Fin.cast hlen.symm i)) =
            List.ofFn word.get := (List.ofFn_congr hlen word.get).symm
        _ = word := List.ofFn_get word
    have hprelt : pre.length < word.length := by
      simp [word, List.length_append]
    have hi : pre.length < p := by
      rw [← hlen]
      exact hprelt
    let i : Fin p := ⟨pre.length, hi⟩
    have hcast : (Fin.cast hlen.symm i : Fin word.length).val = pre.length := by
      simp [i]
    have hidx :
        Fin.cast hlen.symm i = ⟨pre.length, hprelt⟩ := Fin.ext hcast
    have hwordAt : word.get ⟨pre.length, hprelt⟩ = true := by
      simp [word, List.get_eq_getElem]
    have htrue : w i = true := by
      change word.get (Fin.cast hlen.symm i) = true
      rw [hidx]
      exact hwordAt
    refine ⟨⟨w, hcut.1, ?_⟩, ⟨i, htrue⟩⟩
    rw [hrepr]
    exact hcut.2.2
  invFun x := by
    rcases x with ⟨⟨w, hw⟩, ⟨i, hi⟩⟩
    change w i = true at hi
    let word : List Bool := List.ofFn w
    let pre : List Bool := word.take i
    let post : List Bool := word.drop (i + 1)
    have hiword : i < word.length := by simpa [word] using i.isLt
    have hdrop : word.drop i = true :: word.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hiword]
      simp [word, hi]
    have hdecomp : (pre ++ [true]) ++ post = word := by
      dsimp [pre, post]
      calc
        (word.take i ++ [true]) ++ word.drop (i + 1) =
            word.take i ++ ([true] ++ word.drop (i + 1)) := by
              simp [List.append_assoc]
        _ = word.take i ++ word.drop i := by
              rw [show [true] ++ word.drop (i + 1) = word.drop i by
                simpa using hdrop.symm]
        _ = word := List.take_append_drop i word
    have hcutlen : ((pre ++ [true]) ++ post).length = p := by
      rw [hdecomp]
      simp [word]
    have hcutcount :
        (((pre ++ [true]) ++ post).filter id).length = r := by
      rw [hdecomp]
      exact hw.2
    exact ⟨(pre, post), hw.1, hcutlen, hcutcount⟩
  left_inv cut := by
    rcases cut with ⟨⟨pre, post⟩, hcut⟩
    let word : List Bool := (pre ++ [true]) ++ post
    have hlen : word.length = p := hcut.2.1
    let w : Fin p → Bool :=
      fun i => word.get (Fin.cast hlen.symm i)
    have hrepr : List.ofFn w = word := by
      dsimp [w]
      calc
        List.ofFn (fun i : Fin p => word.get (Fin.cast hlen.symm i)) =
            List.ofFn word.get := (List.ofFn_congr hlen word.get).symm
        _ = word := List.ofFn_get word
    have hpre : word.take pre.length = pre := by
      simpa [word, List.append_assoc] using
        (List.take_left (l₁ := pre) (l₂ := [true] ++ post))
    have hpost : word.drop (pre.length + 1) = post := by
      simpa [word, List.append_assoc] using
        (List.drop_left (l₁ := pre ++ [true]) (l₂ := post))
    have hpre' : (List.ofFn w).take pre.length = pre := by
      rw [hrepr]
      exact hpre
    have hpost' : (List.ofFn w).drop (pre.length + 1) = post := by
      rw [hrepr]
      exact hpost
    apply Subtype.ext
    change
      ((List.ofFn w).take pre.length, (List.ofFn w).drop (pre.length + 1)) =
        (pre, post)
    exact Prod.ext hpre' hpost'
  right_inv x := by
    rcases x with ⟨⟨w, hw⟩, ⟨i, hi⟩⟩
    change w i = true at hi
    let word : List Bool := List.ofFn w
    let pre : List Bool := word.take i
    let post : List Bool := word.drop (i + 1)
    have hiword : i < word.length := by simpa [word] using i.isLt
    have hdrop : word.drop i = true :: word.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hiword]
      simp [word, hi]
    have hdecomp : (pre ++ [true]) ++ post = word := by
      dsimp [pre, post]
      calc
        (word.take i ++ [true]) ++ word.drop (i + 1) =
            word.take i ++ ([true] ++ word.drop (i + 1)) := by
              simp [List.append_assoc]
        _ = word.take i ++ word.drop i := by
              rw [show [true] ++ word.drop (i + 1) = word.drop i by
                simpa using hdrop.symm]
        _ = word := List.take_append_drop i word
    have hcutlen : ((pre ++ [true]) ++ post).length = p := by
      rw [hdecomp]
      simp [word]
    have hprelen : pre.length = i := by
      dsimp [pre, word]
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hiword)]
    have hrepr :
        List.ofFn (fun j : Fin p =>
          ((pre ++ [true]) ++ post).get (Fin.cast hcutlen.symm j)) =
          ((pre ++ [true]) ++ post) := by
      calc
        _ = List.ofFn (((pre ++ [true]) ++ post).get) :=
          (List.ofFn_congr hcutlen ((pre ++ [true]) ++ post).get).symm
        _ = (pre ++ [true]) ++ post := List.ofFn_get _
    have hfun :
        (fun j : Fin p =>
          ((pre ++ [true]) ++ post).get (Fin.cast hcutlen.symm j)) = w := by
      apply List.ofFn_injective
      calc
        List.ofFn (fun j : Fin p =>
            ((pre ++ [true]) ++ post).get (Fin.cast hcutlen.symm j)) =
            ((pre ++ [true]) ++ post) := hrepr
        _ = word := hdecomp
        _ = List.ofFn w := rfl
    apply Sigma.subtype_ext
    · exact Subtype.ext hfun
    · exact Fin.ext hprelen

/-- The word reconstructed from a marked cut is exactly its concatenated
binary word, with all p positions retained. -/
theorem binaryWordMarkedCutFinEquiv_word (p r : ℕ)
    (cut : binaryWordMarkedCutStratum p r) :
    List.ofFn (binaryWordMarkedCutFinEquiv p r cut).1.val =
      ((cut.val.1 ++ [true]) ++ cut.val.2) := by
  rcases cut with ⟨⟨pre, post⟩, hcut⟩
  let word : List Bool := (pre ++ [true]) ++ post
  have hlen : word.length = p := hcut.2.1
  let w : Fin p → Bool :=
    fun i => word.get (Fin.cast hlen.symm i)
  have hrepr : List.ofFn w = word := by
    dsimp [w]
    calc
      List.ofFn (fun i : Fin p => word.get (Fin.cast hlen.symm i)) =
          List.ofFn word.get := (List.ofFn_congr hlen word.get).symm
      _ = word := List.ofFn_get word
  change List.ofFn w = word
  exact hrepr

/-- Each exact-weight binary word contributes exactly r copies to the sum
over marked cuts. The summand may be any function of the unmarked word. -/
theorem binaryWordMarkedCutStratum_sum_eq_r_mul_word_sum
    (p r : ℕ) (f : binaryWordFinStratum p r → ℂ) :
    (∑ cut : binaryWordMarkedCutStratum p r,
      f (binaryWordMarkedCutFinEquiv p r cut).1) =
      (r : ℂ) * ∑ w : binaryWordFinStratum p r, f w := by
  classical
  rw [← binaryWordFinMarkedStratum_sum_eq_r_mul p r f]
  exact Fintype.sum_equiv (binaryWordMarkedCutFinEquiv p r)
    (fun cut => f (binaryWordMarkedCutFinEquiv p r cut).1)
    (fun marked => f marked.1)
    (by intro cut; rfl)

/-- The marked-cut trace sum equals r times the unmarked exact-count
binary-word trace sum. This is the word-side multiplicity identity. -/
theorem binaryWordMarkedCutStratum_sum_trace_eq_r_mul_word_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (p r : ℕ) :
    (∑ cut : binaryWordMarkedCutStratum p r,
      Matrix.trace
        (binaryWordMatrix K N ((cut.val.1 ++ [true]) ++ cut.val.2))) =
      (r : ℂ) *
        ∑ w : binaryWordFinStratum p r,
          Matrix.trace (binaryWordMatrix K N (List.ofFn w.val)) := by
  classical
  calc
    _ = ∑ cut : binaryWordMarkedCutStratum p r,
          Matrix.trace
            (binaryWordMatrix K N
              (List.ofFn (binaryWordMarkedCutFinEquiv p r cut).1.val)) := by
      apply Finset.sum_congr rfl
      intro cut _
      rw [← binaryWordMarkedCutFinEquiv_word p r cut]
    _ = (r : ℂ) *
          ∑ w : binaryWordFinStratum p r,
            Matrix.trace (binaryWordMatrix K N (List.ofFn w.val)) := by
      exact binaryWordMarkedCutStratum_sum_eq_r_mul_word_sum p r
        (fun w => Matrix.trace (binaryWordMatrix K N (List.ofFn w.val)))


/-- Reindexing the fixed gap-offset stratum through the finite vector model
preserves its complete cyclic-gap trace sum. The vector conversion keeps
the ordered r coordinates and the actual offset. -/
theorem binaryWordGapOffsetStratum_sum_trace_eq_vector_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (p r : ℕ) :
    (∑ data : binaryWordGapOffsetStratum p r,
      cyclicGapTrace K N data.val.val.1) =
    ∑ data : binaryWordGapOffsetVectorStratum p r,
      cyclicGapTrace K N
        (List.ofFn (fun i : Fin r => (data.val.1 i).val)) := by
  classical
  exact Fintype.sum_equiv (binaryWordGapOffsetVectorEquiv p r)
    (fun data => cyclicGapTrace K N data.val.val.1)
    (fun data => cyclicGapTrace K N
      (List.ofFn (fun i : Fin r => (data.val.1 i).val)))
    (by
      intro data
      rcases data with ⟨⟨⟨gaps, offset⟩, hoffset⟩, hrp, hlen, hsum⟩
      simp [binaryWordGapOffsetVectorEquiv,
        binaryWordGapListToFinVector_ofFn])

/-- The two exact multiplicities combine into the weighted H10 trace
identity. Every marked cut is counted once on the common middle sum;
grouping it by its underlying binary word gives r, while grouping it by
its gap vector gives p. No periodic orbit is quotiented. -/
theorem binaryWordFinStratum_weighted_trace_eq_gap_vector_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (p r : ℕ) :
    (r : ℂ) *
      ∑ w : binaryWordFinStratum p r,
        Matrix.trace (binaryWordMatrix K N (List.ofFn w.val)) =
    (p : ℂ) *
      ∑ gaps : binaryWordGapVectorStratum p r,
        cyclicGapTrace K N
          (List.ofFn (fun i : Fin r => (gaps.val i).val)) := by
  calc
    (r : ℂ) *
        ∑ w : binaryWordFinStratum p r,
          Matrix.trace (binaryWordMatrix K N (List.ofFn w.val)) =
      ∑ cut : binaryWordMarkedCutStratum p r,
        Matrix.trace
          (binaryWordMatrix K N ((cut.val.1 ++ [true]) ++ cut.val.2)) :=
      (binaryWordMarkedCutStratum_sum_trace_eq_r_mul_word_sum
        K N p r).symm
    _ = ∑ data : binaryWordGapOffsetStratum p r,
          cyclicGapTrace K N data.val.val.1 :=
      binaryWordMarkedCutStratum_sum_trace_eq_gapOffsetStratum_sum
        K N p r
    _ = ∑ data : binaryWordGapOffsetVectorStratum p r,
          cyclicGapTrace K N
            (List.ofFn (fun i : Fin r => (data.val.1 i).val)) :=
      binaryWordGapOffsetStratum_sum_trace_eq_vector_sum
        K N p r
    _ = (p : ℂ) *
          ∑ gaps : binaryWordGapVectorStratum p r,
            cyclicGapTrace K N
              (List.ofFn (fun i : Fin r => (gaps.val i).val)) :=
      binaryWordGapOffsetVectorStratum_sum_trace_eq_card_mul_gap_sum
        K N p r



/-- Substituting K*N for the second letter converts a nonnegative gap
a into the positive block K^(a+1)*N. This is the exact change of gap
coordinates used by the p=10 boundary representatives. -/
theorem cyclicGapTrace_K_mul_N_eq_succ_gaps
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (gaps : List ℕ) :
    cyclicGapTrace K (K * N) gaps =
      cyclicGapTrace K N (gaps.map Nat.succ) := by
  unfold cyclicGapTrace
  have hblock :
      gaps.map (fun a => K ^ a * (K * N)) =
        gaps.map (fun a => K ^ (a + 1) * N) := by
    apply List.map_congr_left
    intro a ha
    calc
      K ^ a * (K * N) = (K ^ a * K) * N := by
        rw [← Matrix.mul_assoc]
      _ = K ^ (a + 1) * N := by
        rw [pow_succ]
  have hshift :
      gaps.map (fun a => K ^ (a + 1) * N) =
        (gaps.map Nat.succ).map (fun a => K ^ a * N) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    apply congrArg (fun e : ℕ => K ^ e * N)
    omega
  calc
    Matrix.trace
        ((gaps.map (fun a => K ^ a * (K * N))).prod) =
        Matrix.trace
          ((gaps.map (fun a => K ^ (a + 1) * N)).prod) :=
      congrArg
        (fun blocks : List (Matrix n n ℂ) => Matrix.trace blocks.prod)
        hblock
    _ = Matrix.trace
          (((gaps.map Nat.succ).map (fun a => K ^ a * N)).prod) :=
      congrArg
        (fun blocks : List (Matrix n n ℂ) => Matrix.trace blocks.prod)
        hshift
    _ = cyclicGapTrace K N (gaps.map Nat.succ) := rfl

/-- The exact weighted H10 identity in the positive-gap coordinates used by
the explicit p=10 cyclic representatives. Each selected K*N letter raises
the preceding K-run exponent by one; the r-fold and p-fold multiplicities
remain exactly those already proved. -/
theorem binaryWordFinStratum_weighted_trace_eq_positive_gap_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (p r : ℕ) :
    (r : ℂ) *
      ∑ w : binaryWordFinStratum p r,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (p : ℂ) *
      ∑ gaps : binaryWordGapVectorStratum p r,
        cyclicGapTrace K N
          ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ) := by
  calc
    (r : ℂ) *
        ∑ w : binaryWordFinStratum p r,
          Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
      (p : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum p r,
          cyclicGapTrace K (K * N)
            (List.ofFn (fun i : Fin r => (gaps.val i).val)) :=
      binaryWordFinStratum_weighted_trace_eq_gap_vector_sum K (K * N) p r
    _ = (p : ℂ) *
          ∑ gaps : binaryWordGapVectorStratum p r,
            cyclicGapTrace K N
              ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ) := by
      apply congrArg (fun z : ℂ => (p : ℂ) * z)
      apply Finset.sum_congr rfl
      intro gaps hgaps
      exact cyclicGapTrace_K_mul_N_eq_succ_gaps K N
        (List.ofFn (fun i : Fin r => (gaps.val i).val))




/-! ### The p=10 positive-gap orbit decomposition

For fixed r, positive gap tuples are obtained by adding one to every
coordinate of the finite nonnegative gap vectors. The finite sets below
are partitioned by the cyclic orbits of the representatives already used
in the p=10 boundary formulas. Periodic representatives have smaller
orbit cardinality and therefore retain their reduced weights.
-/

/-- All ordered positive gap tuples in the p=10, r-insertion stratum. -/
noncomputable def binaryWordP10PositiveGapListFinset (r : ℕ) :
    Finset (List ℕ) :=
  (Finset.univ : Finset (binaryWordGapVectorStratum 10 r)).image
    (fun gaps =>
      (List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ)

/-- Canonical p=10 cyclic representatives for the two-insertion stratum. -/
def binaryWordP10GapOrbitReps2 : Finset (List ℕ) :=
  {([1, 9] : List ℕ), [2, 8], [3, 7], [4, 6], [5, 5]}

/-- Canonical p=10 cyclic representatives for the three-insertion stratum.
The twelve orbits all have length three. -/
def binaryWordP10GapOrbitReps3 : Finset (List ℕ) :=
  {([1, 1, 8] : List ℕ), [1, 2, 7], [1, 3, 6], [1, 4, 5],
   [1, 5, 4], [1, 6, 3], [1, 7, 2], [2, 2, 6],
   [2, 3, 5], [2, 4, 4], [2, 5, 3], [3, 3, 4]}

/-- Canonical p=10 cyclic representatives for the four-insertion stratum. -/
def binaryWordP10GapOrbitReps4 : Finset (List ℕ) :=
  {([1, 1, 1, 7] : List ℕ), [1, 1, 2, 6], [1, 1, 3, 5],
   [1, 1, 4, 4], [1, 1, 5, 3], [1, 1, 6, 2],
   [1, 2, 1, 6], [1, 2, 2, 5], [1, 2, 3, 4], [1, 2, 4, 3],
   [1, 2, 5, 2], [1, 3, 1, 5], [1, 3, 2, 4], [1, 3, 3, 3],
   [1, 3, 4, 2], [1, 4, 1, 4], [1, 4, 2, 3], [1, 4, 3, 2],
   [1, 5, 2, 2], [2, 2, 2, 4], [2, 2, 3, 3], [2, 3, 2, 3]}

/-- Canonical p=10 cyclic representatives for the five-insertion stratum.
The 25 aperiodic classes have orbit size five; the all-equal class has size one. -/
def binaryWordP10GapOrbitReps5 : Finset (List ℕ) :=
  {([1, 1, 1, 1, 6] : List ℕ), [1, 1, 1, 2, 5], [1, 1, 1, 3, 4], [1, 1, 1, 4, 3], [1, 1, 1, 5, 2], [1, 1, 2, 1, 5], [1, 1, 2, 2, 4], [1, 1, 2, 3, 3], [1, 1, 2, 4, 2], [1, 1, 3, 1, 4], [1, 1, 3, 2, 3], [1, 1, 3, 3, 2], [1, 1, 4, 1, 3], [1, 1, 4, 2, 2], [1, 1, 5, 1, 2], [1, 2, 1, 2, 4], [1, 2, 1, 3, 3], [1, 2, 1, 4, 2], [1, 2, 2, 1, 4], [1, 2, 2, 2, 3], [1, 2, 2, 3, 2], [1, 2, 3, 1, 3], [1, 2, 3, 2, 2], [1, 3, 1, 3, 2], [1, 3, 2, 2, 2], [2, 2, 2, 2, 2]}

/-- Canonical p=10 cyclic representatives for the six-insertion stratum. -/
def binaryWordP10GapOrbitReps6 : Finset (List ℕ) :=
  {([1, 1, 1, 1, 1, 5] : List ℕ), [1, 1, 1, 1, 2, 4],
   [1, 1, 1, 1, 3, 3], [1, 1, 1, 1, 4, 2],
   [1, 1, 1, 2, 1, 4], [1, 1, 1, 2, 2, 3],
   [1, 1, 1, 2, 3, 2], [1, 1, 1, 3, 1, 3],
   [1, 1, 1, 3, 2, 2], [1, 1, 1, 4, 1, 2],
   [1, 1, 2, 1, 1, 4], [1, 1, 2, 1, 2, 3],
   [1, 1, 2, 1, 3, 2], [1, 1, 2, 2, 1, 3],
   [1, 1, 2, 2, 2, 2], [1, 1, 2, 3, 1, 2],
   [1, 1, 3, 1, 1, 3], [1, 1, 3, 1, 2, 2],
   [1, 1, 3, 2, 1, 2], [1, 2, 1, 2, 1, 3],
   [1, 2, 1, 2, 2, 2], [1, 2, 2, 1, 2, 2]}

/-- Canonical p=10 cyclic representatives for the seven-insertion stratum.
The twelve positive-gap orbits all have length seven. -/
def binaryWordP10GapOrbitReps7 : Finset (List ℕ) :=
  {([1, 1, 1, 1, 1, 1, 4] : List ℕ), [1, 1, 1, 1, 1, 2, 3], [1, 1, 1, 1, 1, 3, 2], [1, 1, 1, 1, 2, 1, 3], [1, 1, 1, 1, 2, 2, 2], [1, 1, 1, 1, 3, 1, 2], [1, 1, 1, 2, 1, 1, 3], [1, 1, 1, 2, 1, 2, 2], [1, 1, 1, 2, 2, 1, 2], [1, 1, 1, 3, 1, 1, 2], [1, 1, 2, 1, 1, 2, 2], [1, 1, 2, 1, 2, 1, 2]}

/-- Canonical p=10 cyclic representatives for the eight-insertion stratum. -/
def binaryWordP10GapOrbitReps8 : Finset (List ℕ) :=
  {([1, 1, 1, 1, 1, 1, 1, 3] : List ℕ),
   [1, 1, 1, 1, 1, 1, 2, 2],
   [1, 1, 1, 1, 1, 2, 1, 2],
   [1, 1, 1, 1, 2, 1, 1, 2],
   [1, 1, 1, 2, 1, 1, 1, 2]}

/-- The unique p=10 cyclic representative for the nine-insertion stratum.
Its nine positive gaps consist of one 2 and eight 1s. -/
def binaryWordP10GapOrbitReps9 : Finset (List ℕ) :=
  {([2, 1, 1, 1, 1, 1, 1, 1, 1] : List ℕ)}

/-- The unique p=10 cyclic representative for the ten-insertion stratum. -/
def binaryWordP10GapOrbitReps10 : Finset (List ℕ) :=
  {(List.replicate 10 1 : List ℕ)}

/-- The two-insertion positive compositions are partitioned by the listed
cyclic gap orbits. -/
theorem binaryWordP10GapOrbitPartition2 :
    binaryWordP10PositiveGapListFinset 2 =
      binaryWordP10GapOrbitReps2.biUnion cyclicGapOrbit := by
  classical
  set_option maxRecDepth 4096 in decide

-- The r=3 partition has 36 positive compositions and twelve length-three orbits.
set_option maxRecDepth 8192 in
/-- The three-insertion positive compositions are partitioned by the listed
cyclic gap orbits. -/
theorem binaryWordP10GapOrbitPartition3 :
    binaryWordP10PositiveGapListFinset 3 =
      binaryWordP10GapOrbitReps3.biUnion cyclicGapOrbit := by
  classical
  decide

-- The r=4 finite composition enumeration exceeds the default elaboration limits.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- The four-insertion positive compositions are partitioned by the listed
cyclic gap orbits. -/
theorem binaryWordP10GapOrbitPartition4 :
    binaryWordP10PositiveGapListFinset 4 =
      binaryWordP10GapOrbitReps4.biUnion cyclicGapOrbit := by
  classical
  decide

-- The five-insertion orbit partition checks all 126 positive compositions.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 12000000 in
/-- The five-insertion positive compositions are partitioned by the 26
listed cyclic gap orbits. The periodic all-twos tuple contributes one element. -/
theorem binaryWordP10GapOrbitPartition5 :
    binaryWordP10PositiveGapListFinset 5 =
      binaryWordP10GapOrbitReps5.biUnion cyclicGapOrbit := by
  classical
  decide

-- The r=6 finite composition enumeration has a larger normalization tree.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- The six-insertion positive compositions are partitioned by the listed
cyclic gap orbits. -/
theorem binaryWordP10GapOrbitPartition6 :
    binaryWordP10PositiveGapListFinset 6 =
      binaryWordP10GapOrbitReps6.biUnion cyclicGapOrbit := by
  classical
  decide

-- The 84 positive seven-part compositions split into twelve cyclic orbits.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 12000000 in
/-- The seven-insertion positive compositions are partitioned by the twelve
listed cyclic gap orbits. Each orbit has cardinality seven. -/
theorem binaryWordP10GapOrbitPartition7 :
    binaryWordP10PositiveGapListFinset 7 =
      binaryWordP10GapOrbitReps7.biUnion cyclicGapOrbit := by
  classical
  decide

-- The explicit r=8 orbit partition exceeds Lean's default recursion bound.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- The eight-insertion positive compositions are partitioned by the listed
cyclic gap orbits. -/
theorem binaryWordP10GapOrbitPartition8 :
    binaryWordP10PositiveGapListFinset 8 =
      binaryWordP10GapOrbitReps8.biUnion cyclicGapOrbit := by
  classical
  decide

-- The finite decider enumerates the nine possible positions of the
-- unique gap of size two and their cyclic rotations.
set_option maxRecDepth 4096 in
/-- The nine-insertion positive compositions form one cyclic orbit:
the unique gap of size two can occur at any of the nine positions. -/
theorem binaryWordP10GapOrbitPartition9 :
    binaryWordP10PositiveGapListFinset 9 =
      binaryWordP10GapOrbitReps9.biUnion cyclicGapOrbit := by
  classical
  decide

/-- The ten-insertion positive composition is its single cyclic orbit. -/
theorem binaryWordP10GapOrbitPartition10 :
    binaryWordP10PositiveGapListFinset 10 =
      binaryWordP10GapOrbitReps10.biUnion cyclicGapOrbit := by
  classical
  decide

/-- A disjoint cyclic-orbit partition converts a sum over all tuples into
the sum of the orbit sums. -/
theorem cyclicGapTrace_sum_biUnion_orbits
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (reps : Finset (List ℕ))
    (hdisj : Set.PairwiseDisjoint (↑reps) cyclicGapOrbit) :
    (∑ gaps ∈ reps.biUnion cyclicGapOrbit, cyclicGapTrace K N gaps) =
      ∑ rep ∈ reps,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  classical
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro rep hrep
  exact cyclicGapTrace_sum_orbit_eq K N rep


/-- A pairwise disjoint family of finite cyclic orbits gives a
pairwise-disjoint family in the sense required by the finite-sum theorem. -/
theorem binaryWordP10GapOrbitReps_pairwise_disjoint
    (reps : Finset (List ℕ))
    (h : ∀ a ∈ reps, ∀ b ∈ reps, a ≠ b →
      Disjoint (cyclicGapOrbit a) (cyclicGapOrbit b)) :
    Set.PairwiseDisjoint (↑reps) cyclicGapOrbit := by
  intro a ha b hb hab
  change Disjoint (cyclicGapOrbit a) (cyclicGapOrbit b)
  exact h a ha b hb hab

/-- The p=10 r=2 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP10GapOrbitReps2_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP10GapOrbitReps2) cyclicGapOrbit := by
  classical
  apply binaryWordP10GapOrbitReps_pairwise_disjoint
  intro a ha b hb hab
  simp only [binaryWordP10GapOrbitReps2, Finset.mem_insert,
    Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases hb with rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (hab rfl).elim
      | decide

-- The twelve r=3 orbit representatives are pairwise disjoint.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- The p=10 r=3 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP10GapOrbitReps3_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP10GapOrbitReps3) cyclicGapOrbit := by
  classical
  apply binaryWordP10GapOrbitReps_pairwise_disjoint
  intro a ha b hb hab
  simp only [binaryWordP10GapOrbitReps3, Finset.mem_insert,
    Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (hab rfl).elim
      | decide

-- Finite pairwise orbit checks for 22 representatives require more reduction depth.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The p=10 r=4 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP10GapOrbitReps4_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP10GapOrbitReps4) cyclicGapOrbit := by
  classical
  apply binaryWordP10GapOrbitReps_pairwise_disjoint
  intro a ha b hb hab
  simp only [binaryWordP10GapOrbitReps4, Finset.mem_insert,
    Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (hab rfl).elim
      | decide

-- Finite pairwise orbit checks for 22 representatives require a larger recursion bound.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 12000000 in
-- The 26 r=5 representatives are checked against their actual finite cyclic orbits.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
/-- The p=10 r=5 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP10GapOrbitReps5_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP10GapOrbitReps5) cyclicGapOrbit := by
  classical
  apply binaryWordP10GapOrbitReps_pairwise_disjoint
  intro a ha b hb hab
  simp only [binaryWordP10GapOrbitReps5, Finset.mem_insert,
    Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (hab rfl).elim
      | decide

/-- The p=10 r=6 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP10GapOrbitReps6_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP10GapOrbitReps6) cyclicGapOrbit := by
  classical
  apply binaryWordP10GapOrbitReps_pairwise_disjoint
  intro a ha b hb hab
  simp only [binaryWordP10GapOrbitReps6, Finset.mem_insert,
    Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (hab rfl).elim
      | decide

-- The twelve length-seven orbits have pairwise distinct cyclic rotations.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The p=10 r=7 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP10GapOrbitReps7_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP10GapOrbitReps7) cyclicGapOrbit := by
  classical
  apply binaryWordP10GapOrbitReps_pairwise_disjoint
  intro a ha b hb hab
  simp only [binaryWordP10GapOrbitReps7, Finset.mem_insert,
    Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (hab rfl).elim
      | decide

/-- The p=10 r=8 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP10GapOrbitReps8_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP10GapOrbitReps8) cyclicGapOrbit := by
  classical
  apply binaryWordP10GapOrbitReps_pairwise_disjoint
  intro a ha b hb hab
  simp only [binaryWordP10GapOrbitReps8, Finset.mem_insert,
    Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases hb with rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (hab rfl).elim
      | decide

/-- The p=10 r=9 cyclic representative orbit is a singleton family. -/
theorem binaryWordP10GapOrbitReps9_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP10GapOrbitReps9) cyclicGapOrbit := by
  classical
  apply binaryWordP10GapOrbitReps_pairwise_disjoint
  intro a ha b hb hab
  simp only [binaryWordP10GapOrbitReps9, Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact (hab rfl).elim

/-- The p=10 r=10 cyclic representative orbits are pairwise disjoint. -/
theorem binaryWordP10GapOrbitReps10_pairwise_disjoint :
    Set.PairwiseDisjoint (↑binaryWordP10GapOrbitReps10) cyclicGapOrbit := by
  classical
  apply binaryWordP10GapOrbitReps_pairwise_disjoint
  intro a ha b hb hab
  simp only [binaryWordP10GapOrbitReps10, Finset.mem_insert,
    Finset.mem_singleton] at ha hb
  rcases ha with rfl
  rcases hb with rfl
  exact (hab rfl).elim

/-- Orbit sums for the p=10 two-insertion stratum. -/
theorem binaryWordP10GapTraceOrbitSum2
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP10PositiveGapListFinset 2,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP10GapOrbitReps2,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP10GapOrbitPartition2]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP10GapOrbitReps2_pairwise_disjoint

/-- Orbit sums for the p=10 three-insertion stratum. -/
theorem binaryWordP10GapTraceOrbitSum3
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP10PositiveGapListFinset 3,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP10GapOrbitReps3,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP10GapOrbitPartition3]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP10GapOrbitReps3_pairwise_disjoint

/-- Orbit sums for the p=10 four-insertion stratum. -/
theorem binaryWordP10GapTraceOrbitSum4
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP10PositiveGapListFinset 4,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP10GapOrbitReps4,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP10GapOrbitPartition4]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP10GapOrbitReps4_pairwise_disjoint

/-- Orbit sums for the p=10 five-insertion stratum. -/
theorem binaryWordP10GapTraceOrbitSum5
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP10PositiveGapListFinset 5,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP10GapOrbitReps5,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP10GapOrbitPartition5]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP10GapOrbitReps5_pairwise_disjoint

/-- Orbit sums for the p=10 six-insertion stratum. -/
theorem binaryWordP10GapTraceOrbitSum6
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP10PositiveGapListFinset 6,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP10GapOrbitReps6,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP10GapOrbitPartition6]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP10GapOrbitReps6_pairwise_disjoint

/-- Orbit sums for the p=10 seven-insertion stratum. -/
theorem binaryWordP10GapTraceOrbitSum7
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP10PositiveGapListFinset 7,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP10GapOrbitReps7,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP10GapOrbitPartition7]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP10GapOrbitReps7_pairwise_disjoint

/-- Orbit sums for the p=10 eight-insertion stratum. -/
theorem binaryWordP10GapTraceOrbitSum8
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP10PositiveGapListFinset 8,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP10GapOrbitReps8,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP10GapOrbitPartition8]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP10GapOrbitReps8_pairwise_disjoint

/-- Orbit sums for the p=10 nine-insertion stratum. -/
theorem binaryWordP10GapTraceOrbitSum9
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP10PositiveGapListFinset 9,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP10GapOrbitReps9,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP10GapOrbitPartition9]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP10GapOrbitReps9_pairwise_disjoint

/-- Orbit sums for the p=10 ten-insertion stratum. -/
theorem binaryWordP10GapTraceOrbitSum10
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ gaps ∈ binaryWordP10PositiveGapListFinset 10,
      cyclicGapTrace K N gaps) =
      ∑ rep ∈ binaryWordP10GapOrbitReps10,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  rw [binaryWordP10GapOrbitPartition10]
  exact cyclicGapTrace_sum_biUnion_orbits K N _
    binaryWordP10GapOrbitReps10_pairwise_disjoint

/-- The exact distinct-orbit cardinalities of all canonical p=10 gap
representatives. The reduced values 1, 2, 3, and 4 are precisely the
periodic-orbit corrections behind the coefficients five in the existing
boundary sums. -/
theorem binaryWordP10GapOrbitRepresentativeCardinals :
    ([(cyclicGapOrbit [1, 9]).card,
      (cyclicGapOrbit [2, 8]).card,
      (cyclicGapOrbit [3, 7]).card,
      (cyclicGapOrbit [4, 6]).card,
      (cyclicGapOrbit [5, 5]).card] : List ℕ) = [2, 2, 2, 2, 1] ∧
    ([(cyclicGapOrbit [1, 1, 1, 7]).card,
      (cyclicGapOrbit [1, 1, 2, 6]).card,
      (cyclicGapOrbit [1, 1, 3, 5]).card,
      (cyclicGapOrbit [1, 1, 4, 4]).card,
      (cyclicGapOrbit [1, 1, 5, 3]).card,
      (cyclicGapOrbit [1, 1, 6, 2]).card,
      (cyclicGapOrbit [1, 2, 1, 6]).card,
      (cyclicGapOrbit [1, 2, 2, 5]).card,
      (cyclicGapOrbit [1, 2, 3, 4]).card,
      (cyclicGapOrbit [1, 2, 4, 3]).card,
      (cyclicGapOrbit [1, 2, 5, 2]).card,
      (cyclicGapOrbit [1, 3, 1, 5]).card,
      (cyclicGapOrbit [1, 3, 2, 4]).card,
      (cyclicGapOrbit [1, 3, 3, 3]).card,
      (cyclicGapOrbit [1, 3, 4, 2]).card,
      (cyclicGapOrbit [1, 4, 1, 4]).card,
      (cyclicGapOrbit [1, 4, 2, 3]).card,
      (cyclicGapOrbit [1, 4, 3, 2]).card,
      (cyclicGapOrbit [1, 5, 2, 2]).card,
      (cyclicGapOrbit [2, 2, 2, 4]).card,
      (cyclicGapOrbit [2, 2, 3, 3]).card,
      (cyclicGapOrbit [2, 3, 2, 3]).card] : List ℕ) =
        [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
         4, 4, 4, 4, 2, 4, 4, 4, 4, 4, 2] ∧
    ([(cyclicGapOrbit [1, 1, 1, 1, 1, 5]).card,
      (cyclicGapOrbit [1, 1, 1, 1, 2, 4]).card,
      (cyclicGapOrbit [1, 1, 1, 1, 3, 3]).card,
      (cyclicGapOrbit [1, 1, 1, 1, 4, 2]).card,
      (cyclicGapOrbit [1, 1, 1, 2, 1, 4]).card,
      (cyclicGapOrbit [1, 1, 1, 2, 2, 3]).card,
      (cyclicGapOrbit [1, 1, 1, 2, 3, 2]).card,
      (cyclicGapOrbit [1, 1, 1, 3, 1, 3]).card,
      (cyclicGapOrbit [1, 1, 1, 3, 2, 2]).card,
      (cyclicGapOrbit [1, 1, 1, 4, 1, 2]).card,
      (cyclicGapOrbit [1, 1, 2, 1, 1, 4]).card,
      (cyclicGapOrbit [1, 1, 2, 1, 2, 3]).card,
      (cyclicGapOrbit [1, 1, 2, 1, 3, 2]).card,
      (cyclicGapOrbit [1, 1, 2, 2, 1, 3]).card,
      (cyclicGapOrbit [1, 1, 2, 2, 2, 2]).card,
      (cyclicGapOrbit [1, 1, 2, 3, 1, 2]).card,
      (cyclicGapOrbit [1, 1, 3, 1, 1, 3]).card,
      (cyclicGapOrbit [1, 1, 3, 1, 2, 2]).card,
      (cyclicGapOrbit [1, 1, 3, 2, 1, 2]).card,
      (cyclicGapOrbit [1, 2, 1, 2, 1, 3]).card,
      (cyclicGapOrbit [1, 2, 1, 2, 2, 2]).card,
      (cyclicGapOrbit [1, 2, 2, 1, 2, 2]).card] : List ℕ) =
        [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
         6, 6, 6, 6, 6, 3, 6, 6, 6, 6, 3] ∧
    ([(cyclicGapOrbit [1, 1, 1, 1, 1, 1, 1, 3]).card,
      (cyclicGapOrbit [1, 1, 1, 1, 1, 1, 2, 2]).card,
      (cyclicGapOrbit [1, 1, 1, 1, 1, 2, 1, 2]).card,
      (cyclicGapOrbit [1, 1, 1, 1, 2, 1, 1, 2]).card,
      (cyclicGapOrbit [1, 1, 1, 2, 1, 1, 1, 2]).card] : List ℕ) =
        [8, 8, 8, 8, 4] ∧
    ([(cyclicGapOrbit (List.replicate 10 1)).card] : List ℕ) = [1] := by
  decide


/-- The 26 p=10 five-insertion gap representatives have orbit sizes
five except for the period-one all-twos tuple. -/
theorem binaryWordP10GapOrbitRepresentativeCardinals5 :
    ([(cyclicGapOrbit [1, 1, 1, 1, 6]).card,
      (cyclicGapOrbit [1, 1, 1, 2, 5]).card,
      (cyclicGapOrbit [1, 1, 1, 3, 4]).card,
      (cyclicGapOrbit [1, 1, 1, 4, 3]).card,
      (cyclicGapOrbit [1, 1, 1, 5, 2]).card,
      (cyclicGapOrbit [1, 1, 2, 1, 5]).card,
      (cyclicGapOrbit [1, 1, 2, 2, 4]).card,
      (cyclicGapOrbit [1, 1, 2, 3, 3]).card,
      (cyclicGapOrbit [1, 1, 2, 4, 2]).card,
      (cyclicGapOrbit [1, 1, 3, 1, 4]).card,
      (cyclicGapOrbit [1, 1, 3, 2, 3]).card,
      (cyclicGapOrbit [1, 1, 3, 3, 2]).card,
      (cyclicGapOrbit [1, 1, 4, 1, 3]).card,
      (cyclicGapOrbit [1, 1, 4, 2, 2]).card,
      (cyclicGapOrbit [1, 1, 5, 1, 2]).card,
      (cyclicGapOrbit [1, 2, 1, 2, 4]).card,
      (cyclicGapOrbit [1, 2, 1, 3, 3]).card,
      (cyclicGapOrbit [1, 2, 1, 4, 2]).card,
      (cyclicGapOrbit [1, 2, 2, 1, 4]).card,
      (cyclicGapOrbit [1, 2, 2, 2, 3]).card,
      (cyclicGapOrbit [1, 2, 2, 3, 2]).card,
      (cyclicGapOrbit [1, 2, 3, 1, 3]).card,
      (cyclicGapOrbit [1, 2, 3, 2, 2]).card,
      (cyclicGapOrbit [1, 3, 1, 3, 2]).card,
      (cyclicGapOrbit [1, 3, 2, 2, 2]).card,
      (cyclicGapOrbit [2, 2, 2, 2, 2]).card] : List ℕ) = [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 1] := by
  decide


/-- The twelve p=10 seven-insertion gap representatives all have
full cyclic orbit cardinality seven. -/
theorem binaryWordP10GapOrbitRepresentativeCardinals7 :
    ([(cyclicGapOrbit [1, 1, 1, 1, 1, 1, 4]).card,
      (cyclicGapOrbit [1, 1, 1, 1, 1, 2, 3]).card,
      (cyclicGapOrbit [1, 1, 1, 1, 1, 3, 2]).card,
      (cyclicGapOrbit [1, 1, 1, 1, 2, 1, 3]).card,
      (cyclicGapOrbit [1, 1, 1, 1, 2, 2, 2]).card,
      (cyclicGapOrbit [1, 1, 1, 1, 3, 1, 2]).card,
      (cyclicGapOrbit [1, 1, 1, 2, 1, 1, 3]).card,
      (cyclicGapOrbit [1, 1, 1, 2, 1, 2, 2]).card,
      (cyclicGapOrbit [1, 1, 1, 2, 2, 1, 2]).card,
      (cyclicGapOrbit [1, 1, 1, 3, 1, 1, 2]).card,
      (cyclicGapOrbit [1, 1, 2, 1, 1, 2, 2]).card,
      (cyclicGapOrbit [1, 1, 2, 1, 2, 1, 2]).card] : List ℕ) = [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] := by
  decide


/-- Summing over the image of the positive-gap encoding is the same as
summing over the original gap-vector subtype. The encoding is injective:
subtracting one from each coordinate recovers the vector. -/
theorem binaryWordP10PositiveGapListFinset_sum_eq_gapVector_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (r : ℕ) :
    (∑ gaps ∈ binaryWordP10PositiveGapListFinset r,
      cyclicGapTrace K N gaps) =
    ∑ gaps : binaryWordGapVectorStratum 10 r,
      cyclicGapTrace K N
        ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ) := by
  classical
  let positiveList : binaryWordGapVectorStratum 10 r → List ℕ :=
    fun gaps =>
      (List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ
  have hpositiveList_injective : Function.Injective positiveList := by
    intro a b hab
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hlist :
        List.ofFn (fun i : Fin r => (a.val i).val) =
          List.ofFn (fun i : Fin r => (b.val i).val) :=
      (List.map_inj_right (fun x y hxy => Nat.succ.inj hxy)).mp hab
    have hfun :
        (fun i : Fin r => (a.val i).val) =
          (fun i : Fin r => (b.val i).val) :=
      List.ofFn_injective hlist
    exact congrFun hfun i
  change
    (∑ gaps ∈
      (Finset.univ : Finset (binaryWordGapVectorStratum 10 r)).image positiveList,
      cyclicGapTrace K N gaps) =
    ∑ gaps : binaryWordGapVectorStratum 10 r,
      cyclicGapTrace K N (positiveList gaps)
  rw [Finset.sum_image (fun a _ b _ h => hpositiveList_injective h)]


/-- Exact H10 two-N trace sum, reindexed by the five canonical cyclic
gap representatives. The factor two counts marked true positions;
the orbit cardinalities retain the periodic class correctly. -/
theorem binaryWordP10WordTraceOrbitSum2
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (2 : ℂ) *
      ∑ w : binaryWordFinStratum 10 2,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (10 : ℂ) *
      ∑ rep ∈ binaryWordP10GapOrbitReps2,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (10 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 10 2,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 2 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 10 2
    _ = (10 : ℂ) *
        ∑ gaps ∈ binaryWordP10PositiveGapListFinset 2,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP10PositiveGapListFinset_sum_eq_gapVector_sum K N 2]
    _ = (10 : ℂ) *
        ∑ rep ∈ binaryWordP10GapOrbitReps2,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP10GapTraceOrbitSum2 K N]


/-- Exact H10 three-N trace sum, reindexed by the twelve canonical
cyclic gap representatives. Every orbit has size three. -/
theorem binaryWordP10WordTraceOrbitSum3
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (3 : ℂ) *
      ∑ w : binaryWordFinStratum 10 3,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (10 : ℂ) *
      ∑ rep ∈ binaryWordP10GapOrbitReps3,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (10 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 10 3,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 3 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 10 3
    _ = (10 : ℂ) *
        ∑ gaps ∈ binaryWordP10PositiveGapListFinset 3,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP10PositiveGapListFinset_sum_eq_gapVector_sum K N 3]
    _ = (10 : ℂ) *
        ∑ rep ∈ binaryWordP10GapOrbitReps3,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP10GapTraceOrbitSum3 K N]

/-- Exact H10 four-N trace sum, reindexed by the canonical cyclic
gap representatives, with all distinct-orbit multiplicities retained. -/
theorem binaryWordP10WordTraceOrbitSum4
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (4 : ℂ) *
      ∑ w : binaryWordFinStratum 10 4,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (10 : ℂ) *
      ∑ rep ∈ binaryWordP10GapOrbitReps4,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (10 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 10 4,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 4 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 10 4
    _ = (10 : ℂ) *
        ∑ gaps ∈ binaryWordP10PositiveGapListFinset 4,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP10PositiveGapListFinset_sum_eq_gapVector_sum K N 4]
    _ = (10 : ℂ) *
        ∑ rep ∈ binaryWordP10GapOrbitReps4,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP10GapTraceOrbitSum4 K N]


/-- Exact H10 five-N trace sum, reindexed by the 26 canonical cyclic
gap representatives. The periodic all-twos class retains orbit size one. -/
theorem binaryWordP10WordTraceOrbitSum5
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (5 : ℂ) *
      ∑ w : binaryWordFinStratum 10 5,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (10 : ℂ) *
      ∑ rep ∈ binaryWordP10GapOrbitReps5,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (10 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 10 5,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 5 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 10 5
    _ = (10 : ℂ) *
        ∑ gaps ∈ binaryWordP10PositiveGapListFinset 5,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP10PositiveGapListFinset_sum_eq_gapVector_sum K N 5]
    _ = (10 : ℂ) *
        ∑ rep ∈ binaryWordP10GapOrbitReps5,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP10GapTraceOrbitSum5 K N]


/-- Exact H10 six-N trace sum, reindexed by the canonical cyclic
gap representatives, with all distinct-orbit multiplicities retained. -/
theorem binaryWordP10WordTraceOrbitSum6
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (6 : ℂ) *
      ∑ w : binaryWordFinStratum 10 6,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (10 : ℂ) *
      ∑ rep ∈ binaryWordP10GapOrbitReps6,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (10 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 10 6,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 6 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 10 6
    _ = (10 : ℂ) *
        ∑ gaps ∈ binaryWordP10PositiveGapListFinset 6,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP10PositiveGapListFinset_sum_eq_gapVector_sum K N 6]
    _ = (10 : ℂ) *
        ∑ rep ∈ binaryWordP10GapOrbitReps6,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP10GapTraceOrbitSum6 K N]


/-- Exact H10 seven-N trace sum, reindexed by the twelve canonical
cyclic gap representatives. Every orbit has size seven. -/
theorem binaryWordP10WordTraceOrbitSum7
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (7 : ℂ) *
      ∑ w : binaryWordFinStratum 10 7,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (10 : ℂ) *
      ∑ rep ∈ binaryWordP10GapOrbitReps7,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (10 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 10 7,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 7 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 10 7
    _ = (10 : ℂ) *
        ∑ gaps ∈ binaryWordP10PositiveGapListFinset 7,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP10PositiveGapListFinset_sum_eq_gapVector_sum K N 7]
    _ = (10 : ℂ) *
        ∑ rep ∈ binaryWordP10GapOrbitReps7,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP10GapTraceOrbitSum7 K N]


/-- Exact H10 eight-N trace sum, reindexed by the canonical cyclic
gap representatives, including its period-four orbit of size four. -/
theorem binaryWordP10WordTraceOrbitSum8
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (8 : ℂ) *
      ∑ w : binaryWordFinStratum 10 8,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (10 : ℂ) *
      ∑ rep ∈ binaryWordP10GapOrbitReps8,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (10 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 10 8,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 8 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 10 8
    _ = (10 : ℂ) *
        ∑ gaps ∈ binaryWordP10PositiveGapListFinset 8,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP10PositiveGapListFinset_sum_eq_gapVector_sum K N 8]
    _ = (10 : ℂ) *
        ∑ rep ∈ binaryWordP10GapOrbitReps8,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP10GapTraceOrbitSum8 K N]


/-- Exact H10 nine-N trace sum, reindexed by its single cyclic
gap orbit. The orbit has cardinality nine, retaining all ten marked cuts
after normalization by the nine selected positions. -/
theorem binaryWordP10WordTraceOrbitSum9
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (9 : ℂ) *
      ∑ w : binaryWordFinStratum 10 9,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (10 : ℂ) *
      ∑ rep ∈ binaryWordP10GapOrbitReps9,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (10 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 10 9,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 9 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 10 9
    _ = (10 : ℂ) *
        ∑ gaps ∈ binaryWordP10PositiveGapListFinset 9,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP10PositiveGapListFinset_sum_eq_gapVector_sum K N 9]
    _ = (10 : ℂ) *
        ∑ rep ∈ binaryWordP10GapOrbitReps9,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP10GapTraceOrbitSum9 K N]

/-- Exact H10 ten-N trace sum. Its single representative has a
one-element orbit, so no cyclic multiplicity remains. -/
theorem binaryWordP10WordTraceOrbitSum10
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (10 : ℂ) *
      ∑ w : binaryWordFinStratum 10 10,
        Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val)) =
    (10 : ℂ) *
      ∑ rep ∈ binaryWordP10GapOrbitReps10,
        (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
  calc
    _ = (10 : ℂ) *
        ∑ gaps : binaryWordGapVectorStratum 10 10,
          cyclicGapTrace K N
            ((List.ofFn (fun i : Fin 10 => (gaps.val i).val)).map Nat.succ) :=
      binaryWordFinStratum_weighted_trace_eq_positive_gap_sum K N 10 10
    _ = (10 : ℂ) *
        ∑ gaps ∈ binaryWordP10PositiveGapListFinset 10,
          cyclicGapTrace K N gaps := by
      rw [binaryWordP10PositiveGapListFinset_sum_eq_gapVector_sum K N 10]
    _ = (10 : ℂ) *
        ∑ rep ∈ binaryWordP10GapOrbitReps10,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep := by
      rw [binaryWordP10GapTraceOrbitSum10 K N]


/-- Normalize the marked-word/cyclic-gap identity by the number r of
selected letters. The coefficient of each cyclic representative is
(10/r) times its actual orbit cardinality; this is the form needed to
compare with the explicit p=10 boundary-stratum coefficients. -/
private theorem binaryWordP10_normalize_weighted_orbit_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) (r : ℕ) (hr : r ≠ 0)
    (reps : Finset (List ℕ)) (W : ℂ)
    (h :
      (r : ℂ) * W =
        (10 : ℂ) *
          ∑ rep ∈ reps,
            (cyclicGapOrbit rep).card • cyclicGapTrace K N rep) :
    W =
      ∑ rep ∈ reps,
        ((10 : ℂ) / (r : ℂ)) *
          ((cyclicGapOrbit rep).card : ℂ) *
          cyclicGapTrace K N rep := by
  have hrC : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr
  have hdiv :
      W = ((10 : ℂ) / (r : ℂ)) *
        (∑ rep ∈ reps,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep) := by
    calc
      W = ((r : ℂ) * W) / (r : ℂ) := by
        field_simp [hrC]
      _ = ((10 : ℂ) *
          ∑ rep ∈ reps,
            (cyclicGapOrbit rep).card • cyclicGapTrace K N rep) /
          (r : ℂ) := by rw [h]
      _ = ((10 : ℂ) / (r : ℂ)) *
          (∑ rep ∈ reps,
            (cyclicGapOrbit rep).card • cyclicGapTrace K N rep) := by
        ring
  calc
    W = ((10 : ℂ) / (r : ℂ)) *
        (∑ rep ∈ reps,
          (cyclicGapOrbit rep).card • cyclicGapTrace K N rep) := hdiv
    _ = ∑ rep ∈ reps,
        ((10 : ℂ) / (r : ℂ)) *
          ((cyclicGapOrbit rep).card : ℂ) *
          cyclicGapTrace K N rep := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rep hrep
      simp only [nsmul_eq_mul]
      ring


/-- The p=10 two-letter word stratum with two selected K*N letters,
normalized to the exact cyclic-orbit coefficients. The four aperiodic
orbits have coefficient ten and the period-two orbit coefficient five. -/
theorem binaryWordP10WordTraceOrbitAverage2
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 10 2,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP10GapOrbitReps2,
      ((10 : ℂ) / (2 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) *
        cyclicGapTrace K N rep := by
  apply binaryWordP10_normalize_weighted_orbit_sum K N 2 (by norm_num)
    binaryWordP10GapOrbitReps2
  exact binaryWordP10WordTraceOrbitSum2 K N


/-- Normalize the p=10 three-N word stratum by its three marked
positions. Its twelve aperiodic gap orbits all have size three. -/
theorem binaryWordP10WordTraceOrbitAverage3
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 10 3,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP10GapOrbitReps3,
      ((10 : ℂ) / (3 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) *
        cyclicGapTrace K N rep := by
  apply binaryWordP10_normalize_weighted_orbit_sum K N 3 (by norm_num)
    binaryWordP10GapOrbitReps3
  exact binaryWordP10WordTraceOrbitSum3 K N

/-- The p=10 four-letter-selected word stratum, normalized by its
four marked positions. Periodic gap classes receive their exact
orbit-size correction through the factor ten over four. -/
theorem binaryWordP10WordTraceOrbitAverage4
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 10 4,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP10GapOrbitReps4,
      ((10 : ℂ) / (4 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) *
        cyclicGapTrace K N rep := by
  apply binaryWordP10_normalize_weighted_orbit_sum K N 4 (by norm_num)
    binaryWordP10GapOrbitReps4
  exact binaryWordP10WordTraceOrbitSum4 K N


/-- Normalize the exact-count p=10 five-N word stratum by its five
marked positions. The 25 full orbits have coefficient ten and the unique
period-one orbit has coefficient two. -/
theorem binaryWordP10WordTraceOrbitAverage5
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 10 5,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP10GapOrbitReps5,
      ((10 : ℂ) / (5 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) *
        cyclicGapTrace K N rep := by
  apply binaryWordP10_normalize_weighted_orbit_sum K N 5 (by norm_num)
    binaryWordP10GapOrbitReps5
  exact binaryWordP10WordTraceOrbitSum5 K N


/-- The p=10 six-letter-selected word stratum, normalized by its
six marked positions. Its two period-three gap classes retain weight five. -/
theorem binaryWordP10WordTraceOrbitAverage6
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 10 6,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP10GapOrbitReps6,
      ((10 : ℂ) / (6 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) *
        cyclicGapTrace K N rep := by
  apply binaryWordP10_normalize_weighted_orbit_sum K N 6 (by norm_num)
    binaryWordP10GapOrbitReps6
  exact binaryWordP10WordTraceOrbitSum6 K N


/-- Normalize the exact-count p=10 seven-N word stratum by its seven
marked positions. All twelve orbits have size seven, so every normalized
cyclic class has coefficient ten. -/
theorem binaryWordP10WordTraceOrbitAverage7
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 10 7,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP10GapOrbitReps7,
      ((10 : ℂ) / (7 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) *
        cyclicGapTrace K N rep := by
  apply binaryWordP10_normalize_weighted_orbit_sum K N 7 (by norm_num)
    binaryWordP10GapOrbitReps7
  exact binaryWordP10WordTraceOrbitSum7 K N


/-- The p=10 eight-letter-selected word stratum, normalized by its
eight marked positions. Its period-four gap class has coefficient five. -/
theorem binaryWordP10WordTraceOrbitAverage8
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 10 8,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP10GapOrbitReps8,
      ((10 : ℂ) / (8 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) *
        cyclicGapTrace K N rep := by
  apply binaryWordP10_normalize_weighted_orbit_sum K N 8 (by norm_num)
    binaryWordP10GapOrbitReps8
  exact binaryWordP10WordTraceOrbitSum8 K N


/-- Normalize the exact-count p=10 nine-N word stratum by its
nine marked positions. Its single gap orbit has size nine, hence the
normalized coefficient remains ten. -/
theorem binaryWordP10WordTraceOrbitAverage9
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 10 9,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP10GapOrbitReps9,
      ((10 : ℂ) / (9 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) *
        cyclicGapTrace K N rep := by
  apply binaryWordP10_normalize_weighted_orbit_sum K N 9 (by norm_num)
    binaryWordP10GapOrbitReps9
  exact binaryWordP10WordTraceOrbitSum9 K N

/-- The p=10 ten-letter-selected stratum consists of one word and one
period-one gap orbit; its normalized coefficient is one. -/
theorem binaryWordP10WordTraceOrbitAverage10
    {n : Type*} [Fintype n] [DecidableEq n]
    (K N : Matrix n n ℂ) :
    (∑ w : binaryWordFinStratum 10 10,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
    ∑ rep ∈ binaryWordP10GapOrbitReps10,
      ((10 : ℂ) / (10 : ℂ)) *
        ((cyclicGapOrbit rep).card : ℂ) *
        cyclicGapTrace K N rep := by
  apply binaryWordP10_normalize_weighted_orbit_sum K N 10 (by norm_num)
    binaryWordP10GapOrbitReps10
  exact binaryWordP10WordTraceOrbitSum10 K N
/-! ### Reindex exact-count word lists by finite binary-word strata -/

/-- A word in the recursive exact-count enumeration has its declared
length and true-letter count. -/
theorem binaryWordExpansionByCount_mem_sound
    (p r : ℕ) {word : List Bool}
    (hword : word ∈ binaryWordExpansionByCount p r) :
    word.length = p ∧ (word.filter id).length = r := by
  induction p generalizing r word with
  | zero =>
      cases r with
      | zero =>
          simp only [binaryWordExpansionByCount, List.mem_singleton] at hword
          subst word
          simp
      | succ r =>
          simp [binaryWordExpansionByCount] at hword
  | succ p ih =>
      cases r with
      | zero =>
          simp only [binaryWordExpansionByCount, List.mem_map] at hword
          rcases hword with ⟨word, hmem, rfl⟩
          rcases ih 0 hmem with ⟨hlen, hcount⟩
          simp [hlen, hcount]
      | succ r =>
          simp only [binaryWordExpansionByCount, List.mem_append,
            List.mem_map] at hword
          rcases hword with ⟨word, hmem, rfl⟩ | ⟨word, hmem, rfl⟩
          · rcases ih (r + 1) hmem with ⟨hlen, hcount⟩
            simp [hlen, hcount]
          · rcases ih r hmem with ⟨hlen, hcount⟩
            simp [hlen, hcount]

/-- Every finite binary word of weight r occurs in the recursive list.
The decomposition uses List.ofFn_succ', which removes the final
coordinate and therefore agrees with the list's append-at-the-end
recurrence. -/
theorem binaryWordExpansionByCount_mem_complete
    (p r : ℕ) (word : Fin p → Bool)
    (hcount : ((List.ofFn word).filter id).length = r) :
    List.ofFn word ∈ binaryWordExpansionByCount p r := by
  induction p generalizing r with
  | zero =>
      cases r with
      | zero =>
          simpa [binaryWordExpansionByCount]
      | succ r =>
          simp at hcount
  | succ p ih =>
      let prefix : Fin p → Bool := fun i => word i.castSucc
      have hdecomp :
          List.ofFn word = List.ofFn prefix ++ [word (Fin.last p)] := by
        rw [List.ofFn_succ']
        simp [prefix, List.concat_eq_append]
      have hsplit :
          ((List.ofFn prefix).filter id).length +
            (if word (Fin.last p) then 1 else 0) = r := by
        rw [hdecomp, List.filter_append] at hcount
        simpa using hcount
      cases hbit : word (Fin.last p) with
      | false =>
          have hprefix :
              ((List.ofFn prefix).filter id).length = r := by
            simpa [hbit] using hsplit
          have hmem := ih r prefix hprefix
          have hword :
              List.ofFn word = List.ofFn prefix ++ [false] := by
            rw [hdecomp, hbit]
          rw [hword]
          cases r with
          | zero =>
              simp only [binaryWordExpansionByCount, List.mem_map]
              exact ⟨List.ofFn prefix, hmem, by simp⟩
          | succ r =>
              simp only [binaryWordExpansionByCount, List.mem_append,
                List.mem_map]
              exact Or.inl ⟨List.ofFn prefix, hmem, by simp⟩
      | true =>
          cases r with
          | zero =>
              have hfalse : ((List.ofFn prefix).filter id).length + 1 = 0 := by
                simpa [hbit] using hsplit
              omega
          | succ r =>
              have hprefix :
                  ((List.ofFn prefix).filter id).length = r := by
                have h := hsplit
                simp [hbit] at h
                omega
              have hmem := ih r prefix hprefix
              have hword :
                  List.ofFn word = List.ofFn prefix ++ [true] := by
                rw [hdecomp, hbit]
              rw [hword]
              simp only [binaryWordExpansionByCount, List.mem_append,
                List.mem_map]
              exact Or.inr ⟨List.ofFn prefix, hmem, by simp⟩

/-- The recursive exact-count list has no repeated words. The two
recurrence branches are disjoint because their last letters differ. -/
theorem binaryWordExpansionByCount_nodup
    (p r : ℕ) : (binaryWordExpansionByCount p r).Nodup := by
  induction p generalizing r with
  | zero =>
      cases r <;> simp [binaryWordExpansionByCount]
  | succ p ih =>
      cases r with
      | zero =>
          simpa [binaryWordExpansionByCount] using
            (ih 0).map (List.append_left_injective [false])
      | succ r =>
          change List.Nodup
            (((binaryWordExpansionByCount p (r + 1)).map
                (fun word => word ++ [false])) ++
              ((binaryWordExpansionByCount p r).map
                (fun word => word ++ [true])))
          apply List.Nodup.append
          · exact (ih (r + 1)).map
              (List.append_left_injective [false])
          · exact (ih r).map
              (List.append_left_injective [true])
          · rw [List.disjoint_iff_ne]
            intro x hx y hy hxy
            simp only [List.mem_map] at hx hy
            rcases hx with ⟨a, ha, hax⟩
            rcases hy with ⟨b, hb, hby⟩
            rw [← hax, ← hby] at hxy
            have hlast := congrArg List.getLast? hxy
            simp at hlast

private def binaryWordListToFin
    (p : ℕ) (word : List Bool) (hlen : word.length = p) :
    Fin p → Bool :=
  fun i => word.get (Fin.cast hlen.symm i)

private theorem binaryWordListToFin_reconstruct
    (p : ℕ) (word : List Bool) (hlen : word.length = p) :
    List.ofFn (binaryWordListToFin p word hlen) = word := by
  change
    List.ofFn (fun i : Fin p => word.get (Fin.cast hlen.symm i)) = word
  calc
    List.ofFn
        (fun i : Fin p => word.get (Fin.cast hlen.symm i)) =
        List.ofFn word.get :=
      (List.ofFn_congr hlen word.get).symm
    _ = word := List.ofFn_get word

/-- Convert a recursive list word into its finite exact-weight word.
Length and weight are explicit arguments so the inverse laws below
do not depend on reducing a proof-producing pattern match. -/
private noncomputable def binaryWordFinStratumOfList
    (p r : ℕ) (word : List Bool)
    (hlen : word.length = p) (hcount : (word.filter id).length = r) :
    binaryWordFinStratum p r := by
  let f := binaryWordListToFin p word hlen
  have hrepr := binaryWordListToFin_reconstruct p word hlen
  have hrp : r ≤ p := by
    have hlenCount := List.length_eq_length_filter_add (l := word) id
    rw [hcount, hlen] at hlenCount
    omega
  exact ⟨f, hrp, by rw [hrepr]; exact hcount⟩

private theorem binaryWordFinStratumOfList_reconstruct
    (p r : ℕ) (word : List Bool)
    (hlen : word.length = p) (hcount : (word.filter id).length = r) :
    List.ofFn (binaryWordFinStratumOfList p r word hlen hcount).val = word := by
  change List.ofFn (binaryWordListToFin p word hlen) = word
  exact binaryWordListToFin_reconstruct p word hlen

/-- The finite exact-weight subtype is equivalent to the recursively
enumerated list viewed as a subtype of its toFinset. -/
private noncomputable def binaryWordFinStratumListEquiv
    (p r : ℕ) :
    binaryWordFinStratum p r ≃
      {word : List Bool // word ∈
        (binaryWordExpansionByCount p r).toFinset} :=
  Equiv.ofBijective
    (fun w : binaryWordFinStratum p r =>
      ⟨List.ofFn w.val,
        List.mem_toFinset.mpr
          (binaryWordExpansionByCount_mem_complete p r w.val w.property.2)⟩)
    (by
      constructor
      · intro a b hab
        apply Subtype.ext
        apply List.ofFn_injective
        exact congrArg Subtype.val hab
      · intro word
        rcases binaryWordExpansionByCount_mem_sound p r
          (List.mem_toFinset.mp word.property) with ⟨hlen, hcount⟩
        refine ⟨binaryWordFinStratumOfList p r word.val hlen hcount, ?_⟩
        apply Subtype.ext
        exact binaryWordFinStratumOfList_reconstruct p r word.val hlen hcount)

/-- The trace sum over the recursive matrix-word list is the same as
the finite sum over binaryWordFinStratum. This reindexing preserves
each ordered word exactly and introduces no cyclic identification. -/
theorem trace_orderedWordExpansionByCount_eq_binaryWordFinStratum
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (p r : ℕ) :
    ((orderedWordExpansionByCount A B p r).map Matrix.trace).sum =
      ∑ word : binaryWordFinStratum p r,
        Matrix.trace (binaryWordMatrix A B (List.ofFn word.val)) := by
  classical
  rw [trace_orderedWordExpansionByCount_eq_binaryWordExpansionByCount]
  let f := fun word : List Bool =>
    Matrix.trace (binaryWordMatrix A B word)
  calc
    ((binaryWordExpansionByCount p r).map f).sum =
        ∑ word ∈ (binaryWordExpansionByCount p r).toFinset, f word :=
      (List.sum_toFinset _ (binaryWordExpansionByCount_nodup p r)).symm
    _ = ∑ word :
          {word : List Bool // word ∈
            (binaryWordExpansionByCount p r).toFinset}, f word.val := by
      rw [← Finset.sum_coe_sort]
    _ = ∑ word : binaryWordFinStratum p r, f (List.ofFn word.val) := by
      symm
      exact Fintype.sum_equiv (binaryWordFinStratumListEquiv p r)
        (fun word => f (List.ofFn word.val))
        (fun word => f word.val)
        (by intro word; rfl)

/-- Full finite-stratum reconstruction of the noncommutative trace power.
This is the existing exact-count list expansion reindexed by the finite
binary-word types; no new coefficients or matrix identities are added. -/
theorem trace_orderedWordExpansionByCount_sum_eq_binaryWordFinStratum
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (p : ℕ) :
    Matrix.trace ((A + B) ^ p) =
      ∑ r ∈ Finset.range (p + 1),
        ∑ word : binaryWordFinStratum p r,
          Matrix.trace (binaryWordMatrix A B (List.ofFn word.val)) := by
  rw [trace_orderedWordExpansionByCount_sum_eq]
  apply Finset.sum_congr rfl
  intro r hr
  exact trace_orderedWordExpansionByCount_eq_binaryWordFinStratum A B p r


end EvgenyTheorem
