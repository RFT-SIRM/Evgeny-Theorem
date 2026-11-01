import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
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

end EvgenyTheorem


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


namespace EvgenyTheorem

open Matrix

/-- Exact cyclic-orbit grouping of the degree-ten ordered trace expansion.
Every one of the 1024 ordered K/B words is retained. The 108 representatives
are the canonical cyclic gap necklaces; each coefficient is the exact size
of its orbit, including all periodic classes. -/
theorem trace_orderedWordExpansion_ten_cyclic
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    ((orderedWordExpansion A B 10).map Matrix.trace).sum =
      1 * Matrix.trace (A * A * A * A * A * A * A * A * A * A)
      +       10 * Matrix.trace (A * A * A * A * A * A * A * A * A * B)
      +       5 * Matrix.trace (A * A * A * A * B * A * A * A * A * B)
      +       10 * Matrix.trace (A * A * A * B * A * A * A * A * A * B)
      +       10 * Matrix.trace (A * A * B * A * A * A * A * A * A * B)
      +       10 * Matrix.trace (A * A * B * A * A * B * A * A * A * B)
      +       10 * Matrix.trace (A * B * A * A * A * A * A * A * A * B)
      +       10 * Matrix.trace (A * B * A * A * A * A * B * A * A * B)
      +       10 * Matrix.trace (A * B * A * A * A * B * A * A * A * B)
      +       10 * Matrix.trace (A * B * A * A * B * A * A * A * A * B)
      +       5 * Matrix.trace (A * B * A * A * B * A * B * A * A * B)
      +       10 * Matrix.trace (A * B * A * B * A * A * A * A * A * B)
      +       10 * Matrix.trace (A * B * A * B * A * A * B * A * A * B)
      +       10 * Matrix.trace (A * B * A * B * A * B * A * A * A * B)
      +       2 * Matrix.trace (A * B * A * B * A * B * A * B * A * B)
      +       10 * Matrix.trace (B * A * A * A * A * A * A * A * A * B)
      +       10 * Matrix.trace (B * A * A * A * A * A * A * B * A * B)
      +       10 * Matrix.trace (B * A * A * A * A * A * B * A * A * B)
      +       10 * Matrix.trace (B * A * A * A * A * B * A * A * A * B)
      +       10 * Matrix.trace (B * A * A * A * A * B * A * B * A * B)
      +       10 * Matrix.trace (B * A * A * A * B * A * A * A * A * B)
      +       10 * Matrix.trace (B * A * A * A * B * A * A * B * A * B)
      +       10 * Matrix.trace (B * A * A * A * B * A * B * A * A * B)
      +       5 * Matrix.trace (B * A * A * A * B * B * A * A * A * B)
      +       10 * Matrix.trace (B * A * A * B * A * A * A * A * A * B)
      +       10 * Matrix.trace (B * A * A * B * A * A * A * B * A * B)
      +       10 * Matrix.trace (B * A * A * B * A * A * B * A * A * B)
      +       10 * Matrix.trace (B * A * A * B * A * B * A * A * A * B)
      +       10 * Matrix.trace (B * A * A * B * A * B * A * B * A * B)
      +       10 * Matrix.trace (B * A * A * B * B * A * A * A * A * B)
      +       10 * Matrix.trace (B * A * A * B * B * A * A * B * A * B)
      +       10 * Matrix.trace (B * A * B * A * A * A * A * A * A * B)
      +       10 * Matrix.trace (B * A * B * A * A * A * A * B * A * B)
      +       10 * Matrix.trace (B * A * B * A * A * A * B * A * A * B)
      +       10 * Matrix.trace (B * A * B * A * A * B * A * A * A * B)
      +       10 * Matrix.trace (B * A * B * A * A * B * A * B * A * B)
      +       10 * Matrix.trace (B * A * B * A * A * B * B * A * A * B)
      +       10 * Matrix.trace (B * A * B * A * B * A * A * A * A * B)
      +       10 * Matrix.trace (B * A * B * A * B * A * A * B * A * B)
      +       10 * Matrix.trace (B * A * B * A * B * A * B * A * A * B)
      +       10 * Matrix.trace (B * A * B * A * B * B * A * A * A * B)
      +       5 * Matrix.trace (B * A * B * A * B * B * A * B * A * B)
      +       10 * Matrix.trace (B * A * B * B * A * A * A * A * A * B)
      +       10 * Matrix.trace (B * A * B * B * A * A * A * B * A * B)
      +       10 * Matrix.trace (B * A * B * B * A * A * B * A * A * B)
      +       10 * Matrix.trace (B * A * B * B * A * B * A * A * A * B)
      +       10 * Matrix.trace (B * A * B * B * A * B * A * B * A * B)
      +       10 * Matrix.trace (B * A * B * B * A * B * B * A * A * B)
      +       10 * Matrix.trace (B * B * A * A * A * A * A * A * A * B)
      +       10 * Matrix.trace (B * B * A * A * A * A * A * B * A * B)
      +       10 * Matrix.trace (B * B * A * A * A * A * B * A * A * B)
      +       10 * Matrix.trace (B * B * A * A * A * A * B * B * A * B)
      +       10 * Matrix.trace (B * B * A * A * A * B * A * A * A * B)
      +       10 * Matrix.trace (B * B * A * A * A * B * A * B * A * B)
      +       10 * Matrix.trace (B * B * A * A * A * B * B * A * A * B)
      +       10 * Matrix.trace (B * B * A * A * B * A * A * A * A * B)
      +       10 * Matrix.trace (B * B * A * A * B * A * A * B * A * B)
      +       10 * Matrix.trace (B * B * A * A * B * A * B * A * A * B)
      +       10 * Matrix.trace (B * B * A * A * B * A * B * B * A * B)
      +       10 * Matrix.trace (B * B * A * A * B * B * A * A * A * B)
      +       10 * Matrix.trace (B * B * A * A * B * B * A * B * A * B)
      +       5 * Matrix.trace (B * B * A * A * B * B * B * A * A * B)
      +       10 * Matrix.trace (B * B * A * B * A * A * A * A * A * B)
      +       10 * Matrix.trace (B * B * A * B * A * A * A * B * A * B)
      +       10 * Matrix.trace (B * B * A * B * A * A * B * A * A * B)
      +       10 * Matrix.trace (B * B * A * B * A * A * B * B * A * B)
      +       10 * Matrix.trace (B * B * A * B * A * B * A * A * A * B)
      +       10 * Matrix.trace (B * B * A * B * A * B * A * B * A * B)
      +       10 * Matrix.trace (B * B * A * B * A * B * B * A * A * B)
      +       10 * Matrix.trace (B * B * A * B * B * A * A * A * A * B)
      +       10 * Matrix.trace (B * B * A * B * B * A * A * B * A * B)
      +       10 * Matrix.trace (B * B * A * B * B * A * B * A * A * B)
      +       10 * Matrix.trace (B * B * A * B * B * A * B * B * A * B)
      +       10 * Matrix.trace (B * B * A * B * B * B * A * A * A * B)
      +       10 * Matrix.trace (B * B * A * B * B * B * A * B * A * B)
      +       10 * Matrix.trace (B * B * B * A * A * A * A * A * A * B)
      +       10 * Matrix.trace (B * B * B * A * A * A * A * B * A * B)
      +       10 * Matrix.trace (B * B * B * A * A * A * B * A * A * B)
      +       10 * Matrix.trace (B * B * B * A * A * A * B * B * A * B)
      +       10 * Matrix.trace (B * B * B * A * A * B * A * A * A * B)
      +       10 * Matrix.trace (B * B * B * A * A * B * A * B * A * B)
      +       10 * Matrix.trace (B * B * B * A * A * B * B * A * A * B)
      +       10 * Matrix.trace (B * B * B * A * A * B * B * B * A * B)
      +       10 * Matrix.trace (B * B * B * A * B * A * A * A * A * B)
      +       10 * Matrix.trace (B * B * B * A * B * A * A * B * A * B)
      +       10 * Matrix.trace (B * B * B * A * B * A * B * A * A * B)
      +       10 * Matrix.trace (B * B * B * A * B * A * B * B * A * B)
      +       10 * Matrix.trace (B * B * B * A * B * B * A * A * A * B)
      +       10 * Matrix.trace (B * B * B * A * B * B * A * B * A * B)
      +       10 * Matrix.trace (B * B * B * A * B * B * B * A * A * B)
      +       5 * Matrix.trace (B * B * B * A * B * B * B * B * A * B)
      +       10 * Matrix.trace (B * B * B * B * A * A * A * A * A * B)
      +       10 * Matrix.trace (B * B * B * B * A * A * A * B * A * B)
      +       10 * Matrix.trace (B * B * B * B * A * A * B * A * A * B)
      +       10 * Matrix.trace (B * B * B * B * A * A * B * B * A * B)
      +       10 * Matrix.trace (B * B * B * B * A * B * A * A * A * B)
      +       10 * Matrix.trace (B * B * B * B * A * B * A * B * A * B)
      +       10 * Matrix.trace (B * B * B * B * A * B * B * A * A * B)
      +       10 * Matrix.trace (B * B * B * B * A * B * B * B * A * B)
      +       10 * Matrix.trace (B * B * B * B * B * A * A * A * A * B)
      +       10 * Matrix.trace (B * B * B * B * B * A * A * B * A * B)
      +       10 * Matrix.trace (B * B * B * B * B * A * B * A * A * B)
      +       10 * Matrix.trace (B * B * B * B * B * A * B * B * A * B)
      +       10 * Matrix.trace (B * B * B * B * B * B * A * A * A * B)
      +       10 * Matrix.trace (B * B * B * B * B * B * A * B * A * B)
      +       10 * Matrix.trace (B * B * B * B * B * B * B * A * A * B)
      +       10 * Matrix.trace (B * B * B * B * B * B * B * B * A * B)
      +       1 * Matrix.trace (B * B * B * B * B * B * B * B * B * B) := by
  have hrot_0000000010 : Matrix.trace (A * A * A * A * A * A * A * A * B * A) =
      Matrix.trace (A * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_0000000011 : Matrix.trace (A * A * A * A * A * A * A * A * B * B) =
      Matrix.trace (B * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0000000100 : Matrix.trace (A * A * A * A * A * A * A * B * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_0000000101 : Matrix.trace (A * A * A * A * A * A * A * B * A * B) =
      Matrix.trace (A * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_0000000110 : Matrix.trace (A * A * A * A * A * A * A * B * B * A) =
      Matrix.trace (B * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0000000111 : Matrix.trace (A * A * A * A * A * A * A * B * B * B) =
      Matrix.trace (B * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0000001000 : Matrix.trace (A * A * A * A * A * A * B * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_0000001001 : Matrix.trace (A * A * A * A * A * A * B * A * A * B) =
      Matrix.trace (A * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_0000001010 : Matrix.trace (A * A * A * A * A * A * B * A * B * A) =
      Matrix.trace (A * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A] : List (Matrix n n ℂ)))

  have hrot_0000001011 : Matrix.trace (A * A * A * A * A * A * B * A * B * B) =
      Matrix.trace (B * A * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0000001100 : Matrix.trace (A * A * A * A * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_0000001101 : Matrix.trace (A * A * A * A * A * A * B * B * A * B) =
      Matrix.trace (B * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_0000001110 : Matrix.trace (A * A * A * A * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0000001111 : Matrix.trace (A * A * A * A * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0000010000 : Matrix.trace (A * A * A * A * A * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0000010001 : Matrix.trace (A * A * A * A * A * B * A * A * A * B) =
      Matrix.trace (A * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0000010010 : Matrix.trace (A * A * A * A * A * B * A * A * B * A) =
      Matrix.trace (A * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0000010011 : Matrix.trace (A * A * A * A * A * B * A * A * B * B) =
      Matrix.trace (B * A * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0000010100 : Matrix.trace (A * A * A * A * A * B * A * B * A * A) =
      Matrix.trace (A * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0000010101 : Matrix.trace (A * A * A * A * A * B * A * B * A * B) =
      Matrix.trace (A * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0000010110 : Matrix.trace (A * A * A * A * A * B * A * B * B * A) =
      Matrix.trace (B * A * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0000010111 : Matrix.trace (A * A * A * A * A * B * A * B * B * B) =
      Matrix.trace (B * B * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0000011000 : Matrix.trace (A * A * A * A * A * B * B * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0000011001 : Matrix.trace (A * A * A * A * A * B * B * A * A * B) =
      Matrix.trace (B * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0000011010 : Matrix.trace (A * A * A * A * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0000011011 : Matrix.trace (A * A * A * A * A * B * B * A * B * B) =
      Matrix.trace (B * A * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0000011100 : Matrix.trace (A * A * A * A * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0000011101 : Matrix.trace (A * A * A * A * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0000011110 : Matrix.trace (A * A * A * A * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0000011111 : Matrix.trace (A * A * A * A * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0000100000 : Matrix.trace (A * A * A * A * B * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0000100010 : Matrix.trace (A * A * A * A * B * A * A * A * B * A) =
      Matrix.trace (A * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0000100011 : Matrix.trace (A * A * A * A * B * A * A * A * B * B) =
      Matrix.trace (B * A * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0000100100 : Matrix.trace (A * A * A * A * B * A * A * B * A * A) =
      Matrix.trace (A * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0000100101 : Matrix.trace (A * A * A * A * B * A * A * B * A * B) =
      Matrix.trace (A * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_0000100110 : Matrix.trace (A * A * A * A * B * A * A * B * B * A) =
      Matrix.trace (B * A * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0000100111 : Matrix.trace (A * A * A * A * B * A * A * B * B * B) =
      Matrix.trace (B * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0000101000 : Matrix.trace (A * A * A * A * B * A * B * A * A * A) =
      Matrix.trace (A * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0000101001 : Matrix.trace (A * A * A * A * B * A * B * A * A * B) =
      Matrix.trace (A * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0000101010 : Matrix.trace (A * A * A * A * B * A * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0000101011 : Matrix.trace (A * A * A * A * B * A * B * A * B * B) =
      Matrix.trace (B * A * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0000101100 : Matrix.trace (A * A * A * A * B * A * B * B * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_0000101101 : Matrix.trace (A * A * A * A * B * A * B * B * A * B) =
      Matrix.trace (B * A * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_0000101110 : Matrix.trace (A * A * A * A * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0000101111 : Matrix.trace (A * A * A * A * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0000110000 : Matrix.trace (A * A * A * A * B * B * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0000110001 : Matrix.trace (A * A * A * A * B * B * A * A * A * B) =
      Matrix.trace (B * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0000110010 : Matrix.trace (A * A * A * A * B * B * A * A * B * A) =
      Matrix.trace (B * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0000110011 : Matrix.trace (A * A * A * A * B * B * A * A * B * B) =
      Matrix.trace (B * A * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0000110100 : Matrix.trace (A * A * A * A * B * B * A * B * A * A) =
      Matrix.trace (B * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0000110101 : Matrix.trace (A * A * A * A * B * B * A * B * A * B) =
      Matrix.trace (B * A * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0000110110 : Matrix.trace (A * A * A * A * B * B * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0000110111 : Matrix.trace (A * A * A * A * B * B * A * B * B * B) =
      Matrix.trace (B * B * A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0000111000 : Matrix.trace (A * A * A * A * B * B * B * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0000111001 : Matrix.trace (A * A * A * A * B * B * B * A * A * B) =
      Matrix.trace (B * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0000111010 : Matrix.trace (A * A * A * A * B * B * B * A * B * A) =
      Matrix.trace (B * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0000111011 : Matrix.trace (A * A * A * A * B * B * B * A * B * B) =
      Matrix.trace (B * B * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0000111100 : Matrix.trace (A * A * A * A * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0000111101 : Matrix.trace (A * A * A * A * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0000111110 : Matrix.trace (A * A * A * A * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0000111111 : Matrix.trace (A * A * A * A * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0001000000 : Matrix.trace (A * A * A * B * A * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0001000010 : Matrix.trace (A * A * A * B * A * A * A * A * B * A) =
      Matrix.trace (A * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0001000011 : Matrix.trace (A * A * A * B * A * A * A * A * B * B) =
      Matrix.trace (B * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0001000100 : Matrix.trace (A * A * A * B * A * A * A * B * A * A) =
      Matrix.trace (A * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0001000101 : Matrix.trace (A * A * A * B * A * A * A * B * A * B) =
      Matrix.trace (A * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_0001000110 : Matrix.trace (A * A * A * B * A * A * A * B * B * A) =
      Matrix.trace (B * A * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0001000111 : Matrix.trace (A * A * A * B * A * A * A * B * B * B) =
      Matrix.trace (B * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0001001000 : Matrix.trace (A * A * A * B * A * A * B * A * A * A) =
      Matrix.trace (A * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0001001001 : Matrix.trace (A * A * A * B * A * A * B * A * A * B) =
      Matrix.trace (A * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([A, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0001001010 : Matrix.trace (A * A * A * B * A * A * B * A * B * A) =
      Matrix.trace (A * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([A, B, A] : List (Matrix n n ℂ)))

  have hrot_0001001011 : Matrix.trace (A * A * A * B * A * A * B * A * B * B) =
      Matrix.trace (B * A * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0001001100 : Matrix.trace (A * A * A * B * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_0001001101 : Matrix.trace (A * A * A * B * A * A * B * B * A * B) =
      Matrix.trace (B * A * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_0001001110 : Matrix.trace (A * A * A * B * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0001001111 : Matrix.trace (A * A * A * B * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0001010000 : Matrix.trace (A * A * A * B * A * B * A * A * A * A) =
      Matrix.trace (A * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0001010001 : Matrix.trace (A * A * A * B * A * B * A * A * A * B) =
      Matrix.trace (A * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0001010010 : Matrix.trace (A * A * A * B * A * B * A * A * B * A) =
      Matrix.trace (A * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0001010011 : Matrix.trace (A * A * A * B * A * B * A * A * B * B) =
      Matrix.trace (B * A * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0001010100 : Matrix.trace (A * A * A * B * A * B * A * B * A * A) =
      Matrix.trace (A * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0001010101 : Matrix.trace (A * A * A * B * A * B * A * B * A * B) =
      Matrix.trace (A * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0001010110 : Matrix.trace (A * A * A * B * A * B * A * B * B * A) =
      Matrix.trace (B * A * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0001010111 : Matrix.trace (A * A * A * B * A * B * A * B * B * B) =
      Matrix.trace (B * B * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0001011000 : Matrix.trace (A * A * A * B * A * B * B * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0001011001 : Matrix.trace (A * A * A * B * A * B * B * A * A * B) =
      Matrix.trace (B * A * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0001011010 : Matrix.trace (A * A * A * B * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0001011011 : Matrix.trace (A * A * A * B * A * B * B * A * B * B) =
      Matrix.trace (B * A * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0001011100 : Matrix.trace (A * A * A * B * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0001011101 : Matrix.trace (A * A * A * B * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0001011110 : Matrix.trace (A * A * A * B * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0001011111 : Matrix.trace (A * A * A * B * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0001100000 : Matrix.trace (A * A * A * B * B * A * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0001100001 : Matrix.trace (A * A * A * B * B * A * A * A * A * B) =
      Matrix.trace (B * A * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0001100010 : Matrix.trace (A * A * A * B * B * A * A * A * B * A) =
      Matrix.trace (B * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0001100011 : Matrix.trace (A * A * A * B * B * A * A * A * B * B) =
      Matrix.trace (B * A * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0001100100 : Matrix.trace (A * A * A * B * B * A * A * B * A * A) =
      Matrix.trace (B * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0001100101 : Matrix.trace (A * A * A * B * B * A * A * B * A * B) =
      Matrix.trace (B * A * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0001100110 : Matrix.trace (A * A * A * B * B * A * A * B * B * A) =
      Matrix.trace (B * A * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0001100111 : Matrix.trace (A * A * A * B * B * A * A * B * B * B) =
      Matrix.trace (B * B * A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0001101000 : Matrix.trace (A * A * A * B * B * A * B * A * A * A) =
      Matrix.trace (B * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0001101001 : Matrix.trace (A * A * A * B * B * A * B * A * A * B) =
      Matrix.trace (B * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0001101010 : Matrix.trace (A * A * A * B * B * A * B * A * B * A) =
      Matrix.trace (B * A * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0001101011 : Matrix.trace (A * A * A * B * B * A * B * A * B * B) =
      Matrix.trace (B * A * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0001101100 : Matrix.trace (A * A * A * B * B * A * B * B * A * A) =
      Matrix.trace (B * A * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0001101101 : Matrix.trace (A * A * A * B * B * A * B * B * A * B) =
      Matrix.trace (B * A * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0001101110 : Matrix.trace (A * A * A * B * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0001101111 : Matrix.trace (A * A * A * B * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0001110000 : Matrix.trace (A * A * A * B * B * B * A * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0001110001 : Matrix.trace (A * A * A * B * B * B * A * A * A * B) =
      Matrix.trace (B * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0001110010 : Matrix.trace (A * A * A * B * B * B * A * A * B * A) =
      Matrix.trace (B * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0001110011 : Matrix.trace (A * A * A * B * B * B * A * A * B * B) =
      Matrix.trace (B * B * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0001110100 : Matrix.trace (A * A * A * B * B * B * A * B * A * A) =
      Matrix.trace (B * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0001110101 : Matrix.trace (A * A * A * B * B * B * A * B * A * B) =
      Matrix.trace (B * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0001110110 : Matrix.trace (A * A * A * B * B * B * A * B * B * A) =
      Matrix.trace (B * B * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0001110111 : Matrix.trace (A * A * A * B * B * B * A * B * B * B) =
      Matrix.trace (B * B * A * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0001111000 : Matrix.trace (A * A * A * B * B * B * B * A * A * A) =
      Matrix.trace (B * B * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0001111001 : Matrix.trace (A * A * A * B * B * B * B * A * A * B) =
      Matrix.trace (B * B * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0001111010 : Matrix.trace (A * A * A * B * B * B * B * A * B * A) =
      Matrix.trace (B * B * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0001111011 : Matrix.trace (A * A * A * B * B * B * B * A * B * B) =
      Matrix.trace (B * B * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0001111100 : Matrix.trace (A * A * A * B * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0001111101 : Matrix.trace (A * A * A * B * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0001111110 : Matrix.trace (A * A * A * B * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0001111111 : Matrix.trace (A * A * A * B * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0010000000 : Matrix.trace (A * A * B * A * A * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0010000010 : Matrix.trace (A * A * B * A * A * A * A * A * B * A) =
      Matrix.trace (A * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_0010000011 : Matrix.trace (A * A * B * A * A * A * A * A * B * B) =
      Matrix.trace (B * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0010000100 : Matrix.trace (A * A * B * A * A * A * A * B * A * A) =
      Matrix.trace (A * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0010000101 : Matrix.trace (A * A * B * A * A * A * A * B * A * B) =
      Matrix.trace (A * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_0010000110 : Matrix.trace (A * A * B * A * A * A * A * B * B * A) =
      Matrix.trace (B * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0010000111 : Matrix.trace (A * A * B * A * A * A * A * B * B * B) =
      Matrix.trace (B * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0010001000 : Matrix.trace (A * A * B * A * A * A * B * A * A * A) =
      Matrix.trace (A * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0010001001 : Matrix.trace (A * A * B * A * A * A * B * A * A * B) =
      Matrix.trace (A * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, B] : List (Matrix n n ℂ)))

  have hrot_0010001010 : Matrix.trace (A * A * B * A * A * A * B * A * B * A) =
      Matrix.trace (A * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A] : List (Matrix n n ℂ)))

  have hrot_0010001011 : Matrix.trace (A * A * B * A * A * A * B * A * B * B) =
      Matrix.trace (B * A * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0010001100 : Matrix.trace (A * A * B * A * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_0010001101 : Matrix.trace (A * A * B * A * A * A * B * B * A * B) =
      Matrix.trace (B * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_0010001110 : Matrix.trace (A * A * B * A * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0010001111 : Matrix.trace (A * A * B * A * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0010010000 : Matrix.trace (A * A * B * A * A * B * A * A * A * A) =
      Matrix.trace (A * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0010010010 : Matrix.trace (A * A * B * A * A * B * A * A * B * A) =
      Matrix.trace (A * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0010010011 : Matrix.trace (A * A * B * A * A * B * A * A * B * B) =
      Matrix.trace (B * A * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0010010100 : Matrix.trace (A * A * B * A * A * B * A * B * A * A) =
      Matrix.trace (A * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0010010101 : Matrix.trace (A * A * B * A * A * B * A * B * A * B) =
      Matrix.trace (A * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0010010110 : Matrix.trace (A * A * B * A * A * B * A * B * B * A) =
      Matrix.trace (B * A * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0010010111 : Matrix.trace (A * A * B * A * A * B * A * B * B * B) =
      Matrix.trace (B * B * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0010011000 : Matrix.trace (A * A * B * A * A * B * B * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0010011001 : Matrix.trace (A * A * B * A * A * B * B * A * A * B) =
      Matrix.trace (B * A * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0010011010 : Matrix.trace (A * A * B * A * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0010011011 : Matrix.trace (A * A * B * A * A * B * B * A * B * B) =
      Matrix.trace (B * A * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0010011100 : Matrix.trace (A * A * B * A * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0010011101 : Matrix.trace (A * A * B * A * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0010011110 : Matrix.trace (A * A * B * A * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0010011111 : Matrix.trace (A * A * B * A * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0010100000 : Matrix.trace (A * A * B * A * B * A * A * A * A * A) =
      Matrix.trace (A * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0010100001 : Matrix.trace (A * A * B * A * B * A * A * A * A * B) =
      Matrix.trace (A * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0010100010 : Matrix.trace (A * A * B * A * B * A * A * A * B * A) =
      Matrix.trace (A * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0010100011 : Matrix.trace (A * A * B * A * B * A * A * A * B * B) =
      Matrix.trace (B * A * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0010100100 : Matrix.trace (A * A * B * A * B * A * A * B * A * A) =
      Matrix.trace (A * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0010100101 : Matrix.trace (A * A * B * A * B * A * A * B * A * B) =
      Matrix.trace (A * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0010100110 : Matrix.trace (A * A * B * A * B * A * A * B * B * A) =
      Matrix.trace (B * A * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0010100111 : Matrix.trace (A * A * B * A * B * A * A * B * B * B) =
      Matrix.trace (B * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0010101000 : Matrix.trace (A * A * B * A * B * A * B * A * A * A) =
      Matrix.trace (A * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0010101001 : Matrix.trace (A * A * B * A * B * A * B * A * A * B) =
      Matrix.trace (A * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0010101010 : Matrix.trace (A * A * B * A * B * A * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0010101011 : Matrix.trace (A * A * B * A * B * A * B * A * B * B) =
      Matrix.trace (B * A * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0010101100 : Matrix.trace (A * A * B * A * B * A * B * B * A * A) =
      Matrix.trace (B * A * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_0010101101 : Matrix.trace (A * A * B * A * B * A * B * B * A * B) =
      Matrix.trace (B * A * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_0010101110 : Matrix.trace (A * A * B * A * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0010101111 : Matrix.trace (A * A * B * A * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0010110000 : Matrix.trace (A * A * B * A * B * B * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0010110001 : Matrix.trace (A * A * B * A * B * B * A * A * A * B) =
      Matrix.trace (B * A * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0010110010 : Matrix.trace (A * A * B * A * B * B * A * A * B * A) =
      Matrix.trace (B * A * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0010110011 : Matrix.trace (A * A * B * A * B * B * A * A * B * B) =
      Matrix.trace (B * A * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0010110100 : Matrix.trace (A * A * B * A * B * B * A * B * A * A) =
      Matrix.trace (B * A * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0010110101 : Matrix.trace (A * A * B * A * B * B * A * B * A * B) =
      Matrix.trace (B * A * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0010110110 : Matrix.trace (A * A * B * A * B * B * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0010110111 : Matrix.trace (A * A * B * A * B * B * A * B * B * B) =
      Matrix.trace (B * B * A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0010111000 : Matrix.trace (A * A * B * A * B * B * B * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0010111001 : Matrix.trace (A * A * B * A * B * B * B * A * A * B) =
      Matrix.trace (B * B * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0010111010 : Matrix.trace (A * A * B * A * B * B * B * A * B * A) =
      Matrix.trace (B * B * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0010111011 : Matrix.trace (A * A * B * A * B * B * B * A * B * B) =
      Matrix.trace (B * B * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0010111100 : Matrix.trace (A * A * B * A * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0010111101 : Matrix.trace (A * A * B * A * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0010111110 : Matrix.trace (A * A * B * A * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0010111111 : Matrix.trace (A * A * B * A * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0011000000 : Matrix.trace (A * A * B * B * A * A * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0011000001 : Matrix.trace (A * A * B * B * A * A * A * A * A * B) =
      Matrix.trace (B * A * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0011000010 : Matrix.trace (A * A * B * B * A * A * A * A * B * A) =
      Matrix.trace (B * A * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0011000011 : Matrix.trace (A * A * B * B * A * A * A * A * B * B) =
      Matrix.trace (B * A * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0011000100 : Matrix.trace (A * A * B * B * A * A * A * B * A * A) =
      Matrix.trace (B * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0011000101 : Matrix.trace (A * A * B * B * A * A * A * B * A * B) =
      Matrix.trace (B * A * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0011000110 : Matrix.trace (A * A * B * B * A * A * A * B * B * A) =
      Matrix.trace (B * A * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0011000111 : Matrix.trace (A * A * B * B * A * A * A * B * B * B) =
      Matrix.trace (B * B * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0011001000 : Matrix.trace (A * A * B * B * A * A * B * A * A * A) =
      Matrix.trace (B * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0011001001 : Matrix.trace (A * A * B * B * A * A * B * A * A * B) =
      Matrix.trace (B * A * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0011001010 : Matrix.trace (A * A * B * B * A * A * B * A * B * A) =
      Matrix.trace (B * A * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0011001011 : Matrix.trace (A * A * B * B * A * A * B * A * B * B) =
      Matrix.trace (B * A * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0011001100 : Matrix.trace (A * A * B * B * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0011001101 : Matrix.trace (A * A * B * B * A * A * B * B * A * B) =
      Matrix.trace (B * A * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_0011001110 : Matrix.trace (A * A * B * B * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0011001111 : Matrix.trace (A * A * B * B * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0011010000 : Matrix.trace (A * A * B * B * A * B * A * A * A * A) =
      Matrix.trace (B * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0011010001 : Matrix.trace (A * A * B * B * A * B * A * A * A * B) =
      Matrix.trace (B * A * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0011010010 : Matrix.trace (A * A * B * B * A * B * A * A * B * A) =
      Matrix.trace (B * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0011010011 : Matrix.trace (A * A * B * B * A * B * A * A * B * B) =
      Matrix.trace (B * A * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0011010100 : Matrix.trace (A * A * B * B * A * B * A * B * A * A) =
      Matrix.trace (B * A * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0011010101 : Matrix.trace (A * A * B * B * A * B * A * B * A * B) =
      Matrix.trace (B * A * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0011010110 : Matrix.trace (A * A * B * B * A * B * A * B * B * A) =
      Matrix.trace (B * A * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0011010111 : Matrix.trace (A * A * B * B * A * B * A * B * B * B) =
      Matrix.trace (B * B * A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0011011000 : Matrix.trace (A * A * B * B * A * B * B * A * A * A) =
      Matrix.trace (B * A * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0011011001 : Matrix.trace (A * A * B * B * A * B * B * A * A * B) =
      Matrix.trace (B * A * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0011011010 : Matrix.trace (A * A * B * B * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0011011011 : Matrix.trace (A * A * B * B * A * B * B * A * B * B) =
      Matrix.trace (B * A * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0011011100 : Matrix.trace (A * A * B * B * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0011011101 : Matrix.trace (A * A * B * B * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0011011110 : Matrix.trace (A * A * B * B * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0011011111 : Matrix.trace (A * A * B * B * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0011100000 : Matrix.trace (A * A * B * B * B * A * A * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0011100001 : Matrix.trace (A * A * B * B * B * A * A * A * A * B) =
      Matrix.trace (B * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0011100010 : Matrix.trace (A * A * B * B * B * A * A * A * B * A) =
      Matrix.trace (B * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0011100011 : Matrix.trace (A * A * B * B * B * A * A * A * B * B) =
      Matrix.trace (B * B * A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0011100100 : Matrix.trace (A * A * B * B * B * A * A * B * A * A) =
      Matrix.trace (B * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0011100101 : Matrix.trace (A * A * B * B * B * A * A * B * A * B) =
      Matrix.trace (B * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0011100110 : Matrix.trace (A * A * B * B * B * A * A * B * B * A) =
      Matrix.trace (B * B * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0011100111 : Matrix.trace (A * A * B * B * B * A * A * B * B * B) =
      Matrix.trace (B * B * A * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0011101000 : Matrix.trace (A * A * B * B * B * A * B * A * A * A) =
      Matrix.trace (B * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0011101001 : Matrix.trace (A * A * B * B * B * A * B * A * A * B) =
      Matrix.trace (B * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0011101010 : Matrix.trace (A * A * B * B * B * A * B * A * B * A) =
      Matrix.trace (B * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0011101011 : Matrix.trace (A * A * B * B * B * A * B * A * B * B) =
      Matrix.trace (B * B * A * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0011101100 : Matrix.trace (A * A * B * B * B * A * B * B * A * A) =
      Matrix.trace (B * B * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0011101101 : Matrix.trace (A * A * B * B * B * A * B * B * A * B) =
      Matrix.trace (B * B * A * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0011101110 : Matrix.trace (A * A * B * B * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0011101111 : Matrix.trace (A * A * B * B * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0011110000 : Matrix.trace (A * A * B * B * B * B * A * A * A * A) =
      Matrix.trace (B * B * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0011110001 : Matrix.trace (A * A * B * B * B * B * A * A * A * B) =
      Matrix.trace (B * B * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0011110010 : Matrix.trace (A * A * B * B * B * B * A * A * B * A) =
      Matrix.trace (B * B * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0011110011 : Matrix.trace (A * A * B * B * B * B * A * A * B * B) =
      Matrix.trace (B * B * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0011110100 : Matrix.trace (A * A * B * B * B * B * A * B * A * A) =
      Matrix.trace (B * B * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0011110101 : Matrix.trace (A * A * B * B * B * B * A * B * A * B) =
      Matrix.trace (B * B * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0011110110 : Matrix.trace (A * A * B * B * B * B * A * B * B * A) =
      Matrix.trace (B * B * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0011110111 : Matrix.trace (A * A * B * B * B * B * A * B * B * B) =
      Matrix.trace (B * B * B * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0011111000 : Matrix.trace (A * A * B * B * B * B * B * A * A * A) =
      Matrix.trace (B * B * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0011111001 : Matrix.trace (A * A * B * B * B * B * B * A * A * B) =
      Matrix.trace (B * B * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0011111010 : Matrix.trace (A * A * B * B * B * B * B * A * B * A) =
      Matrix.trace (B * B * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0011111011 : Matrix.trace (A * A * B * B * B * B * B * A * B * B) =
      Matrix.trace (B * B * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0011111100 : Matrix.trace (A * A * B * B * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0011111101 : Matrix.trace (A * A * B * B * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0011111110 : Matrix.trace (A * A * B * B * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0011111111 : Matrix.trace (A * A * B * B * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0100000000 : Matrix.trace (A * B * A * A * A * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0100000010 : Matrix.trace (A * B * A * A * A * A * A * A * B * A) =
      Matrix.trace (A * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_0100000011 : Matrix.trace (A * B * A * A * A * A * A * A * B * B) =
      Matrix.trace (B * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0100000100 : Matrix.trace (A * B * A * A * A * A * A * B * A * A) =
      Matrix.trace (A * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_0100000101 : Matrix.trace (A * B * A * A * A * A * A * B * A * B) =
      Matrix.trace (A * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_0100000110 : Matrix.trace (A * B * A * A * A * A * A * B * B * A) =
      Matrix.trace (B * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0100000111 : Matrix.trace (A * B * A * A * A * A * A * B * B * B) =
      Matrix.trace (B * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0100001000 : Matrix.trace (A * B * A * A * A * A * B * A * A * A) =
      Matrix.trace (A * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0100001010 : Matrix.trace (A * B * A * A * A * A * B * A * B * A) =
      Matrix.trace (A * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A] : List (Matrix n n ℂ)))

  have hrot_0100001011 : Matrix.trace (A * B * A * A * A * A * B * A * B * B) =
      Matrix.trace (B * A * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0100001100 : Matrix.trace (A * B * A * A * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_0100001101 : Matrix.trace (A * B * A * A * A * A * B * B * A * B) =
      Matrix.trace (B * A * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_0100001110 : Matrix.trace (A * B * A * A * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0100001111 : Matrix.trace (A * B * A * A * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0100010000 : Matrix.trace (A * B * A * A * A * B * A * A * A * A) =
      Matrix.trace (A * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0100010010 : Matrix.trace (A * B * A * A * A * B * A * A * B * A) =
      Matrix.trace (A * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0100010011 : Matrix.trace (A * B * A * A * A * B * A * A * B * B) =
      Matrix.trace (B * A * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0100010100 : Matrix.trace (A * B * A * A * A * B * A * B * A * A) =
      Matrix.trace (A * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0100010101 : Matrix.trace (A * B * A * A * A * B * A * B * A * B) =
      Matrix.trace (A * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0100010110 : Matrix.trace (A * B * A * A * A * B * A * B * B * A) =
      Matrix.trace (B * A * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0100010111 : Matrix.trace (A * B * A * A * A * B * A * B * B * B) =
      Matrix.trace (B * B * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0100011000 : Matrix.trace (A * B * A * A * A * B * B * A * A * A) =
      Matrix.trace (B * A * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0100011001 : Matrix.trace (A * B * A * A * A * B * B * A * A * B) =
      Matrix.trace (B * A * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0100011010 : Matrix.trace (A * B * A * A * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0100011011 : Matrix.trace (A * B * A * A * A * B * B * A * B * B) =
      Matrix.trace (B * A * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0100011100 : Matrix.trace (A * B * A * A * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0100011101 : Matrix.trace (A * B * A * A * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0100011110 : Matrix.trace (A * B * A * A * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0100011111 : Matrix.trace (A * B * A * A * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0100100000 : Matrix.trace (A * B * A * A * B * A * A * A * A * A) =
      Matrix.trace (A * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0100100010 : Matrix.trace (A * B * A * A * B * A * A * A * B * A) =
      Matrix.trace (A * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_0100100011 : Matrix.trace (A * B * A * A * B * A * A * A * B * B) =
      Matrix.trace (B * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0100100100 : Matrix.trace (A * B * A * A * B * A * A * B * A * A) =
      Matrix.trace (A * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, A, B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0100100101 : Matrix.trace (A * B * A * A * B * A * A * B * A * B) =
      Matrix.trace (A * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_0100100110 : Matrix.trace (A * B * A * A * B * A * A * B * B * A) =
      Matrix.trace (B * A * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0100100111 : Matrix.trace (A * B * A * A * B * A * A * B * B * B) =
      Matrix.trace (B * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0100101000 : Matrix.trace (A * B * A * A * B * A * B * A * A * A) =
      Matrix.trace (A * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0100101010 : Matrix.trace (A * B * A * A * B * A * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0100101011 : Matrix.trace (A * B * A * A * B * A * B * A * B * B) =
      Matrix.trace (B * A * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0100101100 : Matrix.trace (A * B * A * A * B * A * B * B * A * A) =
      Matrix.trace (B * A * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_0100101101 : Matrix.trace (A * B * A * A * B * A * B * B * A * B) =
      Matrix.trace (B * A * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_0100101110 : Matrix.trace (A * B * A * A * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0100101111 : Matrix.trace (A * B * A * A * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0100110000 : Matrix.trace (A * B * A * A * B * B * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0100110001 : Matrix.trace (A * B * A * A * B * B * A * A * A * B) =
      Matrix.trace (B * A * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0100110010 : Matrix.trace (A * B * A * A * B * B * A * A * B * A) =
      Matrix.trace (B * A * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0100110011 : Matrix.trace (A * B * A * A * B * B * A * A * B * B) =
      Matrix.trace (B * A * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0100110100 : Matrix.trace (A * B * A * A * B * B * A * B * A * A) =
      Matrix.trace (B * A * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0100110101 : Matrix.trace (A * B * A * A * B * B * A * B * A * B) =
      Matrix.trace (B * A * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0100110110 : Matrix.trace (A * B * A * A * B * B * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0100110111 : Matrix.trace (A * B * A * A * B * B * A * B * B * B) =
      Matrix.trace (B * B * A * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0100111000 : Matrix.trace (A * B * A * A * B * B * B * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0100111001 : Matrix.trace (A * B * A * A * B * B * B * A * A * B) =
      Matrix.trace (B * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0100111010 : Matrix.trace (A * B * A * A * B * B * B * A * B * A) =
      Matrix.trace (B * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0100111011 : Matrix.trace (A * B * A * A * B * B * B * A * B * B) =
      Matrix.trace (B * B * A * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0100111100 : Matrix.trace (A * B * A * A * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0100111101 : Matrix.trace (A * B * A * A * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0100111110 : Matrix.trace (A * B * A * A * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0100111111 : Matrix.trace (A * B * A * A * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0101000000 : Matrix.trace (A * B * A * B * A * A * A * A * A * A) =
      Matrix.trace (A * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0101000010 : Matrix.trace (A * B * A * B * A * A * A * A * B * A) =
      Matrix.trace (A * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0101000011 : Matrix.trace (A * B * A * B * A * A * A * A * B * B) =
      Matrix.trace (B * A * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0101000100 : Matrix.trace (A * B * A * B * A * A * A * B * A * A) =
      Matrix.trace (A * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0101000101 : Matrix.trace (A * B * A * B * A * A * A * B * A * B) =
      Matrix.trace (A * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A, B] : List (Matrix n n ℂ)))

  have hrot_0101000110 : Matrix.trace (A * B * A * B * A * A * A * B * B * A) =
      Matrix.trace (B * A * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0101000111 : Matrix.trace (A * B * A * B * A * A * A * B * B * B) =
      Matrix.trace (B * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0101001000 : Matrix.trace (A * B * A * B * A * A * B * A * A * A) =
      Matrix.trace (A * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, B, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0101001010 : Matrix.trace (A * B * A * B * A * A * B * A * B * A) =
      Matrix.trace (A * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, B, A, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0101001011 : Matrix.trace (A * B * A * B * A * A * B * A * B * B) =
      Matrix.trace (B * A * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0101001100 : Matrix.trace (A * B * A * B * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_0101001101 : Matrix.trace (A * B * A * B * A * A * B * B * A * B) =
      Matrix.trace (B * A * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_0101001110 : Matrix.trace (A * B * A * B * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0101001111 : Matrix.trace (A * B * A * B * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0101010000 : Matrix.trace (A * B * A * B * A * B * A * A * A * A) =
      Matrix.trace (A * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0101010010 : Matrix.trace (A * B * A * B * A * B * A * A * B * A) =
      Matrix.trace (A * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0101010011 : Matrix.trace (A * B * A * B * A * B * A * A * B * B) =
      Matrix.trace (B * A * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0101010100 : Matrix.trace (A * B * A * B * A * B * A * B * A * A) =
      Matrix.trace (A * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0101010110 : Matrix.trace (A * B * A * B * A * B * A * B * B * A) =
      Matrix.trace (B * A * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0101010111 : Matrix.trace (A * B * A * B * A * B * A * B * B * B) =
      Matrix.trace (B * B * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0101011000 : Matrix.trace (A * B * A * B * A * B * B * A * A * A) =
      Matrix.trace (B * A * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0101011001 : Matrix.trace (A * B * A * B * A * B * B * A * A * B) =
      Matrix.trace (B * A * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0101011010 : Matrix.trace (A * B * A * B * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0101011011 : Matrix.trace (A * B * A * B * A * B * B * A * B * B) =
      Matrix.trace (B * A * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0101011100 : Matrix.trace (A * B * A * B * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0101011101 : Matrix.trace (A * B * A * B * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0101011110 : Matrix.trace (A * B * A * B * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0101011111 : Matrix.trace (A * B * A * B * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0101100000 : Matrix.trace (A * B * A * B * B * A * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0101100001 : Matrix.trace (A * B * A * B * B * A * A * A * A * B) =
      Matrix.trace (B * A * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0101100010 : Matrix.trace (A * B * A * B * B * A * A * A * B * A) =
      Matrix.trace (B * A * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0101100011 : Matrix.trace (A * B * A * B * B * A * A * A * B * B) =
      Matrix.trace (B * A * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0101100100 : Matrix.trace (A * B * A * B * B * A * A * B * A * A) =
      Matrix.trace (B * A * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0101100101 : Matrix.trace (A * B * A * B * B * A * A * B * A * B) =
      Matrix.trace (B * A * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0101100110 : Matrix.trace (A * B * A * B * B * A * A * B * B * A) =
      Matrix.trace (B * A * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0101100111 : Matrix.trace (A * B * A * B * B * A * A * B * B * B) =
      Matrix.trace (B * B * A * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0101101000 : Matrix.trace (A * B * A * B * B * A * B * A * A * A) =
      Matrix.trace (B * A * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0101101001 : Matrix.trace (A * B * A * B * B * A * B * A * A * B) =
      Matrix.trace (B * A * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0101101010 : Matrix.trace (A * B * A * B * B * A * B * A * B * A) =
      Matrix.trace (B * A * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0101101011 : Matrix.trace (A * B * A * B * B * A * B * A * B * B) =
      Matrix.trace (B * A * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0101101100 : Matrix.trace (A * B * A * B * B * A * B * B * A * A) =
      Matrix.trace (B * A * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0101101101 : Matrix.trace (A * B * A * B * B * A * B * B * A * B) =
      Matrix.trace (B * A * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0101101110 : Matrix.trace (A * B * A * B * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0101101111 : Matrix.trace (A * B * A * B * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0101110000 : Matrix.trace (A * B * A * B * B * B * A * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0101110001 : Matrix.trace (A * B * A * B * B * B * A * A * A * B) =
      Matrix.trace (B * B * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0101110010 : Matrix.trace (A * B * A * B * B * B * A * A * B * A) =
      Matrix.trace (B * B * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0101110011 : Matrix.trace (A * B * A * B * B * B * A * A * B * B) =
      Matrix.trace (B * B * A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0101110100 : Matrix.trace (A * B * A * B * B * B * A * B * A * A) =
      Matrix.trace (B * B * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0101110101 : Matrix.trace (A * B * A * B * B * B * A * B * A * B) =
      Matrix.trace (B * B * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0101110110 : Matrix.trace (A * B * A * B * B * B * A * B * B * A) =
      Matrix.trace (B * B * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0101110111 : Matrix.trace (A * B * A * B * B * B * A * B * B * B) =
      Matrix.trace (B * B * A * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0101111000 : Matrix.trace (A * B * A * B * B * B * B * A * A * A) =
      Matrix.trace (B * B * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0101111001 : Matrix.trace (A * B * A * B * B * B * B * A * A * B) =
      Matrix.trace (B * B * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0101111010 : Matrix.trace (A * B * A * B * B * B * B * A * B * A) =
      Matrix.trace (B * B * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0101111011 : Matrix.trace (A * B * A * B * B * B * B * A * B * B) =
      Matrix.trace (B * B * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0101111100 : Matrix.trace (A * B * A * B * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0101111101 : Matrix.trace (A * B * A * B * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0101111110 : Matrix.trace (A * B * A * B * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0101111111 : Matrix.trace (A * B * A * B * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0110000000 : Matrix.trace (A * B * B * A * A * A * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0110000001 : Matrix.trace (A * B * B * A * A * A * A * A * A * B) =
      Matrix.trace (B * A * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0110000010 : Matrix.trace (A * B * B * A * A * A * A * A * B * A) =
      Matrix.trace (B * A * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0110000011 : Matrix.trace (A * B * B * A * A * A * A * A * B * B) =
      Matrix.trace (B * A * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0110000100 : Matrix.trace (A * B * B * A * A * A * A * B * A * A) =
      Matrix.trace (B * A * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0110000101 : Matrix.trace (A * B * B * A * A * A * A * B * A * B) =
      Matrix.trace (B * A * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0110000110 : Matrix.trace (A * B * B * A * A * A * A * B * B * A) =
      Matrix.trace (B * A * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0110000111 : Matrix.trace (A * B * B * A * A * A * A * B * B * B) =
      Matrix.trace (B * B * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0110001000 : Matrix.trace (A * B * B * A * A * A * B * A * A * A) =
      Matrix.trace (B * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0110001001 : Matrix.trace (A * B * B * A * A * A * B * A * A * B) =
      Matrix.trace (B * A * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0110001010 : Matrix.trace (A * B * B * A * A * A * B * A * B * A) =
      Matrix.trace (B * A * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0110001011 : Matrix.trace (A * B * B * A * A * A * B * A * B * B) =
      Matrix.trace (B * A * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0110001100 : Matrix.trace (A * B * B * A * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0110001101 : Matrix.trace (A * B * B * A * A * A * B * B * A * B) =
      Matrix.trace (B * A * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_0110001110 : Matrix.trace (A * B * B * A * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0110001111 : Matrix.trace (A * B * B * A * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0110010000 : Matrix.trace (A * B * B * A * A * B * A * A * A * A) =
      Matrix.trace (B * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0110010001 : Matrix.trace (A * B * B * A * A * B * A * A * A * B) =
      Matrix.trace (B * A * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0110010010 : Matrix.trace (A * B * B * A * A * B * A * A * B * A) =
      Matrix.trace (B * A * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0110010011 : Matrix.trace (A * B * B * A * A * B * A * A * B * B) =
      Matrix.trace (B * A * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0110010100 : Matrix.trace (A * B * B * A * A * B * A * B * A * A) =
      Matrix.trace (B * A * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0110010101 : Matrix.trace (A * B * B * A * A * B * A * B * A * B) =
      Matrix.trace (B * A * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0110010110 : Matrix.trace (A * B * B * A * A * B * A * B * B * A) =
      Matrix.trace (B * A * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_0110010111 : Matrix.trace (A * B * B * A * A * B * A * B * B * B) =
      Matrix.trace (B * B * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0110011000 : Matrix.trace (A * B * B * A * A * B * B * A * A * A) =
      Matrix.trace (B * A * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0110011001 : Matrix.trace (A * B * B * A * A * B * B * A * A * B) =
      Matrix.trace (B * A * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, A, B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0110011010 : Matrix.trace (A * B * B * A * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0110011011 : Matrix.trace (A * B * B * A * A * B * B * A * B * B) =
      Matrix.trace (B * A * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0110011100 : Matrix.trace (A * B * B * A * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0110011101 : Matrix.trace (A * B * B * A * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0110011110 : Matrix.trace (A * B * B * A * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0110011111 : Matrix.trace (A * B * B * A * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0110100000 : Matrix.trace (A * B * B * A * B * A * A * A * A * A) =
      Matrix.trace (B * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0110100001 : Matrix.trace (A * B * B * A * B * A * A * A * A * B) =
      Matrix.trace (B * A * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0110100010 : Matrix.trace (A * B * B * A * B * A * A * A * B * A) =
      Matrix.trace (B * A * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0110100011 : Matrix.trace (A * B * B * A * B * A * A * A * B * B) =
      Matrix.trace (B * A * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0110100100 : Matrix.trace (A * B * B * A * B * A * A * B * A * A) =
      Matrix.trace (B * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0110100101 : Matrix.trace (A * B * B * A * B * A * A * B * A * B) =
      Matrix.trace (B * A * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0110100110 : Matrix.trace (A * B * B * A * B * A * A * B * B * A) =
      Matrix.trace (B * A * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0110100111 : Matrix.trace (A * B * B * A * B * A * A * B * B * B) =
      Matrix.trace (B * B * A * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0110101000 : Matrix.trace (A * B * B * A * B * A * B * A * A * A) =
      Matrix.trace (B * A * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0110101001 : Matrix.trace (A * B * B * A * B * A * B * A * A * B) =
      Matrix.trace (B * A * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0110101010 : Matrix.trace (A * B * B * A * B * A * B * A * B * A) =
      Matrix.trace (B * A * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0110101011 : Matrix.trace (A * B * B * A * B * A * B * A * B * B) =
      Matrix.trace (B * A * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0110101100 : Matrix.trace (A * B * B * A * B * A * B * B * A * A) =
      Matrix.trace (B * A * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0110101101 : Matrix.trace (A * B * B * A * B * A * B * B * A * B) =
      Matrix.trace (B * A * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0110101110 : Matrix.trace (A * B * B * A * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_0110101111 : Matrix.trace (A * B * B * A * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0110110000 : Matrix.trace (A * B * B * A * B * B * A * A * A * A) =
      Matrix.trace (B * A * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0110110001 : Matrix.trace (A * B * B * A * B * B * A * A * A * B) =
      Matrix.trace (B * A * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0110110010 : Matrix.trace (A * B * B * A * B * B * A * A * B * A) =
      Matrix.trace (B * A * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0110110011 : Matrix.trace (A * B * B * A * B * B * A * A * B * B) =
      Matrix.trace (B * A * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_0110110100 : Matrix.trace (A * B * B * A * B * B * A * B * A * A) =
      Matrix.trace (B * A * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0110110101 : Matrix.trace (A * B * B * A * B * B * A * B * A * B) =
      Matrix.trace (B * A * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0110110110 : Matrix.trace (A * B * B * A * B * B * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0110110111 : Matrix.trace (A * B * B * A * B * B * A * B * B * B) =
      Matrix.trace (B * B * A * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0110111000 : Matrix.trace (A * B * B * A * B * B * B * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0110111001 : Matrix.trace (A * B * B * A * B * B * B * A * A * B) =
      Matrix.trace (B * B * A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0110111010 : Matrix.trace (A * B * B * A * B * B * B * A * B * A) =
      Matrix.trace (B * B * A * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0110111011 : Matrix.trace (A * B * B * A * B * B * B * A * B * B) =
      Matrix.trace (B * B * A * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0110111100 : Matrix.trace (A * B * B * A * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0110111101 : Matrix.trace (A * B * B * A * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0110111110 : Matrix.trace (A * B * B * A * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0110111111 : Matrix.trace (A * B * B * A * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0111000000 : Matrix.trace (A * B * B * B * A * A * A * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0111000001 : Matrix.trace (A * B * B * B * A * A * A * A * A * B) =
      Matrix.trace (B * B * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0111000010 : Matrix.trace (A * B * B * B * A * A * A * A * B * A) =
      Matrix.trace (B * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0111000011 : Matrix.trace (A * B * B * B * A * A * A * A * B * B) =
      Matrix.trace (B * B * A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0111000100 : Matrix.trace (A * B * B * B * A * A * A * B * A * A) =
      Matrix.trace (B * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0111000101 : Matrix.trace (A * B * B * B * A * A * A * B * A * B) =
      Matrix.trace (B * B * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0111000110 : Matrix.trace (A * B * B * B * A * A * A * B * B * A) =
      Matrix.trace (B * B * A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0111000111 : Matrix.trace (A * B * B * B * A * A * A * B * B * B) =
      Matrix.trace (B * B * A * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0111001000 : Matrix.trace (A * B * B * B * A * A * B * A * A * A) =
      Matrix.trace (B * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0111001001 : Matrix.trace (A * B * B * B * A * A * B * A * A * B) =
      Matrix.trace (B * B * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0111001010 : Matrix.trace (A * B * B * B * A * A * B * A * B * A) =
      Matrix.trace (B * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0111001011 : Matrix.trace (A * B * B * B * A * A * B * A * B * B) =
      Matrix.trace (B * B * A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0111001100 : Matrix.trace (A * B * B * B * A * A * B * B * A * A) =
      Matrix.trace (B * B * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0111001101 : Matrix.trace (A * B * B * B * A * A * B * B * A * B) =
      Matrix.trace (B * B * A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0111001110 : Matrix.trace (A * B * B * B * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0111001111 : Matrix.trace (A * B * B * B * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_0111010000 : Matrix.trace (A * B * B * B * A * B * A * A * A * A) =
      Matrix.trace (B * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0111010001 : Matrix.trace (A * B * B * B * A * B * A * A * A * B) =
      Matrix.trace (B * B * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0111010010 : Matrix.trace (A * B * B * B * A * B * A * A * B * A) =
      Matrix.trace (B * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0111010011 : Matrix.trace (A * B * B * B * A * B * A * A * B * B) =
      Matrix.trace (B * B * A * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0111010100 : Matrix.trace (A * B * B * B * A * B * A * B * A * A) =
      Matrix.trace (B * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0111010101 : Matrix.trace (A * B * B * B * A * B * A * B * A * B) =
      Matrix.trace (B * B * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0111010110 : Matrix.trace (A * B * B * B * A * B * A * B * B * A) =
      Matrix.trace (B * B * A * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0111010111 : Matrix.trace (A * B * B * B * A * B * A * B * B * B) =
      Matrix.trace (B * B * A * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_0111011000 : Matrix.trace (A * B * B * B * A * B * B * A * A * A) =
      Matrix.trace (B * B * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0111011001 : Matrix.trace (A * B * B * B * A * B * B * A * A * B) =
      Matrix.trace (B * B * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0111011010 : Matrix.trace (A * B * B * B * A * B * B * A * B * A) =
      Matrix.trace (B * B * A * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0111011011 : Matrix.trace (A * B * B * B * A * B * B * A * B * B) =
      Matrix.trace (B * B * A * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0111011100 : Matrix.trace (A * B * B * B * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0111011101 : Matrix.trace (A * B * B * B * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0111011110 : Matrix.trace (A * B * B * B * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0111011111 : Matrix.trace (A * B * B * B * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0111100000 : Matrix.trace (A * B * B * B * B * A * A * A * A * A) =
      Matrix.trace (B * B * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0111100001 : Matrix.trace (A * B * B * B * B * A * A * A * A * B) =
      Matrix.trace (B * B * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0111100010 : Matrix.trace (A * B * B * B * B * A * A * A * B * A) =
      Matrix.trace (B * B * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0111100011 : Matrix.trace (A * B * B * B * B * A * A * A * B * B) =
      Matrix.trace (B * B * B * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0111100100 : Matrix.trace (A * B * B * B * B * A * A * B * A * A) =
      Matrix.trace (B * B * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0111100101 : Matrix.trace (A * B * B * B * B * A * A * B * A * B) =
      Matrix.trace (B * B * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0111100110 : Matrix.trace (A * B * B * B * B * A * A * B * B * A) =
      Matrix.trace (B * B * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0111100111 : Matrix.trace (A * B * B * B * B * A * A * B * B * B) =
      Matrix.trace (B * B * B * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0111101000 : Matrix.trace (A * B * B * B * B * A * B * A * A * A) =
      Matrix.trace (B * B * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0111101001 : Matrix.trace (A * B * B * B * B * A * B * A * A * B) =
      Matrix.trace (B * B * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0111101010 : Matrix.trace (A * B * B * B * B * A * B * A * B * A) =
      Matrix.trace (B * B * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0111101011 : Matrix.trace (A * B * B * B * B * A * B * A * B * B) =
      Matrix.trace (B * B * B * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0111101100 : Matrix.trace (A * B * B * B * B * A * B * B * A * A) =
      Matrix.trace (B * B * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0111101101 : Matrix.trace (A * B * B * B * B * A * B * B * A * B) =
      Matrix.trace (B * B * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0111101110 : Matrix.trace (A * B * B * B * B * A * B * B * B * A) =
      Matrix.trace (B * B * B * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0111101111 : Matrix.trace (A * B * B * B * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * A * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0111110000 : Matrix.trace (A * B * B * B * B * B * A * A * A * A) =
      Matrix.trace (B * B * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0111110001 : Matrix.trace (A * B * B * B * B * B * A * A * A * B) =
      Matrix.trace (B * B * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0111110010 : Matrix.trace (A * B * B * B * B * B * A * A * B * A) =
      Matrix.trace (B * B * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0111110011 : Matrix.trace (A * B * B * B * B * B * A * A * B * B) =
      Matrix.trace (B * B * B * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0111110100 : Matrix.trace (A * B * B * B * B * B * A * B * A * A) =
      Matrix.trace (B * B * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0111110101 : Matrix.trace (A * B * B * B * B * B * A * B * A * B) =
      Matrix.trace (B * B * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0111110110 : Matrix.trace (A * B * B * B * B * B * A * B * B * A) =
      Matrix.trace (B * B * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0111110111 : Matrix.trace (A * B * B * B * B * B * A * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_0111111000 : Matrix.trace (A * B * B * B * B * B * B * A * A * A) =
      Matrix.trace (B * B * B * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_0111111001 : Matrix.trace (A * B * B * B * B * B * B * A * A * B) =
      Matrix.trace (B * B * B * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_0111111010 : Matrix.trace (A * B * B * B * B * B * B * A * B * A) =
      Matrix.trace (B * B * B * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_0111111011 : Matrix.trace (A * B * B * B * B * B * B * A * B * B) =
      Matrix.trace (B * B * B * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_0111111100 : Matrix.trace (A * B * B * B * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_0111111101 : Matrix.trace (A * B * B * B * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_0111111110 : Matrix.trace (A * B * B * B * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_0111111111 : Matrix.trace (A * B * B * B * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1000000000 : Matrix.trace (B * A * A * A * A * A * A * A * A * A) =
      Matrix.trace (A * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1000000010 : Matrix.trace (B * A * A * A * A * A * A * A * B * A) =
      Matrix.trace (A * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_1000000011 : Matrix.trace (B * A * A * A * A * A * A * A * B * B) =
      Matrix.trace (B * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1000000100 : Matrix.trace (B * A * A * A * A * A * A * B * A * A) =
      Matrix.trace (A * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_1000000110 : Matrix.trace (B * A * A * A * A * A * A * B * B * A) =
      Matrix.trace (B * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1000000111 : Matrix.trace (B * A * A * A * A * A * A * B * B * B) =
      Matrix.trace (B * B * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1000001000 : Matrix.trace (B * A * A * A * A * A * B * A * A * A) =
      Matrix.trace (A * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, A] : List (Matrix n n ℂ)))

  have hrot_1000001010 : Matrix.trace (B * A * A * A * A * A * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A] : List (Matrix n n ℂ)))

  have hrot_1000001011 : Matrix.trace (B * A * A * A * A * A * B * A * B * B) =
      Matrix.trace (B * B * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1000001100 : Matrix.trace (B * A * A * A * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_1000001101 : Matrix.trace (B * A * A * A * A * A * B * B * A * B) =
      Matrix.trace (B * A * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_1000001110 : Matrix.trace (B * A * A * A * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1000001111 : Matrix.trace (B * A * A * A * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1000010000 : Matrix.trace (B * A * A * A * A * B * A * A * A * A) =
      Matrix.trace (A * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1000010010 : Matrix.trace (B * A * A * A * A * B * A * A * B * A) =
      Matrix.trace (A * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_1000010011 : Matrix.trace (B * A * A * A * A * B * A * A * B * B) =
      Matrix.trace (B * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1000010100 : Matrix.trace (B * A * A * A * A * B * A * B * A * A) =
      Matrix.trace (A * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1000010110 : Matrix.trace (B * A * A * A * A * B * A * B * B * A) =
      Matrix.trace (B * A * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1000010111 : Matrix.trace (B * A * A * A * A * B * A * B * B * B) =
      Matrix.trace (B * B * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1000011000 : Matrix.trace (B * A * A * A * A * B * B * A * A * A) =
      Matrix.trace (B * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1000011001 : Matrix.trace (B * A * A * A * A * B * B * A * A * B) =
      Matrix.trace (B * A * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1000011010 : Matrix.trace (B * A * A * A * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1000011011 : Matrix.trace (B * A * A * A * A * B * B * A * B * B) =
      Matrix.trace (B * B * A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1000011100 : Matrix.trace (B * A * A * A * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1000011101 : Matrix.trace (B * A * A * A * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1000011110 : Matrix.trace (B * A * A * A * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1000011111 : Matrix.trace (B * A * A * A * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1000100000 : Matrix.trace (B * A * A * A * B * A * A * A * A * A) =
      Matrix.trace (A * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, A, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1000100010 : Matrix.trace (B * A * A * A * B * A * A * A * B * A) =
      Matrix.trace (A * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_1000100011 : Matrix.trace (B * A * A * A * B * A * A * A * B * B) =
      Matrix.trace (B * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1000100100 : Matrix.trace (B * A * A * A * B * A * A * B * A * A) =
      Matrix.trace (A * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1000100110 : Matrix.trace (B * A * A * A * B * A * A * B * B * A) =
      Matrix.trace (B * A * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1000100111 : Matrix.trace (B * A * A * A * B * A * A * B * B * B) =
      Matrix.trace (B * B * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1000101000 : Matrix.trace (B * A * A * A * B * A * B * A * A * A) =
      Matrix.trace (A * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1000101010 : Matrix.trace (B * A * A * A * B * A * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1000101011 : Matrix.trace (B * A * A * A * B * A * B * A * B * B) =
      Matrix.trace (B * B * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1000101100 : Matrix.trace (B * A * A * A * B * A * B * B * A * A) =
      Matrix.trace (B * A * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_1000101101 : Matrix.trace (B * A * A * A * B * A * B * B * A * B) =
      Matrix.trace (B * A * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_1000101110 : Matrix.trace (B * A * A * A * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1000101111 : Matrix.trace (B * A * A * A * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1000110000 : Matrix.trace (B * A * A * A * B * B * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1000110010 : Matrix.trace (B * A * A * A * B * B * A * A * B * A) =
      Matrix.trace (B * A * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1000110011 : Matrix.trace (B * A * A * A * B * B * A * A * B * B) =
      Matrix.trace (B * B * A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1000110100 : Matrix.trace (B * A * A * A * B * B * A * B * A * A) =
      Matrix.trace (B * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1000110101 : Matrix.trace (B * A * A * A * B * B * A * B * A * B) =
      Matrix.trace (B * A * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1000110110 : Matrix.trace (B * A * A * A * B * B * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1000110111 : Matrix.trace (B * A * A * A * B * B * A * B * B * B) =
      Matrix.trace (B * B * B * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1000111000 : Matrix.trace (B * A * A * A * B * B * B * A * A * A) =
      Matrix.trace (B * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1000111001 : Matrix.trace (B * A * A * A * B * B * B * A * A * B) =
      Matrix.trace (B * B * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1000111010 : Matrix.trace (B * A * A * A * B * B * B * A * B * A) =
      Matrix.trace (B * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1000111011 : Matrix.trace (B * A * A * A * B * B * B * A * B * B) =
      Matrix.trace (B * B * A * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_1000111100 : Matrix.trace (B * A * A * A * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1000111101 : Matrix.trace (B * A * A * A * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1000111110 : Matrix.trace (B * A * A * A * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1000111111 : Matrix.trace (B * A * A * A * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1001000000 : Matrix.trace (B * A * A * B * A * A * A * A * A * A) =
      Matrix.trace (A * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1001000010 : Matrix.trace (B * A * A * B * A * A * A * A * B * A) =
      Matrix.trace (A * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_1001000011 : Matrix.trace (B * A * A * B * A * A * A * A * B * B) =
      Matrix.trace (B * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1001000100 : Matrix.trace (B * A * A * B * A * A * A * B * A * A) =
      Matrix.trace (A * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A, A] : List (Matrix n n ℂ)))

  have hrot_1001000110 : Matrix.trace (B * A * A * B * A * A * A * B * B * A) =
      Matrix.trace (B * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1001000111 : Matrix.trace (B * A * A * B * A * A * A * B * B * B) =
      Matrix.trace (B * B * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1001001000 : Matrix.trace (B * A * A * B * A * A * B * A * A * A) =
      Matrix.trace (A * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, A, B, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1001001010 : Matrix.trace (B * A * A * B * A * A * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([A, B, A] : List (Matrix n n ℂ)))

  have hrot_1001001011 : Matrix.trace (B * A * A * B * A * A * B * A * B * B) =
      Matrix.trace (B * B * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1001001100 : Matrix.trace (B * A * A * B * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_1001001101 : Matrix.trace (B * A * A * B * A * A * B * B * A * B) =
      Matrix.trace (B * A * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_1001001110 : Matrix.trace (B * A * A * B * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1001001111 : Matrix.trace (B * A * A * B * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1001010000 : Matrix.trace (B * A * A * B * A * B * A * A * A * A) =
      Matrix.trace (A * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1001010010 : Matrix.trace (B * A * A * B * A * B * A * A * B * A) =
      Matrix.trace (A * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1001010011 : Matrix.trace (B * A * A * B * A * B * A * A * B * B) =
      Matrix.trace (B * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1001010100 : Matrix.trace (B * A * A * B * A * B * A * B * A * A) =
      Matrix.trace (A * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1001010110 : Matrix.trace (B * A * A * B * A * B * A * B * B * A) =
      Matrix.trace (B * A * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1001010111 : Matrix.trace (B * A * A * B * A * B * A * B * B * B) =
      Matrix.trace (B * B * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1001011000 : Matrix.trace (B * A * A * B * A * B * B * A * A * A) =
      Matrix.trace (B * A * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1001011001 : Matrix.trace (B * A * A * B * A * B * B * A * A * B) =
      Matrix.trace (B * A * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1001011010 : Matrix.trace (B * A * A * B * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1001011011 : Matrix.trace (B * A * A * B * A * B * B * A * B * B) =
      Matrix.trace (B * B * A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1001011100 : Matrix.trace (B * A * A * B * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1001011101 : Matrix.trace (B * A * A * B * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1001011110 : Matrix.trace (B * A * A * B * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1001011111 : Matrix.trace (B * A * A * B * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1001100000 : Matrix.trace (B * A * A * B * B * A * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1001100010 : Matrix.trace (B * A * A * B * B * A * A * A * B * A) =
      Matrix.trace (B * A * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1001100011 : Matrix.trace (B * A * A * B * B * A * A * A * B * B) =
      Matrix.trace (B * B * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1001100100 : Matrix.trace (B * A * A * B * B * A * A * B * A * A) =
      Matrix.trace (B * A * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1001100110 : Matrix.trace (B * A * A * B * B * A * A * B * B * A) =
      Matrix.trace (B * A * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1001100111 : Matrix.trace (B * A * A * B * B * A * A * B * B * B) =
      Matrix.trace (B * B * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1001101000 : Matrix.trace (B * A * A * B * B * A * B * A * A * A) =
      Matrix.trace (B * A * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1001101001 : Matrix.trace (B * A * A * B * B * A * B * A * A * B) =
      Matrix.trace (B * A * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1001101010 : Matrix.trace (B * A * A * B * B * A * B * A * B * A) =
      Matrix.trace (B * A * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1001101011 : Matrix.trace (B * A * A * B * B * A * B * A * B * B) =
      Matrix.trace (B * B * A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1001101100 : Matrix.trace (B * A * A * B * B * A * B * B * A * A) =
      Matrix.trace (B * A * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1001101101 : Matrix.trace (B * A * A * B * B * A * B * B * A * B) =
      Matrix.trace (B * A * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1001101110 : Matrix.trace (B * A * A * B * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1001101111 : Matrix.trace (B * A * A * B * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1001110000 : Matrix.trace (B * A * A * B * B * B * A * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1001110001 : Matrix.trace (B * A * A * B * B * B * A * A * A * B) =
      Matrix.trace (B * B * A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1001110010 : Matrix.trace (B * A * A * B * B * B * A * A * B * A) =
      Matrix.trace (B * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1001110011 : Matrix.trace (B * A * A * B * B * B * A * A * B * B) =
      Matrix.trace (B * B * A * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_1001110100 : Matrix.trace (B * A * A * B * B * B * A * B * A * A) =
      Matrix.trace (B * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1001110101 : Matrix.trace (B * A * A * B * B * B * A * B * A * B) =
      Matrix.trace (B * B * A * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1001110110 : Matrix.trace (B * A * A * B * B * B * A * B * B * A) =
      Matrix.trace (B * B * A * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1001110111 : Matrix.trace (B * A * A * B * B * B * A * B * B * B) =
      Matrix.trace (B * B * B * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1001111000 : Matrix.trace (B * A * A * B * B * B * B * A * A * A) =
      Matrix.trace (B * B * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1001111001 : Matrix.trace (B * A * A * B * B * B * B * A * A * B) =
      Matrix.trace (B * B * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1001111010 : Matrix.trace (B * A * A * B * B * B * B * A * B * A) =
      Matrix.trace (B * B * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1001111011 : Matrix.trace (B * A * A * B * B * B * B * A * B * B) =
      Matrix.trace (B * B * B * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_1001111100 : Matrix.trace (B * A * A * B * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1001111101 : Matrix.trace (B * A * A * B * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1001111110 : Matrix.trace (B * A * A * B * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1001111111 : Matrix.trace (B * A * A * B * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1010000000 : Matrix.trace (B * A * B * A * A * A * A * A * A * A) =
      Matrix.trace (A * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1010000010 : Matrix.trace (B * A * B * A * A * A * A * A * B * A) =
      Matrix.trace (A * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_1010000011 : Matrix.trace (B * A * B * A * A * A * A * A * B * B) =
      Matrix.trace (B * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1010000100 : Matrix.trace (B * A * B * A * A * A * A * B * A * A) =
      Matrix.trace (A * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1010000110 : Matrix.trace (B * A * B * A * A * A * A * B * B * A) =
      Matrix.trace (B * A * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1010000111 : Matrix.trace (B * A * B * A * A * A * A * B * B * B) =
      Matrix.trace (B * B * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1010001000 : Matrix.trace (B * A * B * A * A * A * B * A * A * A) =
      Matrix.trace (A * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1010001010 : Matrix.trace (B * A * B * A * A * A * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A, B, A] : List (Matrix n n ℂ)))

  have hrot_1010001011 : Matrix.trace (B * A * B * A * A * A * B * A * B * B) =
      Matrix.trace (B * B * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1010001100 : Matrix.trace (B * A * B * A * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_1010001101 : Matrix.trace (B * A * B * A * A * A * B * B * A * B) =
      Matrix.trace (B * A * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_1010001110 : Matrix.trace (B * A * B * A * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1010001111 : Matrix.trace (B * A * B * A * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1010010000 : Matrix.trace (B * A * B * A * A * B * A * A * A * A) =
      Matrix.trace (A * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1010010010 : Matrix.trace (B * A * B * A * A * B * A * A * B * A) =
      Matrix.trace (A * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_1010010011 : Matrix.trace (B * A * B * A * A * B * A * A * B * B) =
      Matrix.trace (B * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1010010100 : Matrix.trace (B * A * B * A * A * B * A * B * A * A) =
      Matrix.trace (A * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1010010110 : Matrix.trace (B * A * B * A * A * B * A * B * B * A) =
      Matrix.trace (B * A * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1010010111 : Matrix.trace (B * A * B * A * A * B * A * B * B * B) =
      Matrix.trace (B * B * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1010011000 : Matrix.trace (B * A * B * A * A * B * B * A * A * A) =
      Matrix.trace (B * A * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1010011010 : Matrix.trace (B * A * B * A * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1010011011 : Matrix.trace (B * A * B * A * A * B * B * A * B * B) =
      Matrix.trace (B * B * A * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1010011100 : Matrix.trace (B * A * B * A * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1010011101 : Matrix.trace (B * A * B * A * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1010011110 : Matrix.trace (B * A * B * A * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1010011111 : Matrix.trace (B * A * B * A * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1010100000 : Matrix.trace (B * A * B * A * B * A * A * A * A * A) =
      Matrix.trace (A * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1010100010 : Matrix.trace (B * A * B * A * B * A * A * A * B * A) =
      Matrix.trace (A * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([A] : List (Matrix n n ℂ)))

  have hrot_1010100011 : Matrix.trace (B * A * B * A * B * A * A * A * B * B) =
      Matrix.trace (B * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1010100100 : Matrix.trace (B * A * B * A * B * A * A * B * A * A) =
      Matrix.trace (A * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1010100110 : Matrix.trace (B * A * B * A * B * A * A * B * B * A) =
      Matrix.trace (B * A * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1010100111 : Matrix.trace (B * A * B * A * B * A * A * B * B * B) =
      Matrix.trace (B * B * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1010101000 : Matrix.trace (B * A * B * A * B * A * B * A * A * A) =
      Matrix.trace (A * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1010101010 : Matrix.trace (B * A * B * A * B * A * B * A * B * A) =
      Matrix.trace (A * B * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([A, B, A, B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1010101011 : Matrix.trace (B * A * B * A * B * A * B * A * B * B) =
      Matrix.trace (B * B * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1010101100 : Matrix.trace (B * A * B * A * B * A * B * B * A * A) =
      Matrix.trace (B * A * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_1010101101 : Matrix.trace (B * A * B * A * B * A * B * B * A * B) =
      Matrix.trace (B * A * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_1010101110 : Matrix.trace (B * A * B * A * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1010101111 : Matrix.trace (B * A * B * A * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1010110000 : Matrix.trace (B * A * B * A * B * B * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1010110010 : Matrix.trace (B * A * B * A * B * B * A * A * B * A) =
      Matrix.trace (B * A * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1010110011 : Matrix.trace (B * A * B * A * B * B * A * A * B * B) =
      Matrix.trace (B * B * A * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1010110100 : Matrix.trace (B * A * B * A * B * B * A * B * A * A) =
      Matrix.trace (B * A * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1010110110 : Matrix.trace (B * A * B * A * B * B * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1010110111 : Matrix.trace (B * A * B * A * B * B * A * B * B * B) =
      Matrix.trace (B * B * B * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1010111000 : Matrix.trace (B * A * B * A * B * B * B * A * A * A) =
      Matrix.trace (B * B * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1010111001 : Matrix.trace (B * A * B * A * B * B * B * A * A * B) =
      Matrix.trace (B * B * A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1010111010 : Matrix.trace (B * A * B * A * B * B * B * A * B * A) =
      Matrix.trace (B * B * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1010111011 : Matrix.trace (B * A * B * A * B * B * B * A * B * B) =
      Matrix.trace (B * B * A * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_1010111100 : Matrix.trace (B * A * B * A * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1010111101 : Matrix.trace (B * A * B * A * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1010111110 : Matrix.trace (B * A * B * A * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1010111111 : Matrix.trace (B * A * B * A * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1011000000 : Matrix.trace (B * A * B * B * A * A * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1011000010 : Matrix.trace (B * A * B * B * A * A * A * A * B * A) =
      Matrix.trace (B * A * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1011000011 : Matrix.trace (B * A * B * B * A * A * A * A * B * B) =
      Matrix.trace (B * B * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1011000100 : Matrix.trace (B * A * B * B * A * A * A * B * A * A) =
      Matrix.trace (B * A * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1011000110 : Matrix.trace (B * A * B * B * A * A * A * B * B * A) =
      Matrix.trace (B * A * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1011000111 : Matrix.trace (B * A * B * B * A * A * A * B * B * B) =
      Matrix.trace (B * B * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1011001000 : Matrix.trace (B * A * B * B * A * A * B * A * A * A) =
      Matrix.trace (B * A * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1011001010 : Matrix.trace (B * A * B * B * A * A * B * A * B * A) =
      Matrix.trace (B * A * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1011001011 : Matrix.trace (B * A * B * B * A * A * B * A * B * B) =
      Matrix.trace (B * B * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1011001100 : Matrix.trace (B * A * B * B * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1011001101 : Matrix.trace (B * A * B * B * A * A * B * B * A * B) =
      Matrix.trace (B * A * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B] : List (Matrix n n ℂ)))

  have hrot_1011001110 : Matrix.trace (B * A * B * B * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1011001111 : Matrix.trace (B * A * B * B * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1011010000 : Matrix.trace (B * A * B * B * A * B * A * A * A * A) =
      Matrix.trace (B * A * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1011010010 : Matrix.trace (B * A * B * B * A * B * A * A * B * A) =
      Matrix.trace (B * A * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1011010011 : Matrix.trace (B * A * B * B * A * B * A * A * B * B) =
      Matrix.trace (B * B * A * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1011010100 : Matrix.trace (B * A * B * B * A * B * A * B * A * A) =
      Matrix.trace (B * A * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1011010110 : Matrix.trace (B * A * B * B * A * B * A * B * B * A) =
      Matrix.trace (B * A * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1011010111 : Matrix.trace (B * A * B * B * A * B * A * B * B * B) =
      Matrix.trace (B * B * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1011011000 : Matrix.trace (B * A * B * B * A * B * B * A * A * A) =
      Matrix.trace (B * A * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1011011010 : Matrix.trace (B * A * B * B * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1011011011 : Matrix.trace (B * A * B * B * A * B * B * A * B * B) =
      Matrix.trace (B * B * A * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1011011100 : Matrix.trace (B * A * B * B * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1011011101 : Matrix.trace (B * A * B * B * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1011011110 : Matrix.trace (B * A * B * B * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1011011111 : Matrix.trace (B * A * B * B * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1011100000 : Matrix.trace (B * A * B * B * B * A * A * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1011100001 : Matrix.trace (B * A * B * B * B * A * A * A * A * B) =
      Matrix.trace (B * B * A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1011100010 : Matrix.trace (B * A * B * B * B * A * A * A * B * A) =
      Matrix.trace (B * B * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1011100011 : Matrix.trace (B * A * B * B * B * A * A * A * B * B) =
      Matrix.trace (B * B * A * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1011100100 : Matrix.trace (B * A * B * B * B * A * A * B * A * A) =
      Matrix.trace (B * B * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1011100101 : Matrix.trace (B * A * B * B * B * A * A * B * A * B) =
      Matrix.trace (B * B * A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1011100110 : Matrix.trace (B * A * B * B * B * A * A * B * B * A) =
      Matrix.trace (B * B * A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1011100111 : Matrix.trace (B * A * B * B * B * A * A * B * B * B) =
      Matrix.trace (B * B * B * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1011101000 : Matrix.trace (B * A * B * B * B * A * B * A * A * A) =
      Matrix.trace (B * B * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1011101001 : Matrix.trace (B * A * B * B * B * A * B * A * A * B) =
      Matrix.trace (B * B * A * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1011101010 : Matrix.trace (B * A * B * B * B * A * B * A * B * A) =
      Matrix.trace (B * B * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1011101011 : Matrix.trace (B * A * B * B * B * A * B * A * B * B) =
      Matrix.trace (B * B * A * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1011101100 : Matrix.trace (B * A * B * B * B * A * B * B * A * A) =
      Matrix.trace (B * B * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1011101101 : Matrix.trace (B * A * B * B * B * A * B * B * A * B) =
      Matrix.trace (B * B * A * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1011101110 : Matrix.trace (B * A * B * B * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1011101111 : Matrix.trace (B * A * B * B * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1011110000 : Matrix.trace (B * A * B * B * B * B * A * A * A * A) =
      Matrix.trace (B * B * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1011110001 : Matrix.trace (B * A * B * B * B * B * A * A * A * B) =
      Matrix.trace (B * B * B * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1011110010 : Matrix.trace (B * A * B * B * B * B * A * A * B * A) =
      Matrix.trace (B * B * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1011110011 : Matrix.trace (B * A * B * B * B * B * A * A * B * B) =
      Matrix.trace (B * B * B * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, B] : List (Matrix n n ℂ)))

  have hrot_1011110100 : Matrix.trace (B * A * B * B * B * B * A * B * A * A) =
      Matrix.trace (B * B * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1011110101 : Matrix.trace (B * A * B * B * B * B * A * B * A * B) =
      Matrix.trace (B * B * B * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1011110110 : Matrix.trace (B * A * B * B * B * B * A * B * B * A) =
      Matrix.trace (B * B * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1011110111 : Matrix.trace (B * A * B * B * B * B * A * B * B * B) =
      Matrix.trace (B * B * B * A * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1011111000 : Matrix.trace (B * A * B * B * B * B * B * A * A * A) =
      Matrix.trace (B * B * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1011111001 : Matrix.trace (B * A * B * B * B * B * B * A * A * B) =
      Matrix.trace (B * B * B * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1011111010 : Matrix.trace (B * A * B * B * B * B * B * A * B * A) =
      Matrix.trace (B * B * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1011111011 : Matrix.trace (B * A * B * B * B * B * B * A * B * B) =
      Matrix.trace (B * B * B * B * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_1011111100 : Matrix.trace (B * A * B * B * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1011111101 : Matrix.trace (B * A * B * B * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1011111110 : Matrix.trace (B * A * B * B * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1011111111 : Matrix.trace (B * A * B * B * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1100000000 : Matrix.trace (B * B * A * A * A * A * A * A * A * A) =
      Matrix.trace (B * A * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1100000010 : Matrix.trace (B * B * A * A * A * A * A * A * B * A) =
      Matrix.trace (B * A * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1100000011 : Matrix.trace (B * B * A * A * A * A * A * A * B * B) =
      Matrix.trace (B * B * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1100000100 : Matrix.trace (B * B * A * A * A * A * A * B * A * A) =
      Matrix.trace (B * A * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1100000110 : Matrix.trace (B * B * A * A * A * A * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1100000111 : Matrix.trace (B * B * A * A * A * A * A * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1100001000 : Matrix.trace (B * B * A * A * A * A * B * A * A * A) =
      Matrix.trace (B * A * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1100001010 : Matrix.trace (B * B * A * A * A * A * B * A * B * A) =
      Matrix.trace (B * A * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, A, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1100001011 : Matrix.trace (B * B * A * A * A * A * B * A * B * B) =
      Matrix.trace (B * B * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1100001100 : Matrix.trace (B * B * A * A * A * A * B * B * A * A) =
      Matrix.trace (B * A * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_1100001110 : Matrix.trace (B * B * A * A * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1100001111 : Matrix.trace (B * B * A * A * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1100010000 : Matrix.trace (B * B * A * A * A * B * A * A * A * A) =
      Matrix.trace (B * A * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1100010010 : Matrix.trace (B * B * A * A * A * B * A * A * B * A) =
      Matrix.trace (B * A * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1100010011 : Matrix.trace (B * B * A * A * A * B * A * A * B * B) =
      Matrix.trace (B * B * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1100010100 : Matrix.trace (B * B * A * A * A * B * A * B * A * A) =
      Matrix.trace (B * A * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1100010110 : Matrix.trace (B * B * A * A * A * B * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1100010111 : Matrix.trace (B * B * A * A * A * B * A * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1100011000 : Matrix.trace (B * B * A * A * A * B * B * A * A * A) =
      Matrix.trace (B * A * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, A, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1100011010 : Matrix.trace (B * B * A * A * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1100011011 : Matrix.trace (B * B * A * A * A * B * B * A * B * B) =
      Matrix.trace (B * B * B * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1100011100 : Matrix.trace (B * B * A * A * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1100011101 : Matrix.trace (B * B * A * A * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1100011110 : Matrix.trace (B * B * A * A * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1100011111 : Matrix.trace (B * B * A * A * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1100100000 : Matrix.trace (B * B * A * A * B * A * A * A * A * A) =
      Matrix.trace (B * A * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1100100010 : Matrix.trace (B * B * A * A * B * A * A * A * B * A) =
      Matrix.trace (B * A * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1100100011 : Matrix.trace (B * B * A * A * B * A * A * A * B * B) =
      Matrix.trace (B * B * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1100100100 : Matrix.trace (B * B * A * A * B * A * A * B * A * A) =
      Matrix.trace (B * A * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1100100110 : Matrix.trace (B * B * A * A * B * A * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1100100111 : Matrix.trace (B * B * A * A * B * A * A * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1100101000 : Matrix.trace (B * B * A * A * B * A * B * A * A * A) =
      Matrix.trace (B * A * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1100101010 : Matrix.trace (B * B * A * A * B * A * B * A * B * A) =
      Matrix.trace (B * A * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1100101011 : Matrix.trace (B * B * A * A * B * A * B * A * B * B) =
      Matrix.trace (B * B * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1100101100 : Matrix.trace (B * B * A * A * B * A * B * B * A * A) =
      Matrix.trace (B * A * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, A, A] : List (Matrix n n ℂ)))

  have hrot_1100101110 : Matrix.trace (B * B * A * A * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1100101111 : Matrix.trace (B * B * A * A * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1100110000 : Matrix.trace (B * B * A * A * B * B * A * A * A * A) =
      Matrix.trace (B * A * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, B, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1100110010 : Matrix.trace (B * B * A * A * B * B * A * A * B * A) =
      Matrix.trace (B * A * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, A, B, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1100110011 : Matrix.trace (B * B * A * A * B * B * A * A * B * B) =
      Matrix.trace (B * B * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1100110100 : Matrix.trace (B * B * A * A * B * B * A * B * A * A) =
      Matrix.trace (B * A * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1100110110 : Matrix.trace (B * B * A * A * B * B * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B] : List (Matrix n n ℂ)) ([B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1100110111 : Matrix.trace (B * B * A * A * B * B * A * B * B * B) =
      Matrix.trace (B * B * B * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1100111000 : Matrix.trace (B * B * A * A * B * B * B * A * A * A) =
      Matrix.trace (B * B * A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1100111010 : Matrix.trace (B * B * A * A * B * B * B * A * B * A) =
      Matrix.trace (B * B * A * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1100111011 : Matrix.trace (B * B * A * A * B * B * B * A * B * B) =
      Matrix.trace (B * B * B * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B, B, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1100111100 : Matrix.trace (B * B * A * A * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1100111101 : Matrix.trace (B * B * A * A * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1100111110 : Matrix.trace (B * B * A * A * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1100111111 : Matrix.trace (B * B * A * A * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1101000000 : Matrix.trace (B * B * A * B * A * A * A * A * A * A) =
      Matrix.trace (B * A * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1101000010 : Matrix.trace (B * B * A * B * A * A * A * A * B * A) =
      Matrix.trace (B * A * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1101000011 : Matrix.trace (B * B * A * B * A * A * A * A * B * B) =
      Matrix.trace (B * B * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1101000100 : Matrix.trace (B * B * A * B * A * A * A * B * A * A) =
      Matrix.trace (B * A * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1101000110 : Matrix.trace (B * B * A * B * A * A * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1101000111 : Matrix.trace (B * B * A * B * A * A * A * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1101001000 : Matrix.trace (B * B * A * B * A * A * B * A * A * A) =
      Matrix.trace (B * A * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1101001010 : Matrix.trace (B * B * A * B * A * A * B * A * B * A) =
      Matrix.trace (B * A * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1101001011 : Matrix.trace (B * B * A * B * A * A * B * A * B * B) =
      Matrix.trace (B * B * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1101001100 : Matrix.trace (B * B * A * B * A * A * B * B * A * A) =
      Matrix.trace (B * A * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, A, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1101001110 : Matrix.trace (B * B * A * B * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1101001111 : Matrix.trace (B * B * A * B * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1101010000 : Matrix.trace (B * B * A * B * A * B * A * A * A * A) =
      Matrix.trace (B * A * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1101010010 : Matrix.trace (B * B * A * B * A * B * A * A * B * A) =
      Matrix.trace (B * A * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1101010011 : Matrix.trace (B * B * A * B * A * B * A * A * B * B) =
      Matrix.trace (B * B * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1101010100 : Matrix.trace (B * B * A * B * A * B * A * B * A * A) =
      Matrix.trace (B * A * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1101010110 : Matrix.trace (B * B * A * B * A * B * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1101010111 : Matrix.trace (B * B * A * B * A * B * A * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1101011000 : Matrix.trace (B * B * A * B * A * B * B * A * A * A) =
      Matrix.trace (B * A * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, A, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1101011010 : Matrix.trace (B * B * A * B * A * B * B * A * B * A) =
      Matrix.trace (B * A * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, A, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1101011011 : Matrix.trace (B * B * A * B * A * B * B * A * B * B) =
      Matrix.trace (B * B * B * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1101011100 : Matrix.trace (B * B * A * B * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1101011101 : Matrix.trace (B * B * A * B * A * B * B * B * A * B) =
      Matrix.trace (B * B * A * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1101011110 : Matrix.trace (B * B * A * B * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1101011111 : Matrix.trace (B * B * A * B * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1101100000 : Matrix.trace (B * B * A * B * B * A * A * A * A * A) =
      Matrix.trace (B * A * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1101100010 : Matrix.trace (B * B * A * B * B * A * A * A * B * A) =
      Matrix.trace (B * A * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1101100011 : Matrix.trace (B * B * A * B * B * A * A * A * B * B) =
      Matrix.trace (B * B * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1101100100 : Matrix.trace (B * B * A * B * B * A * A * B * A * A) =
      Matrix.trace (B * A * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1101100110 : Matrix.trace (B * B * A * B * B * A * A * B * B * A) =
      Matrix.trace (B * A * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, A] : List (Matrix n n ℂ)))

  have hrot_1101100111 : Matrix.trace (B * B * A * B * B * A * A * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1101101000 : Matrix.trace (B * B * A * B * B * A * B * A * A * A) =
      Matrix.trace (B * A * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1101101010 : Matrix.trace (B * B * A * B * B * A * B * A * B * A) =
      Matrix.trace (B * A * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1101101011 : Matrix.trace (B * B * A * B * B * A * B * A * B * B) =
      Matrix.trace (B * B * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1101101100 : Matrix.trace (B * B * A * B * B * A * B * B * A * A) =
      Matrix.trace (B * A * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, A, B, B, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1101101110 : Matrix.trace (B * B * A * B * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1101101111 : Matrix.trace (B * B * A * B * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1101110000 : Matrix.trace (B * B * A * B * B * B * A * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1101110010 : Matrix.trace (B * B * A * B * B * B * A * A * B * A) =
      Matrix.trace (B * B * A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1101110011 : Matrix.trace (B * B * A * B * B * B * A * A * B * B) =
      Matrix.trace (B * B * B * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1101110100 : Matrix.trace (B * B * A * B * B * B * A * B * A * A) =
      Matrix.trace (B * B * A * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1101110110 : Matrix.trace (B * B * A * B * B * B * A * B * B * A) =
      Matrix.trace (B * B * A * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1101110111 : Matrix.trace (B * B * A * B * B * B * A * B * B * B) =
      Matrix.trace (B * B * B * B * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1101111000 : Matrix.trace (B * B * A * B * B * B * B * A * A * A) =
      Matrix.trace (B * B * B * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1101111001 : Matrix.trace (B * B * A * B * B * B * B * A * A * B) =
      Matrix.trace (B * B * B * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B] : List (Matrix n n ℂ)))

  have hrot_1101111010 : Matrix.trace (B * B * A * B * B * B * B * A * B * A) =
      Matrix.trace (B * B * B * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1101111011 : Matrix.trace (B * B * A * B * B * B * B * A * B * B) =
      Matrix.trace (B * B * B * A * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B] : List (Matrix n n ℂ)))

  have hrot_1101111100 : Matrix.trace (B * B * A * B * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1101111101 : Matrix.trace (B * B * A * B * B * B * B * B * A * B) =
      Matrix.trace (B * B * B * B * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B] : List (Matrix n n ℂ)))

  have hrot_1101111110 : Matrix.trace (B * B * A * B * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1101111111 : Matrix.trace (B * B * A * B * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1110000000 : Matrix.trace (B * B * B * A * A * A * A * A * A * A) =
      Matrix.trace (B * B * A * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1110000010 : Matrix.trace (B * B * B * A * A * A * A * A * B * A) =
      Matrix.trace (B * B * A * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1110000011 : Matrix.trace (B * B * B * A * A * A * A * A * B * B) =
      Matrix.trace (B * B * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1110000100 : Matrix.trace (B * B * B * A * A * A * A * B * A * A) =
      Matrix.trace (B * B * A * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1110000110 : Matrix.trace (B * B * B * A * A * A * A * B * B * A) =
      Matrix.trace (B * B * A * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1110000111 : Matrix.trace (B * B * B * A * A * A * A * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1110001000 : Matrix.trace (B * B * B * A * A * A * B * A * A * A) =
      Matrix.trace (B * B * A * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1110001010 : Matrix.trace (B * B * B * A * A * A * B * A * B * A) =
      Matrix.trace (B * B * A * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1110001011 : Matrix.trace (B * B * B * A * A * A * B * A * B * B) =
      Matrix.trace (B * B * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1110001100 : Matrix.trace (B * B * B * A * A * A * B * B * A * A) =
      Matrix.trace (B * B * A * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1110001110 : Matrix.trace (B * B * B * A * A * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1110001111 : Matrix.trace (B * B * B * A * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1110010000 : Matrix.trace (B * B * B * A * A * B * A * A * A * A) =
      Matrix.trace (B * B * A * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1110010010 : Matrix.trace (B * B * B * A * A * B * A * A * B * A) =
      Matrix.trace (B * B * A * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1110010011 : Matrix.trace (B * B * B * A * A * B * A * A * B * B) =
      Matrix.trace (B * B * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1110010100 : Matrix.trace (B * B * B * A * A * B * A * B * A * A) =
      Matrix.trace (B * B * A * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1110010110 : Matrix.trace (B * B * B * A * A * B * A * B * B * A) =
      Matrix.trace (B * B * A * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1110010111 : Matrix.trace (B * B * B * A * A * B * A * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1110011000 : Matrix.trace (B * B * B * A * A * B * B * A * A * A) =
      Matrix.trace (B * B * A * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1110011010 : Matrix.trace (B * B * B * A * A * B * B * A * B * A) =
      Matrix.trace (B * B * A * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1110011011 : Matrix.trace (B * B * B * A * A * B * B * A * B * B) =
      Matrix.trace (B * B * B * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, A, B, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1110011100 : Matrix.trace (B * B * B * A * A * B * B * B * A * A) =
      Matrix.trace (B * B * A * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, A, B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1110011110 : Matrix.trace (B * B * B * A * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1110011111 : Matrix.trace (B * B * B * A * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1110100000 : Matrix.trace (B * B * B * A * B * A * A * A * A * A) =
      Matrix.trace (B * B * A * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1110100010 : Matrix.trace (B * B * B * A * B * A * A * A * B * A) =
      Matrix.trace (B * B * A * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1110100011 : Matrix.trace (B * B * B * A * B * A * A * A * B * B) =
      Matrix.trace (B * B * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1110100100 : Matrix.trace (B * B * B * A * B * A * A * B * A * A) =
      Matrix.trace (B * B * A * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1110100110 : Matrix.trace (B * B * B * A * B * A * A * B * B * A) =
      Matrix.trace (B * B * A * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1110100111 : Matrix.trace (B * B * B * A * B * A * A * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1110101000 : Matrix.trace (B * B * B * A * B * A * B * A * A * A) =
      Matrix.trace (B * B * A * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1110101010 : Matrix.trace (B * B * B * A * B * A * B * A * B * A) =
      Matrix.trace (B * B * A * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1110101011 : Matrix.trace (B * B * B * A * B * A * B * A * B * B) =
      Matrix.trace (B * B * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1110101100 : Matrix.trace (B * B * B * A * B * A * B * B * A * A) =
      Matrix.trace (B * B * A * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1110101110 : Matrix.trace (B * B * B * A * B * A * B * B * B * A) =
      Matrix.trace (B * B * A * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, A] : List (Matrix n n ℂ)))

  have hrot_1110101111 : Matrix.trace (B * B * B * A * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1110110000 : Matrix.trace (B * B * B * A * B * B * A * A * A * A) =
      Matrix.trace (B * B * A * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1110110010 : Matrix.trace (B * B * B * A * B * B * A * A * B * A) =
      Matrix.trace (B * B * A * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1110110011 : Matrix.trace (B * B * B * A * B * B * A * A * B * B) =
      Matrix.trace (B * B * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1110110100 : Matrix.trace (B * B * B * A * B * B * A * B * A * A) =
      Matrix.trace (B * B * A * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1110110110 : Matrix.trace (B * B * B * A * B * B * A * B * B * A) =
      Matrix.trace (B * B * A * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1110110111 : Matrix.trace (B * B * B * A * B * B * A * B * B * B) =
      Matrix.trace (B * B * B * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1110111000 : Matrix.trace (B * B * B * A * B * B * B * A * A * A) =
      Matrix.trace (B * B * A * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1110111010 : Matrix.trace (B * B * B * A * B * B * B * A * B * A) =
      Matrix.trace (B * B * A * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, A, B, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1110111011 : Matrix.trace (B * B * B * A * B * B * B * A * B * B) =
      Matrix.trace (B * B * B * B * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B, B, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1110111100 : Matrix.trace (B * B * B * A * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1110111110 : Matrix.trace (B * B * B * A * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1110111111 : Matrix.trace (B * B * B * A * B * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1111000000 : Matrix.trace (B * B * B * B * A * A * A * A * A * A) =
      Matrix.trace (B * B * B * A * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1111000010 : Matrix.trace (B * B * B * B * A * A * A * A * B * A) =
      Matrix.trace (B * B * B * A * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1111000011 : Matrix.trace (B * B * B * B * A * A * A * A * B * B) =
      Matrix.trace (B * B * B * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, A, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1111000100 : Matrix.trace (B * B * B * B * A * A * A * B * A * A) =
      Matrix.trace (B * B * B * A * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1111000110 : Matrix.trace (B * B * B * B * A * A * A * B * B * A) =
      Matrix.trace (B * B * B * A * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1111000111 : Matrix.trace (B * B * B * B * A * A * A * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1111001000 : Matrix.trace (B * B * B * B * A * A * B * A * A * A) =
      Matrix.trace (B * B * B * A * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1111001010 : Matrix.trace (B * B * B * B * A * A * B * A * B * A) =
      Matrix.trace (B * B * B * A * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1111001011 : Matrix.trace (B * B * B * B * A * A * B * A * B * B) =
      Matrix.trace (B * B * B * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, A, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1111001100 : Matrix.trace (B * B * B * B * A * A * B * B * A * A) =
      Matrix.trace (B * B * B * A * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1111001110 : Matrix.trace (B * B * B * B * A * A * B * B * B * A) =
      Matrix.trace (B * B * B * A * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, A, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1111001111 : Matrix.trace (B * B * B * B * A * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1111010000 : Matrix.trace (B * B * B * B * A * B * A * A * A * A) =
      Matrix.trace (B * B * B * A * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1111010010 : Matrix.trace (B * B * B * B * A * B * A * A * B * A) =
      Matrix.trace (B * B * B * A * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1111010011 : Matrix.trace (B * B * B * B * A * B * A * A * B * B) =
      Matrix.trace (B * B * B * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, A, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1111010100 : Matrix.trace (B * B * B * B * A * B * A * B * A * A) =
      Matrix.trace (B * B * B * A * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1111010110 : Matrix.trace (B * B * B * B * A * B * A * B * B * A) =
      Matrix.trace (B * B * B * A * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1111010111 : Matrix.trace (B * B * B * B * A * B * A * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1111011000 : Matrix.trace (B * B * B * B * A * B * B * A * A * A) =
      Matrix.trace (B * B * B * A * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1111011010 : Matrix.trace (B * B * B * B * A * B * B * A * B * A) =
      Matrix.trace (B * B * B * A * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1111011011 : Matrix.trace (B * B * B * B * A * B * B * A * B * B) =
      Matrix.trace (B * B * B * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, A, B, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1111011100 : Matrix.trace (B * B * B * B * A * B * B * B * A * A) =
      Matrix.trace (B * B * B * A * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1111011110 : Matrix.trace (B * B * B * B * A * B * B * B * B * A) =
      Matrix.trace (B * B * B * A * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, A, B, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1111011111 : Matrix.trace (B * B * B * B * A * B * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B, B] : List (Matrix n n ℂ)))

  have hrot_1111100000 : Matrix.trace (B * B * B * B * B * A * A * A * A * A) =
      Matrix.trace (B * B * B * B * A * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1111100010 : Matrix.trace (B * B * B * B * B * A * A * A * B * A) =
      Matrix.trace (B * B * B * B * A * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1111100011 : Matrix.trace (B * B * B * B * B * A * A * A * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B, A, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1111100100 : Matrix.trace (B * B * B * B * B * A * A * B * A * A) =
      Matrix.trace (B * B * B * B * A * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1111100110 : Matrix.trace (B * B * B * B * B * A * A * B * B * A) =
      Matrix.trace (B * B * B * B * A * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, A, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1111100111 : Matrix.trace (B * B * B * B * B * A * A * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B, A, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1111101000 : Matrix.trace (B * B * B * B * B * A * B * A * A * A) =
      Matrix.trace (B * B * B * B * A * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1111101010 : Matrix.trace (B * B * B * B * B * A * B * A * B * A) =
      Matrix.trace (B * B * B * B * A * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1111101011 : Matrix.trace (B * B * B * B * B * A * B * A * B * B) =
      Matrix.trace (B * B * B * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B, A, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1111101100 : Matrix.trace (B * B * B * B * B * A * B * B * A * A) =
      Matrix.trace (B * B * B * B * A * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1111101110 : Matrix.trace (B * B * B * B * B * A * B * B * B * A) =
      Matrix.trace (B * B * B * B * A * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, A, B, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1111101111 : Matrix.trace (B * B * B * B * B * A * B * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B, B] : List (Matrix n n ℂ)))

  have hrot_1111110000 : Matrix.trace (B * B * B * B * B * B * A * A * A * A) =
      Matrix.trace (B * B * B * B * B * A * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1111110010 : Matrix.trace (B * B * B * B * B * B * A * A * B * A) =
      Matrix.trace (B * B * B * B * B * A * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1111110011 : Matrix.trace (B * B * B * B * B * B * A * A * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B, B, A, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1111110100 : Matrix.trace (B * B * B * B * B * B * A * B * A * A) =
      Matrix.trace (B * B * B * B * B * A * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1111110110 : Matrix.trace (B * B * B * B * B * B * A * B * B * A) =
      Matrix.trace (B * B * B * B * B * A * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, B, A, B, B, A] : List (Matrix n n ℂ)))

  have hrot_1111110111 : Matrix.trace (B * B * B * B * B * B * A * B * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B, B, A, B] : List (Matrix n n ℂ)) ([B, B] : List (Matrix n n ℂ)))

  have hrot_1111111000 : Matrix.trace (B * B * B * B * B * B * B * A * A * A) =
      Matrix.trace (B * B * B * B * B * B * A * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, A, A, A] : List (Matrix n n ℂ)))

  have hrot_1111111010 : Matrix.trace (B * B * B * B * B * B * B * A * B * A) =
      Matrix.trace (B * B * B * B * B * B * A * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, A, B, A] : List (Matrix n n ℂ)))

  have hrot_1111111011 : Matrix.trace (B * B * B * B * B * B * B * A * B * B) =
      Matrix.trace (B * B * B * B * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B, B, B, B, B, B, B, A, B] : List (Matrix n n ℂ)) ([B] : List (Matrix n n ℂ)))

  have hrot_1111111100 : Matrix.trace (B * B * B * B * B * B * B * B * A * A) =
      Matrix.trace (B * B * B * B * B * B * B * A * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, B, A, A] : List (Matrix n n ℂ)))

  have hrot_1111111110 : Matrix.trace (B * B * B * B * B * B * B * B * B * A) =
      Matrix.trace (B * B * B * B * B * B * B * B * A * B) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list ([B] : List (Matrix n n ℂ)) ([B, B, B, B, B, B, B, B, A] : List (Matrix n n ℂ)))
  simp [orderedWordExpansion, List.map_append, List.sum_append]
  rw [
    hrot_0000000010,
    hrot_0000000011,
    hrot_0000000100,
    hrot_0000000101,
    hrot_0000000110,
    hrot_0000000111,
    hrot_0000001000,
    hrot_0000001001,
    hrot_0000001010,
    hrot_0000001011,
    hrot_0000001100,
    hrot_0000001101,
    hrot_0000001110,
    hrot_0000001111,
    hrot_0000010000,
    hrot_0000010001,
    hrot_0000010010,
    hrot_0000010011,
    hrot_0000010100,
    hrot_0000010101,
    hrot_0000010110,
    hrot_0000010111,
    hrot_0000011000,
    hrot_0000011001,
    hrot_0000011010,
    hrot_0000011011,
    hrot_0000011100,
    hrot_0000011101,
    hrot_0000011110,
    hrot_0000011111,
    hrot_0000100000,
    hrot_0000100010,
    hrot_0000100011,
    hrot_0000100100,
    hrot_0000100101,
    hrot_0000100110,
    hrot_0000100111,
    hrot_0000101000,
    hrot_0000101001,
    hrot_0000101010,
    hrot_0000101011,
    hrot_0000101100,
    hrot_0000101101,
    hrot_0000101110,
    hrot_0000101111,
    hrot_0000110000,
    hrot_0000110001,
    hrot_0000110010,
    hrot_0000110011,
    hrot_0000110100,
    hrot_0000110101,
    hrot_0000110110,
    hrot_0000110111,
    hrot_0000111000,
    hrot_0000111001,
    hrot_0000111010,
    hrot_0000111011,
    hrot_0000111100,
    hrot_0000111101,
    hrot_0000111110,
    hrot_0000111111,
    hrot_0001000000,
    hrot_0001000010,
    hrot_0001000011,
    hrot_0001000100,
    hrot_0001000101,
    hrot_0001000110,
    hrot_0001000111,
    hrot_0001001000,
    hrot_0001001001,
    hrot_0001001010,
    hrot_0001001011,
    hrot_0001001100,
    hrot_0001001101,
    hrot_0001001110,
    hrot_0001001111,
    hrot_0001010000,
    hrot_0001010001,
    hrot_0001010010,
    hrot_0001010011,
    hrot_0001010100,
    hrot_0001010101,
    hrot_0001010110,
    hrot_0001010111,
    hrot_0001011000,
    hrot_0001011001,
    hrot_0001011010,
    hrot_0001011011,
    hrot_0001011100,
    hrot_0001011101,
    hrot_0001011110,
    hrot_0001011111,
    hrot_0001100000,
    hrot_0001100001,
    hrot_0001100010,
    hrot_0001100011,
    hrot_0001100100,
    hrot_0001100101,
    hrot_0001100110,
    hrot_0001100111,
    hrot_0001101000,
    hrot_0001101001,
    hrot_0001101010,
    hrot_0001101011,
    hrot_0001101100,
    hrot_0001101101,
    hrot_0001101110,
    hrot_0001101111,
    hrot_0001110000,
    hrot_0001110001,
    hrot_0001110010,
    hrot_0001110011,
    hrot_0001110100,
    hrot_0001110101,
    hrot_0001110110,
    hrot_0001110111,
    hrot_0001111000,
    hrot_0001111001,
    hrot_0001111010,
    hrot_0001111011,
    hrot_0001111100,
    hrot_0001111101,
    hrot_0001111110,
    hrot_0001111111,
    hrot_0010000000,
    hrot_0010000010,
    hrot_0010000011,
    hrot_0010000100,
    hrot_0010000101,
    hrot_0010000110,
    hrot_0010000111,
    hrot_0010001000,
    hrot_0010001001,
    hrot_0010001010,
    hrot_0010001011,
    hrot_0010001100,
    hrot_0010001101,
    hrot_0010001110,
    hrot_0010001111,
    hrot_0010010000,
    hrot_0010010010,
    hrot_0010010011,
    hrot_0010010100,
    hrot_0010010101,
    hrot_0010010110,
    hrot_0010010111,
    hrot_0010011000,
    hrot_0010011001,
    hrot_0010011010,
    hrot_0010011011,
    hrot_0010011100,
    hrot_0010011101,
    hrot_0010011110,
    hrot_0010011111,
    hrot_0010100000,
    hrot_0010100001,
    hrot_0010100010,
    hrot_0010100011,
    hrot_0010100100,
    hrot_0010100101,
    hrot_0010100110,
    hrot_0010100111,
    hrot_0010101000,
    hrot_0010101001,
    hrot_0010101010,
    hrot_0010101011,
    hrot_0010101100,
    hrot_0010101101,
    hrot_0010101110,
    hrot_0010101111,
    hrot_0010110000,
    hrot_0010110001,
    hrot_0010110010,
    hrot_0010110011,
    hrot_0010110100,
    hrot_0010110101,
    hrot_0010110110,
    hrot_0010110111,
    hrot_0010111000,
    hrot_0010111001,
    hrot_0010111010,
    hrot_0010111011,
    hrot_0010111100,
    hrot_0010111101,
    hrot_0010111110,
    hrot_0010111111,
    hrot_0011000000,
    hrot_0011000001,
    hrot_0011000010,
    hrot_0011000011,
    hrot_0011000100,
    hrot_0011000101,
    hrot_0011000110,
    hrot_0011000111,
    hrot_0011001000,
    hrot_0011001001,
    hrot_0011001010,
    hrot_0011001011,
    hrot_0011001100,
    hrot_0011001101,
    hrot_0011001110,
    hrot_0011001111,
    hrot_0011010000,
    hrot_0011010001,
    hrot_0011010010,
    hrot_0011010011,
    hrot_0011010100,
    hrot_0011010101,
    hrot_0011010110,
    hrot_0011010111,
    hrot_0011011000,
    hrot_0011011001,
    hrot_0011011010,
    hrot_0011011011,
    hrot_0011011100,
    hrot_0011011101,
    hrot_0011011110,
    hrot_0011011111,
    hrot_0011100000,
    hrot_0011100001,
    hrot_0011100010,
    hrot_0011100011,
    hrot_0011100100,
    hrot_0011100101,
    hrot_0011100110,
    hrot_0011100111,
    hrot_0011101000,
    hrot_0011101001,
    hrot_0011101010,
    hrot_0011101011,
    hrot_0011101100,
    hrot_0011101101,
    hrot_0011101110,
    hrot_0011101111,
    hrot_0011110000,
    hrot_0011110001,
    hrot_0011110010,
    hrot_0011110011,
    hrot_0011110100,
    hrot_0011110101,
    hrot_0011110110,
    hrot_0011110111,
    hrot_0011111000,
    hrot_0011111001,
    hrot_0011111010,
    hrot_0011111011,
    hrot_0011111100,
    hrot_0011111101,
    hrot_0011111110,
    hrot_0011111111,
    hrot_0100000000,
    hrot_0100000010,
    hrot_0100000011,
    hrot_0100000100,
    hrot_0100000101,
    hrot_0100000110,
    hrot_0100000111,
    hrot_0100001000,
    hrot_0100001010,
    hrot_0100001011,
    hrot_0100001100,
    hrot_0100001101,
    hrot_0100001110,
    hrot_0100001111,
    hrot_0100010000,
    hrot_0100010010,
    hrot_0100010011,
    hrot_0100010100,
    hrot_0100010101,
    hrot_0100010110,
    hrot_0100010111,
    hrot_0100011000,
    hrot_0100011001,
    hrot_0100011010,
    hrot_0100011011,
    hrot_0100011100,
    hrot_0100011101,
    hrot_0100011110,
    hrot_0100011111,
    hrot_0100100000,
    hrot_0100100010,
    hrot_0100100011,
    hrot_0100100100,
    hrot_0100100101,
    hrot_0100100110,
    hrot_0100100111,
    hrot_0100101000,
    hrot_0100101010,
    hrot_0100101011,
    hrot_0100101100,
    hrot_0100101101,
    hrot_0100101110,
    hrot_0100101111,
    hrot_0100110000,
    hrot_0100110001,
    hrot_0100110010,
    hrot_0100110011,
    hrot_0100110100,
    hrot_0100110101,
    hrot_0100110110,
    hrot_0100110111,
    hrot_0100111000,
    hrot_0100111001,
    hrot_0100111010,
    hrot_0100111011,
    hrot_0100111100,
    hrot_0100111101,
    hrot_0100111110,
    hrot_0100111111,
    hrot_0101000000,
    hrot_0101000010,
    hrot_0101000011,
    hrot_0101000100,
    hrot_0101000101,
    hrot_0101000110,
    hrot_0101000111,
    hrot_0101001000,
    hrot_0101001010,
    hrot_0101001011,
    hrot_0101001100,
    hrot_0101001101,
    hrot_0101001110,
    hrot_0101001111,
    hrot_0101010000,
    hrot_0101010010,
    hrot_0101010011,
    hrot_0101010100,
    hrot_0101010110,
    hrot_0101010111,
    hrot_0101011000,
    hrot_0101011001,
    hrot_0101011010,
    hrot_0101011011,
    hrot_0101011100,
    hrot_0101011101,
    hrot_0101011110,
    hrot_0101011111,
    hrot_0101100000,
    hrot_0101100001,
    hrot_0101100010,
    hrot_0101100011,
    hrot_0101100100,
    hrot_0101100101,
    hrot_0101100110,
    hrot_0101100111,
    hrot_0101101000,
    hrot_0101101001,
    hrot_0101101010,
    hrot_0101101011,
    hrot_0101101100,
    hrot_0101101101,
    hrot_0101101110,
    hrot_0101101111,
    hrot_0101110000,
    hrot_0101110001,
    hrot_0101110010,
    hrot_0101110011,
    hrot_0101110100,
    hrot_0101110101,
    hrot_0101110110,
    hrot_0101110111,
    hrot_0101111000,
    hrot_0101111001,
    hrot_0101111010,
    hrot_0101111011,
    hrot_0101111100,
    hrot_0101111101,
    hrot_0101111110,
    hrot_0101111111,
    hrot_0110000000,
    hrot_0110000001,
    hrot_0110000010,
    hrot_0110000011,
    hrot_0110000100,
    hrot_0110000101,
    hrot_0110000110,
    hrot_0110000111,
    hrot_0110001000,
    hrot_0110001001,
    hrot_0110001010,
    hrot_0110001011,
    hrot_0110001100,
    hrot_0110001101,
    hrot_0110001110,
    hrot_0110001111,
    hrot_0110010000,
    hrot_0110010001,
    hrot_0110010010,
    hrot_0110010011,
    hrot_0110010100,
    hrot_0110010101,
    hrot_0110010110,
    hrot_0110010111,
    hrot_0110011000,
    hrot_0110011001,
    hrot_0110011010,
    hrot_0110011011,
    hrot_0110011100,
    hrot_0110011101,
    hrot_0110011110,
    hrot_0110011111,
    hrot_0110100000,
    hrot_0110100001,
    hrot_0110100010,
    hrot_0110100011,
    hrot_0110100100,
    hrot_0110100101,
    hrot_0110100110,
    hrot_0110100111,
    hrot_0110101000,
    hrot_0110101001,
    hrot_0110101010,
    hrot_0110101011,
    hrot_0110101100,
    hrot_0110101101,
    hrot_0110101110,
    hrot_0110101111,
    hrot_0110110000,
    hrot_0110110001,
    hrot_0110110010,
    hrot_0110110011,
    hrot_0110110100,
    hrot_0110110101,
    hrot_0110110110,
    hrot_0110110111,
    hrot_0110111000,
    hrot_0110111001,
    hrot_0110111010,
    hrot_0110111011,
    hrot_0110111100,
    hrot_0110111101,
    hrot_0110111110,
    hrot_0110111111,
    hrot_0111000000,
    hrot_0111000001,
    hrot_0111000010,
    hrot_0111000011,
    hrot_0111000100,
    hrot_0111000101,
    hrot_0111000110,
    hrot_0111000111,
    hrot_0111001000,
    hrot_0111001001,
    hrot_0111001010,
    hrot_0111001011,
    hrot_0111001100,
    hrot_0111001101,
    hrot_0111001110,
    hrot_0111001111,
    hrot_0111010000,
    hrot_0111010001,
    hrot_0111010010,
    hrot_0111010011,
    hrot_0111010100,
    hrot_0111010101,
    hrot_0111010110,
    hrot_0111010111,
    hrot_0111011000,
    hrot_0111011001,
    hrot_0111011010,
    hrot_0111011011,
    hrot_0111011100,
    hrot_0111011101,
    hrot_0111011110,
    hrot_0111011111,
    hrot_0111100000,
    hrot_0111100001,
    hrot_0111100010,
    hrot_0111100011,
    hrot_0111100100,
    hrot_0111100101,
    hrot_0111100110,
    hrot_0111100111,
    hrot_0111101000,
    hrot_0111101001,
    hrot_0111101010,
    hrot_0111101011,
    hrot_0111101100,
    hrot_0111101101,
    hrot_0111101110,
    hrot_0111101111,
    hrot_0111110000,
    hrot_0111110001,
    hrot_0111110010,
    hrot_0111110011,
    hrot_0111110100,
    hrot_0111110101,
    hrot_0111110110,
    hrot_0111110111,
    hrot_0111111000,
    hrot_0111111001,
    hrot_0111111010,
    hrot_0111111011,
    hrot_0111111100,
    hrot_0111111101,
    hrot_0111111110,
    hrot_0111111111,
    hrot_1000000000,
    hrot_1000000010,
    hrot_1000000011,
    hrot_1000000100,
    hrot_1000000110,
    hrot_1000000111,
    hrot_1000001000,
    hrot_1000001010,
    hrot_1000001011,
    hrot_1000001100,
    hrot_1000001101,
    hrot_1000001110,
    hrot_1000001111,
    hrot_1000010000,
    hrot_1000010010,
    hrot_1000010011,
    hrot_1000010100,
    hrot_1000010110,
    hrot_1000010111,
    hrot_1000011000,
    hrot_1000011001,
    hrot_1000011010,
    hrot_1000011011,
    hrot_1000011100,
    hrot_1000011101,
    hrot_1000011110,
    hrot_1000011111,
    hrot_1000100000,
    hrot_1000100010,
    hrot_1000100011,
    hrot_1000100100,
    hrot_1000100110,
    hrot_1000100111,
    hrot_1000101000,
    hrot_1000101010,
    hrot_1000101011,
    hrot_1000101100,
    hrot_1000101101,
    hrot_1000101110,
    hrot_1000101111,
    hrot_1000110000,
    hrot_1000110010,
    hrot_1000110011,
    hrot_1000110100,
    hrot_1000110101,
    hrot_1000110110,
    hrot_1000110111,
    hrot_1000111000,
    hrot_1000111001,
    hrot_1000111010,
    hrot_1000111011,
    hrot_1000111100,
    hrot_1000111101,
    hrot_1000111110,
    hrot_1000111111,
    hrot_1001000000,
    hrot_1001000010,
    hrot_1001000011,
    hrot_1001000100,
    hrot_1001000110,
    hrot_1001000111,
    hrot_1001001000,
    hrot_1001001010,
    hrot_1001001011,
    hrot_1001001100,
    hrot_1001001101,
    hrot_1001001110,
    hrot_1001001111,
    hrot_1001010000,
    hrot_1001010010,
    hrot_1001010011,
    hrot_1001010100,
    hrot_1001010110,
    hrot_1001010111,
    hrot_1001011000,
    hrot_1001011001,
    hrot_1001011010,
    hrot_1001011011,
    hrot_1001011100,
    hrot_1001011101,
    hrot_1001011110,
    hrot_1001011111,
    hrot_1001100000,
    hrot_1001100010,
    hrot_1001100011,
    hrot_1001100100,
    hrot_1001100110,
    hrot_1001100111,
    hrot_1001101000,
    hrot_1001101001,
    hrot_1001101010,
    hrot_1001101011,
    hrot_1001101100,
    hrot_1001101101,
    hrot_1001101110,
    hrot_1001101111,
    hrot_1001110000,
    hrot_1001110001,
    hrot_1001110010,
    hrot_1001110011,
    hrot_1001110100,
    hrot_1001110101,
    hrot_1001110110,
    hrot_1001110111,
    hrot_1001111000,
    hrot_1001111001,
    hrot_1001111010,
    hrot_1001111011,
    hrot_1001111100,
    hrot_1001111101,
    hrot_1001111110,
    hrot_1001111111,
    hrot_1010000000,
    hrot_1010000010,
    hrot_1010000011,
    hrot_1010000100,
    hrot_1010000110,
    hrot_1010000111,
    hrot_1010001000,
    hrot_1010001010,
    hrot_1010001011,
    hrot_1010001100,
    hrot_1010001101,
    hrot_1010001110,
    hrot_1010001111,
    hrot_1010010000,
    hrot_1010010010,
    hrot_1010010011,
    hrot_1010010100,
    hrot_1010010110,
    hrot_1010010111,
    hrot_1010011000,
    hrot_1010011010,
    hrot_1010011011,
    hrot_1010011100,
    hrot_1010011101,
    hrot_1010011110,
    hrot_1010011111,
    hrot_1010100000,
    hrot_1010100010,
    hrot_1010100011,
    hrot_1010100100,
    hrot_1010100110,
    hrot_1010100111,
    hrot_1010101000,
    hrot_1010101010,
    hrot_1010101011,
    hrot_1010101100,
    hrot_1010101101,
    hrot_1010101110,
    hrot_1010101111,
    hrot_1010110000,
    hrot_1010110010,
    hrot_1010110011,
    hrot_1010110100,
    hrot_1010110110,
    hrot_1010110111,
    hrot_1010111000,
    hrot_1010111001,
    hrot_1010111010,
    hrot_1010111011,
    hrot_1010111100,
    hrot_1010111101,
    hrot_1010111110,
    hrot_1010111111,
    hrot_1011000000,
    hrot_1011000010,
    hrot_1011000011,
    hrot_1011000100,
    hrot_1011000110,
    hrot_1011000111,
    hrot_1011001000,
    hrot_1011001010,
    hrot_1011001011,
    hrot_1011001100,
    hrot_1011001101,
    hrot_1011001110,
    hrot_1011001111,
    hrot_1011010000,
    hrot_1011010010,
    hrot_1011010011,
    hrot_1011010100,
    hrot_1011010110,
    hrot_1011010111,
    hrot_1011011000,
    hrot_1011011010,
    hrot_1011011011,
    hrot_1011011100,
    hrot_1011011101,
    hrot_1011011110,
    hrot_1011011111,
    hrot_1011100000,
    hrot_1011100001,
    hrot_1011100010,
    hrot_1011100011,
    hrot_1011100100,
    hrot_1011100101,
    hrot_1011100110,
    hrot_1011100111,
    hrot_1011101000,
    hrot_1011101001,
    hrot_1011101010,
    hrot_1011101011,
    hrot_1011101100,
    hrot_1011101101,
    hrot_1011101110,
    hrot_1011101111,
    hrot_1011110000,
    hrot_1011110001,
    hrot_1011110010,
    hrot_1011110011,
    hrot_1011110100,
    hrot_1011110101,
    hrot_1011110110,
    hrot_1011110111,
    hrot_1011111000,
    hrot_1011111001,
    hrot_1011111010,
    hrot_1011111011,
    hrot_1011111100,
    hrot_1011111101,
    hrot_1011111110,
    hrot_1011111111,
    hrot_1100000000,
    hrot_1100000010,
    hrot_1100000011,
    hrot_1100000100,
    hrot_1100000110,
    hrot_1100000111,
    hrot_1100001000,
    hrot_1100001010,
    hrot_1100001011,
    hrot_1100001100,
    hrot_1100001110,
    hrot_1100001111,
    hrot_1100010000,
    hrot_1100010010,
    hrot_1100010011,
    hrot_1100010100,
    hrot_1100010110,
    hrot_1100010111,
    hrot_1100011000,
    hrot_1100011010,
    hrot_1100011011,
    hrot_1100011100,
    hrot_1100011101,
    hrot_1100011110,
    hrot_1100011111,
    hrot_1100100000,
    hrot_1100100010,
    hrot_1100100011,
    hrot_1100100100,
    hrot_1100100110,
    hrot_1100100111,
    hrot_1100101000,
    hrot_1100101010,
    hrot_1100101011,
    hrot_1100101100,
    hrot_1100101110,
    hrot_1100101111,
    hrot_1100110000,
    hrot_1100110010,
    hrot_1100110011,
    hrot_1100110100,
    hrot_1100110110,
    hrot_1100110111,
    hrot_1100111000,
    hrot_1100111010,
    hrot_1100111011,
    hrot_1100111100,
    hrot_1100111101,
    hrot_1100111110,
    hrot_1100111111,
    hrot_1101000000,
    hrot_1101000010,
    hrot_1101000011,
    hrot_1101000100,
    hrot_1101000110,
    hrot_1101000111,
    hrot_1101001000,
    hrot_1101001010,
    hrot_1101001011,
    hrot_1101001100,
    hrot_1101001110,
    hrot_1101001111,
    hrot_1101010000,
    hrot_1101010010,
    hrot_1101010011,
    hrot_1101010100,
    hrot_1101010110,
    hrot_1101010111,
    hrot_1101011000,
    hrot_1101011010,
    hrot_1101011011,
    hrot_1101011100,
    hrot_1101011101,
    hrot_1101011110,
    hrot_1101011111,
    hrot_1101100000,
    hrot_1101100010,
    hrot_1101100011,
    hrot_1101100100,
    hrot_1101100110,
    hrot_1101100111,
    hrot_1101101000,
    hrot_1101101010,
    hrot_1101101011,
    hrot_1101101100,
    hrot_1101101110,
    hrot_1101101111,
    hrot_1101110000,
    hrot_1101110010,
    hrot_1101110011,
    hrot_1101110100,
    hrot_1101110110,
    hrot_1101110111,
    hrot_1101111000,
    hrot_1101111001,
    hrot_1101111010,
    hrot_1101111011,
    hrot_1101111100,
    hrot_1101111101,
    hrot_1101111110,
    hrot_1101111111,
    hrot_1110000000,
    hrot_1110000010,
    hrot_1110000011,
    hrot_1110000100,
    hrot_1110000110,
    hrot_1110000111,
    hrot_1110001000,
    hrot_1110001010,
    hrot_1110001011,
    hrot_1110001100,
    hrot_1110001110,
    hrot_1110001111,
    hrot_1110010000,
    hrot_1110010010,
    hrot_1110010011,
    hrot_1110010100,
    hrot_1110010110,
    hrot_1110010111,
    hrot_1110011000,
    hrot_1110011010,
    hrot_1110011011,
    hrot_1110011100,
    hrot_1110011110,
    hrot_1110011111,
    hrot_1110100000,
    hrot_1110100010,
    hrot_1110100011,
    hrot_1110100100,
    hrot_1110100110,
    hrot_1110100111,
    hrot_1110101000,
    hrot_1110101010,
    hrot_1110101011,
    hrot_1110101100,
    hrot_1110101110,
    hrot_1110101111,
    hrot_1110110000,
    hrot_1110110010,
    hrot_1110110011,
    hrot_1110110100,
    hrot_1110110110,
    hrot_1110110111,
    hrot_1110111000,
    hrot_1110111010,
    hrot_1110111011,
    hrot_1110111100,
    hrot_1110111110,
    hrot_1110111111,
    hrot_1111000000,
    hrot_1111000010,
    hrot_1111000011,
    hrot_1111000100,
    hrot_1111000110,
    hrot_1111000111,
    hrot_1111001000,
    hrot_1111001010,
    hrot_1111001011,
    hrot_1111001100,
    hrot_1111001110,
    hrot_1111001111,
    hrot_1111010000,
    hrot_1111010010,
    hrot_1111010011,
    hrot_1111010100,
    hrot_1111010110,
    hrot_1111010111,
    hrot_1111011000,
    hrot_1111011010,
    hrot_1111011011,
    hrot_1111011100,
    hrot_1111011110,
    hrot_1111011111,
    hrot_1111100000,
    hrot_1111100010,
    hrot_1111100011,
    hrot_1111100100,
    hrot_1111100110,
    hrot_1111100111,
    hrot_1111101000,
    hrot_1111101010,
    hrot_1111101011,
    hrot_1111101100,
    hrot_1111101110,
    hrot_1111101111,
    hrot_1111110000,
    hrot_1111110010,
    hrot_1111110011,
    hrot_1111110100,
    hrot_1111110110,
    hrot_1111110111,
    hrot_1111111000,
    hrot_1111111010,
    hrot_1111111011,
    hrot_1111111100,
    hrot_1111111110
  ]
  ring

end EvgenyTheorem
