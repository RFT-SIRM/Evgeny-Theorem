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
  simpa using (add_comm (Matrix.trace xs.reverse.prod) (Matrix.trace xs.prod))

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
