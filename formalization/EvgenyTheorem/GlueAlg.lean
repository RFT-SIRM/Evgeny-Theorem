import EvgenyTheorem.TraceExpand

namespace EvgenyTheorem

open Matrix

section GlueAlg

variable {W ι : Type*} [Fintype W] [DecidableEq W] [DecidableEq ι]

/-- Pairing of "glued" points: `g` marks glued points, `σ` is the partner map. -/
structure GlueData (cp : W → ι) where
  g : W → Prop
  dg : DecidablePred g
  σ : W → W
  g_σ : ∀ w, g w → g (σ w)
  σσ : ∀ w, g w → σ (σ w) = w
  cp_σ : ∀ w, g w → cp (σ w) ≠ cp w

/-- `X` has vanishing entries between two distinct glued points that lie in the same copy and
whose partners also lie in a common copy. (Replaces the former field `uniq`, which is false when
the index also carries the two spin components of one point.) -/
def GlueDiag {cp : W → ι} (G : GlueData cp) (X : Matrix W W ℂ) : Prop :=
  ∀ w w', G.g w → G.g w' → cp w = cp w' → cp (G.σ w) = cp (G.σ w') → w ≠ w' → X w w' = 0

attribute [instance] GlueData.dg


/-- A partner involution on the glued locus lets us exchange the two factors
in a boundary sum. Unlike a permutation of all of W, this uses only the
involution law actually provided by GlueData. -/
theorem glued_sum_partner_product_swap {cp : W → ι} (G : GlueData cp)
    (f h : W → ℂ) :
    (∑ x : {w // G.g w}, f x.1 * h (G.σ x.1)) =
      ∑ x : {w // G.g w}, h x.1 * f (G.σ x.1) := by
  let e : Equiv.Perm {w // G.g w} :=
    { toFun := fun x => ⟨G.σ x.1, G.g_σ x.1 x.2⟩
      invFun := fun x => ⟨G.σ x.1, G.g_σ x.1 x.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact G.σσ x.1 x.2
      right_inv := by
        intro x
        apply Subtype.ext
        exact G.σσ x.1 x.2 }
  calc
    (∑ x : {w // G.g w}, f x.1 * h (G.σ x.1)) =
        ∑ x : {w // G.g w}, (fun y => f y.1 * h (G.σ y.1)) (e x) := by
          symm
          exact Equiv.sum_comp e (fun y => f y.1 * h (G.σ y.1))
    _ = ∑ x : {w // G.g w}, f (G.σ x.1) * h x.1 := by
          apply Finset.sum_congr rfl
          intro x hx
          change f (G.σ x.1) * h (G.σ (G.σ x.1)) =
            f (G.σ x.1) * h x.1
          rw [G.σσ x.1 x.2]
    _ = ∑ x : {w // G.g w}, h x.1 * f (G.σ x.1) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact mul_comm _ _

/-- The pairing matrix. -/
noncomputable def GlueData.N {cp : W → ι} (G : GlueData cp) : Matrix W W ℂ :=
  fun w a => if G.g w ∧ a = G.σ w then 1 else 0

/-- The pairing matrix is self-adjoint: the involution law for the partner map
makes its graph symmetric, and all nonzero entries are real. This is the
adjoint premise needed to reverse expanded K/N words by complex conjugation. -/
theorem GlueData.N_hermitian {cp : W → ι} (G : GlueData cp) :
    Matrix.conjTranspose G.N = G.N := by
  classical
  ext w a
  simp only [Matrix.conjTranspose_apply, GlueData.N]
  by_cases hright : G.g w ∧ a = G.σ w
  · rcases hright with ⟨hw, hwa⟩
    have ha : G.g a := by
      rw [hwa]
      exact G.g_σ w hw
    have haw : w = G.σ a := by
      rw [hwa]
      exact (G.σσ w hw).symm
    have hleft : G.g a ∧ w = G.σ a := ⟨ha, haw⟩
    have hright' : G.g w ∧ a = G.σ w := ⟨hw, hwa⟩
    simp only [if_pos hleft, if_pos hright', star_one]
  · have hleft : ¬ (G.g a ∧ w = G.σ a) := by
      rintro ⟨ha, haw⟩
      apply hright
      constructor
      · rw [haw]
        exact G.g_σ a ha
      · calc
          a = G.σ (G.σ a) := (G.σσ a ha).symm
          _ = G.σ w := by rw [haw]
    simp only [if_neg hleft, if_neg hright, star_zero]

/-- Block diagonality with respect to the copy map `cp`. -/
def BD (cp : W → ι) (M : Matrix W W ℂ) : Prop := ∀ w w', cp w ≠ cp w' → M w w' = 0

theorem BD_mul {cp : W → ι} {A B : Matrix W W ℂ} (hA : BD cp A) (hB : BD cp B) :
    BD cp (A * B) := by
  intro w w' h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun v _ => ?_)
  by_cases hv : cp w = cp v
  · have : cp v ≠ cp w' := fun h' => h (hv.trans h')
    rw [hB v w' this, mul_zero]
  · rw [hA w v hv, zero_mul]

theorem BD_diagonal {cp : W → ι} (κ : W → ℂ) : BD cp (Matrix.diagonal κ) := by
  intro w w' h
  have : w ≠ w' := fun e => h (by rw [e])
  simp [Matrix.diagonal_apply, this]

theorem N_mul {cp : W → ι} (G : GlueData cp) (M : Matrix W W ℂ) (a d : W) :
    (G.N * M) a d = if G.g a then M (G.σ a) d else 0 := by
  simp only [Matrix.mul_apply, GlueData.N]
  by_cases ha : G.g a
  · simp [ha]
  · simp [ha]

theorem mul_N {cp : W → ι} (G : GlueData cp) (M : Matrix W W ℂ) (a b : W) :
    (M * G.N) a b = if G.g b then M a (G.σ b) else 0 := by
  simp only [Matrix.mul_apply, GlueData.N]
  by_cases hb : G.g b
  · rw [if_pos hb, Finset.sum_eq_single (G.σ b)]
    · have h1 : G.g (G.σ b) := G.g_σ b hb
      have h2 : b = G.σ (G.σ b) := (G.σσ b hb).symm
      rw [if_pos ⟨h1, h2⟩, mul_one]
    · intro c _ hc
      have : ¬ (G.g c ∧ b = G.σ c) := by
        rintro ⟨hgc, hbc⟩
        apply hc
        rw [hbc, G.σσ c hgc]
      rw [if_neg this, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hb]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    have : ¬ (G.g c ∧ b = G.σ c) := by
      rintro ⟨hgc, hbc⟩
      apply hb
      rw [hbc]
      exact G.g_σ c hgc
    rw [if_neg this, mul_zero]

theorem trace_BD_N {cp : W → ι} (G : GlueData cp) {X : Matrix W W ℂ} (hX : BD cp X) :
    Matrix.trace (X * G.N) = 0 := by
  unfold Matrix.trace
  refine Finset.sum_eq_zero (fun w _ => ?_)
  simp only [Matrix.diag_apply]
  rw [mul_N]
  by_cases hw : G.g w
  · rw [if_pos hw]
    exact hX w (G.σ w) (fun h => G.cp_σ w hw h.symm)
  · rw [if_neg hw]

/-- A finite product of matrices that are block diagonal across the copy map
remains block diagonal. The factors need not be equal or commute. -/
theorem BD_list_prod {cp : W → ι} (xs : List (Matrix W W ℂ))
    (hxs : ∀ M, M ∈ xs → BD cp M) : BD cp xs.prod := by
  induction xs with
  | nil =>
      intro w w' h
      have hne : w ≠ w' := fun e => h (congrArg cp e)
      simp [Matrix.one_apply, hne]
  | cons A xs ih =>
      change BD cp (A * xs.prod)
      apply BD_mul
      · exact hxs A (by simp)
      · apply ih
        intro M hM
        exact hxs M (by simp [hM])

/-- Any ordered finite product of block-diagonal factors has zero trace after
multiplication by the pairing matrix. This generalizes the power-only case:
the block-diagonal factors may all be different. -/
theorem trace_list_prod_mul_N_zero {cp : W → ι} (G : GlueData cp)
    (xs : List (Matrix W W ℂ))
    (hxs : ∀ M, M ∈ xs → BD cp M) :
    Matrix.trace (xs.prod * G.N) = 0 := by
  exact trace_BD_N G (BD_list_prod xs hxs)

/-- The same vanishing holds when the pairing matrix occurs at the left
edge of the trace: cyclicity moves it to the right edge. -/
theorem trace_N_mul_list_prod_zero {cp : W → ι} (G : GlueData cp)
    (xs : List (Matrix W W ℂ))
    (hxs : ∀ M, M ∈ xs → BD cp M) :
    Matrix.trace (G.N * xs.prod) = 0 := by
  rw [Matrix.trace_mul_comm]
  exact trace_list_prod_mul_N_zero G xs hxs

/-- Block diagonality is preserved by every natural power. -/
theorem BD_pow {cp : W → ι} (K : Matrix W W ℂ) (hK : BD cp K) (n : ℕ) :
    BD cp (K ^ n) := by
  induction n with
  | zero =>
      intro w w' h
      have hne : w ≠ w' := fun e => h (congrArg cp e)
      simp [Matrix.one_apply, hne]
  | succ n ih =>
      simpa [pow_succ] using BD_mul ih hK

/-- The trace contribution of a single pairing factor vanishes after any natural power
of a matrix that is block diagonal across the copy map. -/
theorem trace_pow_mul_N_zero {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K) (n : ℕ) :
    Matrix.trace (K ^ n * G.N) = 0 := by
  exact trace_BD_N G (BD_pow K hK n)

/-- A single pairing factor vanishes in the trace even when block-diagonal
powers of K occur on both sides. Cyclicity moves the right-hand power next
to the left-hand power, after which they combine into one power. -/
theorem trace_pow_N_pow_zero {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K) (a b : ℕ) :
    Matrix.trace (K ^ a * G.N * K ^ b) = 0 := by
  calc
    Matrix.trace ((K ^ a * G.N) * K ^ b) =
        Matrix.trace (K ^ b * (K ^ a * G.N)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((K ^ b * K ^ a) * G.N) := by
      rw [← Matrix.mul_assoc]
    _ = Matrix.trace (K ^ (b + a) * G.N) := by
      rw [← pow_add]
    _ = 0 := trace_pow_mul_N_zero G K hK (b + a)

/-- A word with exactly one factor of the form `K * N` vanishes under
the trace when the remaining factors are powers of a block-diagonal `K`.
This is the single-pairing stratum needed when expanding `(K + K*N)^p`. -/
theorem trace_single_KN_word_zero {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K) (a b : ℕ) :
    Matrix.trace (K ^ a * (K * G.N) * K ^ b) = 0 := by
  calc
    Matrix.trace (K ^ a * (K * G.N) * K ^ b) =
        Matrix.trace (K ^ (a + 1) * G.N * K ^ b) := by
      rw [pow_succ]
      simp only [Matrix.mul_assoc]
    _ = 0 := trace_pow_N_pow_zero G K hK (a + 1) b

/-- In a trace word with exactly one pairing factor N, its position is irrelevant:
if every other factor is block diagonal across copies, cyclicity gathers those
factors into one block-diagonal product and the trace vanishes. -/
theorem trace_one_N_between_products_zero {cp : W → ι} (G : GlueData cp)
    (xs ys : List (Matrix W W ℂ))
    (hxs : ∀ M, M ∈ xs → BD cp M)
    (hys : ∀ M, M ∈ ys → BD cp M) :
    Matrix.trace (xs.prod * G.N * ys.prod) = 0 := by
  calc
    Matrix.trace ((xs.prod * G.N) * ys.prod) =
        Matrix.trace (ys.prod * (xs.prod * G.N)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((ys.prod * xs.prod) * G.N) := by
      rw [← Matrix.mul_assoc]
    _ = Matrix.trace ((ys ++ xs).prod * G.N) := by
      rw [List.prod_append]
    _ = 0 := by
      apply trace_list_prod_mul_N_zero G (ys ++ xs)
      intro M hM
      simp only [List.mem_append] at hM
      rcases hM with hM | hM
      · exact hys M hM
      · exact hxs M hM

theorem Q_apply {cp : W → ι} (G : GlueData cp) (K : Matrix W W ℂ) (hbd : BD cp K)
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → K w w' = 0) (a b : W) :
    (G.N * K * G.N) a b = if G.g a ∧ a = b then K (G.σ a) (G.σ a) else 0 := by
  rw [mul_N, N_mul]
  by_cases hb : G.g b
  · rw [if_pos hb]
    by_cases ha : G.g a
    · rw [if_pos ha]
      by_cases hab : a = b
      · subst hab
        simp [ha]
      · rw [if_neg (fun h => hab h.2)]
        have hne : G.σ a ≠ G.σ b := fun h => hab (by
          rw [← G.σσ a ha, ← G.σσ b hb, h])
        by_cases hc : cp (G.σ a) = cp (G.σ b)
        · exact hkg _ _ (G.g_σ a ha) (G.g_σ b hb) hc hne
        · exact hbd _ _ hc
    · rw [if_neg ha, if_neg (fun h => ha h.1)]
  · rw [if_neg hb, if_neg (show ¬ (G.g a ∧ a = b) from fun h => hb (h.2 ▸ h.1))]

theorem Q_eq_diag {cp : W → ι} (G : GlueData cp) (K : Matrix W W ℂ) (hbd : BD cp K)
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → K w w' = 0) :
    G.N * K * G.N =
      Matrix.diagonal (fun a => if G.g a then K (G.σ a) (G.σ a) else 0) := by
  ext a b
  rw [Q_apply G K hbd hkg, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : G.g a <;> simp [ha]
  · rw [if_neg (fun h => hab h.2), if_neg hab]

theorem trace_mul_Q {cp : W → ι} (G : GlueData cp) (K : Matrix W W ℂ) (hbd : BD cp K)
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → K w w' = 0)
    (X : Matrix W W ℂ) :
    Matrix.trace (X * (G.N * K * G.N)) =
      ∑ a, if G.g a then X a a * K (G.σ a) (G.σ a) else 0 := by
  rw [Q_eq_diag G K hbd hkg]
  unfold Matrix.trace
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Matrix.diag_apply, Matrix.mul_diagonal]
  by_cases ha : G.g a <;> simp [ha]

/-- General two-pairing trace formula. The middle factor may be any matrix M,
provided it is block diagonal and satisfies the required glued-corner vanishing.
This isolates the boundary contribution of a word with exactly two N factors. -/
theorem trace_two_N {cp : W → ι} (G : GlueData cp)
    (M X : Matrix W W ℂ) (hbd : BD cp M)
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → M w w' = 0) :
    Matrix.trace (X * (G.N * M * G.N)) =
      ∑ a, if G.g a then X a a * M (G.σ a) (G.σ a) else 0 := by
  exact trace_mul_Q G M hbd hkg X

/-- Two-pairing formula for an arbitrary ordered word: the factors before and
after the two N's are arbitrary finite products of block-diagonal matrices.
Cyclicity combines the outside factors in their correct order; no commutation
of individual factors is assumed. -/
theorem trace_two_N_word {cp : W → ι} (G : GlueData cp)
    (xs ys : List (Matrix W W ℂ)) (M : Matrix W W ℂ)
    (hbd : BD cp M)
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → M w w' = 0) :
    Matrix.trace (xs.prod * G.N * M * G.N * ys.prod) =
      ∑ a, if G.g a then ((ys ++ xs).prod) a a * M (G.σ a) (G.σ a) else 0 := by
  calc
    Matrix.trace (xs.prod * G.N * M * G.N * ys.prod) =
        Matrix.trace ((xs.prod * G.N * M * G.N) * ys.prod) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (ys.prod * (xs.prod * G.N * M * G.N)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((ys.prod * xs.prod) * (G.N * M * G.N)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((ys ++ xs).prod * (G.N * M * G.N)) := by
      rw [List.prod_append]
    _ = ∑ a, if G.g a then ((ys ++ xs).prod) a a * M (G.σ a) (G.σ a) else 0 := by
      exact trace_two_N G M ((ys ++ xs).prod) hbd hkg

/-- Derive the glued-corner vanishing condition when partner copies coincide.
For partner points in different copies, the required vanishing is supplied
explicitly as a separate hypothesis. -/
theorem GlueDiag_pair_vanish {cp : W → ι} (G : GlueData cp)
    (M : Matrix W W ℂ) (hdiag : GlueDiag G M)
    (hcross : ∀ w w', G.g w → G.g w' → cp w = cp w' →
      cp (G.σ w) ≠ cp (G.σ w') → w ≠ w' → M w w' = 0) :
    ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → M w w' = 0 := by
  intro w w' hw hw' hcopy hne
  by_cases hpartner : cp (G.σ w) = cp (G.σ w')
  · exact hdiag w w' hw hw' hcopy hpartner hne
  · exact hcross w w' hw hw' hcopy hpartner hne

/-- Two-pairing word formula for arbitrary natural powers of K. The geometric
condition is stated explicitly for the middle power; it is not inferred merely
from block diagonality of K. -/
theorem trace_two_N_powers {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (a b c : ℕ) (hbd : BD cp (K ^ b))
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ b) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c) =
      ∑ x, if G.g x then (K ^ c * K ^ a) x x * (K ^ b) (G.σ x) (G.σ x) else 0 := by
  calc
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c) =
        Matrix.trace ((K ^ a * G.N * K ^ b * G.N) * K ^ c) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (K ^ c * (K ^ a * G.N * K ^ b * G.N)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((K ^ c * K ^ a) * (G.N * K ^ b * G.N)) := by
      simp only [Matrix.mul_assoc]
    _ = ∑ x, if G.g x then (K ^ c * K ^ a) x x * (K ^ b) (G.σ x) (G.σ x) else 0 :=
      trace_two_N G (K ^ b) (K ^ c * K ^ a) hbd hkg

/-- Convenient specialization of `trace_two_N_powers`: block diagonality of the
middle power is derived from block diagonality of K, so callers need only provide
the separate glued-corner vanishing condition for that power. -/
theorem trace_two_N_powers_of_BD {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K) (a b c : ℕ)
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ b) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c) =
      ∑ x, if G.g x then (K ^ c * K ^ a) x x * (K ^ b) (G.σ x) (G.σ x) else 0 := by
  exact trace_two_N_powers G K a b c (BD_pow K hK b) hkg

/-- Two-pairing formula with the middle corner condition discharged by
`GlueDiag` on the middle power and an explicit cross-copy hypothesis.
This is the convenient interface for applications to powers of K. -/
theorem trace_two_N_powers_of_GlueDiag {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K) (a b c : ℕ)
    (hdiag : GlueDiag G (K ^ b))
    (hcross : ∀ w w', G.g w → G.g w' → cp w = cp w' →
      cp (G.σ w) ≠ cp (G.σ w') → w ≠ w' → (K ^ b) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c) =
      ∑ x, if G.g x then (K ^ c * K ^ a) x x * (K ^ b) (G.σ x) (G.σ x) else 0 := by
  apply trace_two_N_powers_of_BD G K hK a b c
  exact GlueDiag_pair_vanish G (K ^ b) hdiag hcross

/-- A word with three pairing factors vanishes when the middle power satisfies
the explicit glued-corner vanishing condition. Pairing the first two N factors
produces a diagonal matrix; the remaining block-diagonal factors then leave one
N factor in the trace, which vanishes. -/
theorem trace_three_N_powers {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K) (a b c d : ℕ)
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ b) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N * K ^ d) = 0 := by
  have hbd : BD cp (K ^ b) := BD_pow K hK b
  have hQ : BD cp (G.N * K ^ b * G.N) := by
    rw [Q_eq_diag G (K ^ b) hbd hkg]
    exact BD_diagonal _
  have hrotate :
      Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N * K ^ d) =
        Matrix.trace ((K ^ d * K ^ a) * (G.N * K ^ b * G.N) * K ^ c * G.N) := by
    calc
      Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N * K ^ d) =
          Matrix.trace ((K ^ a * (G.N * K ^ b * G.N) * K ^ c * G.N) * K ^ d) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (K ^ d * (K ^ a * (G.N * K ^ b * G.N) * K ^ c * G.N)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((K ^ d * K ^ a) * (G.N * K ^ b * G.N) * K ^ c * G.N) := by
        simp only [Matrix.mul_assoc]
  rw [hrotate]
  have hprod : BD cp ((K ^ d * K ^ a) * (G.N * K ^ b * G.N) * K ^ c) := by
    apply BD_mul
    · apply BD_mul
      · exact BD_mul (BD_pow K hK d) (BD_pow K hK a)
      · exact hQ
    · exact BD_pow K hK c
  exact trace_BD_N G hprod



/-- General three-pairing reduction for an ordered word. The factors outside
the three displayed pairing matrices may be different block-diagonal matrices;
their order is preserved. If the middle factor M makes N*M*N diagonal, the
remaining single N forces the trace to vanish. This is a reusable list-level
lemma, not a claim that the required corner condition holds for every power
of K. -/
theorem trace_three_N_word_zero {cp : W → ι} (G : GlueData cp)
    (xs ys zs : List (Matrix W W ℂ)) (M : Matrix W W ℂ)
    (hxs : ∀ A, A ∈ xs → BD cp A)
    (hys : ∀ A, A ∈ ys → BD cp A)
    (hzs : ∀ A, A ∈ zs → BD cp A)
    (hMbd : BD cp M)
    (hMkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → M w w' = 0) :
    Matrix.trace (xs.prod * G.N * M * G.N * ys.prod * G.N * zs.prod) = 0 := by
  have hQ : BD cp (G.N * M * G.N) := by
    rw [Q_eq_diag G M hMbd hMkg]
    exact BD_diagonal _
  have hrotate :
      Matrix.trace (xs.prod * G.N * M * G.N * ys.prod * G.N * zs.prod) =
        Matrix.trace ((zs.prod * xs.prod) * (G.N * M * G.N) * ys.prod * G.N) := by
    calc
      Matrix.trace (xs.prod * G.N * M * G.N * ys.prod * G.N * zs.prod) =
          Matrix.trace ((xs.prod * (G.N * M * G.N) * ys.prod * G.N) * zs.prod) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (zs.prod * (xs.prod * (G.N * M * G.N) * ys.prod * G.N)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((zs.prod * xs.prod) * (G.N * M * G.N) * ys.prod * G.N) := by
        simp only [Matrix.mul_assoc]
  rw [hrotate]
  have hleft : BD cp (zs.prod * xs.prod) := BD_mul (BD_list_prod zs hzs) (BD_list_prod xs hxs)
  have hprod : BD cp ((zs.prod * xs.prod) * (G.N * M * G.N) * ys.prod) := by
    exact BD_mul (BD_mul hleft hQ) (BD_list_prod ys hys)
  exact trace_BD_N G hprod


/-- Five-pairing trace words vanish when two selected middle powers satisfy
the glued-corner condition. Pairing the first two N factors makes
`N * K^b * N` block diagonal; the remaining three N factors then vanish
by `trace_three_N_word_zero` using the independent corner condition for
`K^d`. No all-power corner assumption is hidden in this statement. -/
theorem trace_five_N_powers_zero {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K)
    (a b c d e f : ℕ)
    (hkg_b : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ b) w w' = 0)
    (hkg_d : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ d) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f) = 0 := by
  have hbd_b : BD cp (K ^ b) := BD_pow K hK b
  have hQ : BD cp (G.N * K ^ b * G.N) := by
    rw [Q_eq_diag G (K ^ b) hbd_b hkg_b]
    exact BD_diagonal _
  have hrotate :
      Matrix.trace (K ^ a * (G.N * K ^ b * G.N) * K ^ c *
          G.N * K ^ d * G.N * K ^ e * G.N * K ^ f) =
        Matrix.trace (G.N * K ^ d * G.N * K ^ e * G.N *
          (K ^ f * K ^ a * (G.N * K ^ b * G.N) * K ^ c)) := by
    calc
      Matrix.trace (K ^ a * (G.N * K ^ b * G.N) * K ^ c *
          G.N * K ^ d * G.N * K ^ e * G.N * K ^ f) =
          Matrix.trace ((K ^ a * (G.N * K ^ b * G.N) * K ^ c *
            G.N * K ^ d * G.N * K ^ e * G.N) * K ^ f) := by
              simp only [Matrix.mul_assoc]
      _ = Matrix.trace (K ^ f *
            (K ^ a * (G.N * K ^ b * G.N) * K ^ c *
              G.N * K ^ d * G.N * K ^ e * G.N)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((K ^ f * K ^ a * (G.N * K ^ b * G.N) * K ^ c) *
            (G.N * K ^ d * G.N * K ^ e * G.N)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((G.N * K ^ d * G.N * K ^ e * G.N) *
            (K ^ f * K ^ a * (G.N * K ^ b * G.N) * K ^ c) ) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace (G.N * K ^ d * G.N * K ^ e * G.N *
            (K ^ f * K ^ a * (G.N * K ^ b * G.N) * K ^ c)) := by
          simp only [Matrix.mul_assoc]
  rw [show K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f =
      K ^ a * (G.N * K ^ b * G.N) * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f by
        simp only [Matrix.mul_assoc]]
  rw [hrotate]
  have hxs : ∀ A, A ∈ ([] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp at hA
  have hys : ∀ A, A ∈ ([K ^ e] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_singleton] at hA
    simpa [hA] using (BD_pow K hK e)
  have hzs : ∀ A, A ∈
      ([K ^ f, K ^ a, G.N * K ^ b * G.N, K ^ c] :
        List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_cons] at hA
    rcases hA with hA | hA
    · subst A
      exact BD_pow K hK f
    · rcases hA with hA | hA
      · subst A
        exact BD_pow K hK a
      · rcases hA with hA | hA
        · subst A
          exact hQ
        · rcases hA with hA | hA
          · subst A
            exact BD_pow K hK c
          · simp at hA
  have hbd_d : BD cp (K ^ d) := BD_pow K hK d
  simpa [List.prod_cons, Matrix.mul_assoc] using (trace_three_N_word_zero G
    ([] : List (Matrix W W ℂ))
    ([K ^ e] : List (Matrix W W ℂ))
    ([K ^ f, K ^ a, G.N * K ^ b * G.N, K ^ c] :
      List (Matrix W W ℂ))
    (K ^ d) hxs hys hzs hbd_d hkg_d)

theorem trace_XNXN {cp : W → ι} (G : GlueData cp) {X : Matrix W W ℂ} (hX : BD cp X)
    (hu : GlueDiag G X) :
    Matrix.trace (X * G.N * X * G.N) =
      ∑ a, if G.g a then X a a * X (G.σ a) (G.σ a) else 0 := by
  have e : X * G.N * X * G.N = (X * G.N) * (X * G.N) := by simp only [Matrix.mul_assoc]
  rw [e]
  unfold Matrix.trace
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]
  have key : ∀ c, (X * G.N) a c * (X * G.N) c a =
      if c = G.σ a ∧ G.g a then X a a * X (G.σ a) (G.σ a) else 0 := by
    intro c
    rw [mul_N, mul_N]
    by_cases ga : G.g a
    · by_cases gc : G.g c
      · by_cases hc : c = G.σ a
        · subst hc
          rw [if_pos gc, if_pos ga, G.σσ a ga, if_pos ⟨rfl, ga⟩]
        · rw [if_pos gc, if_pos ga, if_neg (fun h => hc h.1)]
          by_cases h1 : cp a = cp (G.σ c)
          · by_cases h2 : cp c = cp (G.σ a)
            · have hne : a ≠ G.σ c := by
                intro h
                apply hc
                rw [h, G.σσ c gc]
              have hz := hu a (G.σ c) ga (G.g_σ c gc) h1
                (by rw [G.σσ c gc]; exact h2.symm) hne
              rw [hz, zero_mul]
            · rw [hX c (G.σ a) h2, mul_zero]
          · rw [hX a (G.σ c) h1, zero_mul]
      · rw [if_neg gc, zero_mul, if_neg]
        rintro ⟨hc, _⟩
        apply gc
        rw [hc]
        exact G.g_σ a ga
    · rw [if_neg ga, mul_zero, if_neg (fun h => ga h.2)]
  simp only [key]
  by_cases ga : G.g a
  · simp [ga]
  · simp [ga]

theorem trace_KQKQ {cp : W → ι} (G : GlueData cp) (K : Matrix W W ℂ) (hbd : BD cp K)
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → K w w' = 0) :
    Matrix.trace ((K * (G.N * K * G.N)) * (K * (G.N * K * G.N))) =
      ∑ a, if G.g a then K a a * K a a * (K (G.σ a) (G.σ a) * K (G.σ a) (G.σ a)) else 0 := by
  rw [Q_eq_diag G K hbd hkg]
  unfold Matrix.trace
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.mul_diagonal]
    by_cases ha : G.g a
    · simp only [if_pos ha]
      ring
    · simp [ha]
  · intro b _ hb
    simp only [Matrix.mul_diagonal]
    by_cases ga : G.g a
    · by_cases gb : G.g b
      · by_cases hc : cp a = cp b
        · have := hkg a b ga gb hc (fun h => hb h.symm)
          rw [this]
          ring
        · rw [hbd a b hc]
          ring
      · simp [gb]
    · simp [ga]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- Four-pairing boundary formula. The outermost pair of pairing matrices
is handled by the general two-pairing formula, retaining the ordered product
between them. The required corner-vanishing hypothesis is explicit for the
middle power K^d; it is not inferred from block diagonality alone. -/
theorem trace_four_N_powers {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K)
    (a b c d e : ℕ)
    (hkgD : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ d) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N * K ^ d * G.N * K ^ e) =
      ∑ x, if G.g x then
        (K ^ e * K ^ a * (G.N * K ^ b * G.N) * K ^ c) x x *
          (K ^ d) (G.σ x) (G.σ x) else 0 := by
  have hrot :
      Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N * K ^ d * G.N * K ^ e) =
      Matrix.trace ((K ^ e * K ^ a * (G.N * K ^ b * G.N) * K ^ c) *
        G.N * K ^ d * G.N) := by
    calc
      _ = Matrix.trace ((K ^ a * (G.N * K ^ b * G.N) * K ^ c * G.N * K ^ d * G.N) * K ^ e) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (K ^ e *
          (K ^ a * (G.N * K ^ b * G.N) * K ^ c * G.N * K ^ d * G.N)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((K ^ e * K ^ a * (G.N * K ^ b * G.N) * K ^ c) *
          G.N * K ^ d * G.N) := by
        simp only [Matrix.mul_assoc]
  rw [hrot]
  simpa [List.prod_cons] using (trace_two_N_word G
    ([K ^ e * K ^ a * (G.N * K ^ b * G.N) * K ^ c] : List (Matrix W W ℂ))
    ([] : List (Matrix W W ℂ)) (K ^ d) (BD_pow K hK d) hkgD)

/-- Explicit nested boundary sum for a four-pairing word. The inner pair
is expanded using its own glued-corner vanishing hypothesis, while the outer
pair uses the condition for K^d. Matrix-factor order is preserved throughout. -/
theorem trace_four_N_powers_explicit {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K)
    (a b c d e : ℕ)
    (hkgB : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ b) w w' = 0)
    (hkgD : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ d) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N * K ^ d * G.N * K ^ e) =
      ∑ x, if G.g x then
        (∑ y, if G.g y then
          ((K ^ e * K ^ a) x y * (K ^ b) (G.σ y) (G.σ y)) * (K ^ c) y x
          else 0) * (K ^ d) (G.σ x) (G.σ x) else 0 := by
  have hQ : G.N * K ^ b * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ b) (BD_pow K hK b) hkgB
  have hentry (x : W) :
      ((K ^ e * K ^ a) * (G.N * K ^ b * G.N) * K ^ c) x x =
        ∑ y, if G.g y then
          ((K ^ e * K ^ a) x y * (K ^ b) (G.σ y) (G.σ y)) * (K ^ c) y x
          else 0 := by
    rw [hQ, Matrix.mul_apply]
    simp [Matrix.mul_diagonal, Matrix.diagonal_apply, mul_assoc]
  calc
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N * K ^ d * G.N * K ^ e) =
        ∑ x, if G.g x then
          ((K ^ e * K ^ a * (G.N * K ^ b * G.N) * K ^ c) x x) *
            (K ^ d) (G.σ x) (G.σ x) else 0 :=
      trace_four_N_powers G K hK a b c d e hkgD
    _ = ∑ x, if G.g x then
          (∑ y, if G.g y then
            ((K ^ e * K ^ a) x y * (K ^ b) (G.σ y) (G.σ y)) * (K ^ c) y x
            else 0) * (K ^ d) (G.σ x) (G.σ x) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases gx : G.g x
      · simp only [gx, if_pos]
        rw [hentry x]
      · simp [gx]

/-- Six-pairing boundary reduction. Pairing consecutive N factors turns each
`N * K^n * N` into a diagonal boundary factor, provided the corresponding
corner-vanishing hypothesis is supplied. Cyclicity preserves the order of the
three boundary factors and the intervening powers; this is a boundary formula,
not a claim that the six-pairing stratum vanishes. -/
theorem trace_six_N_powers_boundary {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K)
    (a b c d e f g : ℕ)
    (hkgB : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ b) w w' = 0)
    (hkgD : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ d) w w' = 0)
    (hkgF : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ f) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f * G.N * K ^ g) =
    Matrix.trace (K ^ g * K ^ a *
      Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0) *
      K ^ c *
      Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0) *
      K ^ e *
      Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0)) := by
  have hQb : G.N * K ^ b * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ b) (BD_pow K hK b) hkgB
  have hQd : G.N * K ^ d * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ d) (BD_pow K hK d) hkgD
  have hQf : G.N * K ^ f * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ f) (BD_pow K hK f) hkgF
  have hrotate :
      Matrix.trace (K ^ a * (G.N * K ^ b * G.N) * K ^ c *
        (G.N * K ^ d * G.N) * K ^ e * (G.N * K ^ f * G.N) * K ^ g) =
      Matrix.trace (K ^ g * K ^ a * (G.N * K ^ b * G.N) * K ^ c *
        (G.N * K ^ d * G.N) * K ^ e * (G.N * K ^ f * G.N)) := by
    calc
      Matrix.trace ((K ^ a * (G.N * K ^ b * G.N) * K ^ c *
          (G.N * K ^ d * G.N) * K ^ e * (G.N * K ^ f * G.N)) * K ^ g) =
          Matrix.trace (K ^ g *
            (K ^ a * (G.N * K ^ b * G.N) * K ^ c *
              (G.N * K ^ d * G.N) * K ^ e * (G.N * K ^ f * G.N)) ) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (K ^ g * K ^ a * (G.N * K ^ b * G.N) * K ^ c *
          (G.N * K ^ d * G.N) * K ^ e * (G.N * K ^ f * G.N)) := by
        simp only [Matrix.mul_assoc]
  rw [show K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f * G.N * K ^ g =
      K ^ a * (G.N * K ^ b * G.N) * K ^ c *
        (G.N * K ^ d * G.N) * K ^ e * (G.N * K ^ f * G.N) * K ^ g by
      simp only [Matrix.mul_assoc]]
  rw [hrotate, hQb, hQd, hQf]

/-- Seven-pairing trace words vanish under three explicit corner
hypotheses. Pairing the first two selected gaps makes two diagonal boundary
blocks; the remaining three N factors are then handled by the generic
three-pairing reduction. The hypotheses for the three selected middle powers
remain explicit. -/
theorem trace_seven_N_powers_zero {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K)
    (a b c d e f g h : ℕ)
    (hkgB : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ b) w w' = 0)
    (hkgD : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ d) w w' = 0)
    (hkgF : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ f) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f * G.N * K ^ g * G.N * K ^ h) = 0 := by
  have hQb : G.N * K ^ b * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ b) (BD_pow K hK b) hkgB
  have hQd : G.N * K ^ d * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ d) (BD_pow K hK d) hkgD
  rw [show K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f * G.N * K ^ g * G.N * K ^ h =
      K ^ a * (G.N * K ^ b * G.N) * K ^ c *
        (G.N * K ^ d * G.N) * K ^ e * G.N * K ^ f * G.N * K ^ g * G.N * K ^ h by
      simp only [Matrix.mul_assoc]]
  rw [hQb, hQd]
  have hxs : ∀ A, A ∈
      ([K ^ a,
        Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0),
        K ^ c,
        Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0),
        K ^ e] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_cons] at hA
    rcases hA with hA | hA
    · subst A
      exact BD_pow K hK a
    · rcases hA with hA | hA
      · subst A
        exact BD_diagonal _
      · rcases hA with hA | hA
        · subst A
          exact BD_pow K hK c
        · rcases hA with hA | hA
          · subst A
            exact BD_diagonal _
          · rcases hA with hA | hA
            · subst A
              exact BD_pow K hK e
            · simp at hA
  have hys : ∀ A, A ∈ ([K ^ g] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_singleton] at hA
    simpa [hA] using (BD_pow K hK g)
  have hzs : ∀ A, A ∈ ([K ^ h] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_singleton] at hA
    simpa [hA] using (BD_pow K hK h)
  simpa [List.prod_cons, Matrix.mul_assoc] using
    (trace_three_N_word_zero G
      ([K ^ a,
        Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0),
        K ^ c,
        Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0),
        K ^ e] : List (Matrix W W ℂ))
      ([K ^ g] : List (Matrix W W ℂ))
      ([K ^ h] : List (Matrix W W ℂ))
      (K ^ f) hxs hys hzs (BD_pow K hK f) hkgF)

/-- Eight-pairing boundary formula. Three selected N-K-power-N blocks
are diagonalized, leaving a two-pairing word whose remaining middle-power
corner condition is explicit. -/
theorem trace_eight_N_powers_boundary {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K)
    (a b c d e f g h i : ℕ)
    (hkgB : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ b) w w' = 0)
    (hkgD : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ d) w w' = 0)
    (hkgF : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ f) w w' = 0)
    (hkgH : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ h) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f * G.N * K ^ g * G.N *
      K ^ h * G.N * K ^ i) =
      ∑ x, if G.g x then
        (([K ^ i, K ^ a,
          Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0),
          K ^ c,
          Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0),
          K ^ e,
          Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0),
          K ^ g] : List (Matrix W W ℂ)).prod) x x *
          (K ^ h) (G.σ x) (G.σ x) else 0 := by
  have hQb : G.N * K ^ b * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ b) (BD_pow K hK b) hkgB
  have hQd : G.N * K ^ d * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ d) (BD_pow K hK d) hkgD
  have hQf : G.N * K ^ f * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ f) (BD_pow K hK f) hkgF
  rw [show K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f * G.N * K ^ g * G.N *
      K ^ h * G.N * K ^ i =
      K ^ a * (G.N * K ^ b * G.N) * K ^ c *
        (G.N * K ^ d * G.N) * K ^ e *
        (G.N * K ^ f * G.N) * K ^ g * G.N * K ^ h * G.N * K ^ i by
      simp only [Matrix.mul_assoc]]
  rw [hQb, hQd, hQf]
  have hxs : ∀ A, A ∈
      ([K ^ a,
        Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0),
        K ^ c,
        Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0),
        K ^ e,
        Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0),
        K ^ g] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_cons] at hA
    rcases hA with hA | hA
    · subst A; exact BD_pow K hK a
    · rcases hA with hA | hA
      · subst A; exact BD_diagonal _
      · rcases hA with hA | hA
        · subst A; exact BD_pow K hK c
        · rcases hA with hA | hA
          · subst A; exact BD_diagonal _
          · rcases hA with hA | hA
            · subst A; exact BD_pow K hK e
            · rcases hA with hA | hA
              · subst A; exact BD_diagonal _
              · rcases hA with hA | hA
                · subst A; exact BD_pow K hK g
                · simp at hA
  have hys : ∀ A, A ∈ ([K ^ i] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_singleton] at hA
    simpa [hA] using (BD_pow K hK i)
  simpa [List.prod_cons, Matrix.mul_assoc] using
    (trace_two_N_word G
      ([K ^ a,
        Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0),
        K ^ c,
        Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0),
        K ^ e,
        Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0),
        K ^ g] : List (Matrix W W ℂ))
      ([K ^ i] : List (Matrix W W ℂ)) (K ^ h) (BD_pow K hK h) hkgH)

/-- Nine-pairing words vanish conditionally: diagonalize three selected
N-K-power-N blocks, then apply the generic three-pairing vanishing lemma to
the remaining three N factors. -/
theorem trace_nine_N_powers_zero {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K)
    (a b c d e f g h i j : ℕ)
    (hkgB : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ b) w w' = 0)
    (hkgD : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ d) w w' = 0)
    (hkgF : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ f) w w' = 0)
    (hkgH : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ h) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f * G.N * K ^ g * G.N *
      K ^ h * G.N * K ^ i * G.N * K ^ j) = 0 := by
  have hQb : G.N * K ^ b * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ b) (BD_pow K hK b) hkgB
  have hQd : G.N * K ^ d * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ d) (BD_pow K hK d) hkgD
  have hQf : G.N * K ^ f * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ f) (BD_pow K hK f) hkgF
  rw [show K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f * G.N * K ^ g * G.N *
      K ^ h * G.N * K ^ i * G.N * K ^ j =
      K ^ a * (G.N * K ^ b * G.N) * K ^ c *
        (G.N * K ^ d * G.N) * K ^ e *
        (G.N * K ^ f * G.N) * K ^ g * G.N * K ^ h * G.N *
        K ^ i * G.N * K ^ j by
      simp only [Matrix.mul_assoc]]
  rw [hQb, hQd, hQf]
  have hxs : ∀ A, A ∈
      ([K ^ a,
        Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0),
        K ^ c,
        Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0),
        K ^ e,
        Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0),
        K ^ g] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_cons] at hA
    rcases hA with hA | hA
    · subst A; exact BD_pow K hK a
    · rcases hA with hA | hA
      · subst A; exact BD_diagonal _
      · rcases hA with hA | hA
        · subst A; exact BD_pow K hK c
        · rcases hA with hA | hA
          · subst A; exact BD_diagonal _
          · rcases hA with hA | hA
            · subst A; exact BD_pow K hK e
            · rcases hA with hA | hA
              · subst A; exact BD_diagonal _
              · rcases hA with hA | hA
                · subst A; exact BD_pow K hK g
                · simp at hA
  have hys : ∀ A, A ∈ ([K ^ i] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_singleton] at hA
    simpa [hA] using (BD_pow K hK i)
  have hzs : ∀ A, A ∈ ([K ^ j] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_singleton] at hA
    simpa [hA] using (BD_pow K hK j)
  simpa [List.prod_cons, Matrix.mul_assoc] using
    (trace_three_N_word_zero G
      ([K ^ a,
        Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0),
        K ^ c,
        Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0),
        K ^ e,
        Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0),
        K ^ g] : List (Matrix W W ℂ))
      ([K ^ i] : List (Matrix W W ℂ))
      ([K ^ j] : List (Matrix W W ℂ))
      (K ^ h) hxs hys hzs (BD_pow K hK h) hkgH)

/-- Ten-pairing boundary formula. Four selected N-K-power-N blocks are
diagonalized, leaving an explicit two-pairing boundary sum. -/
theorem trace_ten_N_powers_boundary {cp : W → ι} (G : GlueData cp)
    (K : Matrix W W ℂ) (hK : BD cp K)
    (a b c d e f g h i j k : ℕ)
    (hkgB : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ b) w w' = 0)
    (hkgD : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ d) w w' = 0)
    (hkgF : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ f) w w' = 0)
    (hkgH : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ h) w w' = 0)
    (hkgJ : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' →
      (K ^ j) w w' = 0) :
    Matrix.trace (K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f * G.N * K ^ g * G.N *
      K ^ h * G.N * K ^ i * G.N * K ^ j * G.N * K ^ k) =
      ∑ x, if G.g x then
        (([K ^ k, K ^ a,
          Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0),
          K ^ c,
          Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0),
          K ^ e,
          Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0),
          K ^ g,
          Matrix.diagonal (fun y => if G.g y then (K ^ h) (G.σ y) (G.σ y) else 0),
          K ^ i] : List (Matrix W W ℂ)).prod) x x *
          (K ^ j) (G.σ x) (G.σ x) else 0 := by
  have hQb : G.N * K ^ b * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ b) (BD_pow K hK b) hkgB
  have hQd : G.N * K ^ d * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ d) (BD_pow K hK d) hkgD
  have hQf : G.N * K ^ f * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ f) (BD_pow K hK f) hkgF
  have hQh : G.N * K ^ h * G.N =
      Matrix.diagonal (fun y => if G.g y then (K ^ h) (G.σ y) (G.σ y) else 0) :=
    Q_eq_diag G (K ^ h) (BD_pow K hK h) hkgH
  rw [show K ^ a * G.N * K ^ b * G.N * K ^ c * G.N *
      K ^ d * G.N * K ^ e * G.N * K ^ f * G.N * K ^ g * G.N *
      K ^ h * G.N * K ^ i * G.N * K ^ j * G.N * K ^ k =
      K ^ a * (G.N * K ^ b * G.N) * K ^ c *
        (G.N * K ^ d * G.N) * K ^ e *
        (G.N * K ^ f * G.N) * K ^ g *
        (G.N * K ^ h * G.N) * K ^ i * G.N * K ^ j * G.N * K ^ k by
      simp only [Matrix.mul_assoc]]
  rw [hQb, hQd, hQf, hQh]
  have hxs : ∀ A, A ∈
      ([K ^ a,
        Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0),
        K ^ c,
        Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0),
        K ^ e,
        Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0),
        K ^ g,
        Matrix.diagonal (fun y => if G.g y then (K ^ h) (G.σ y) (G.σ y) else 0),
        K ^ i] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_cons] at hA
    rcases hA with hA | hA
    · subst A; exact BD_pow K hK a
    · rcases hA with hA | hA
      · subst A; exact BD_diagonal _
      · rcases hA with hA | hA
        · subst A; exact BD_pow K hK c
        · rcases hA with hA | hA
          · subst A; exact BD_diagonal _
          · rcases hA with hA | hA
            · subst A; exact BD_pow K hK e
            · rcases hA with hA | hA
              · subst A; exact BD_diagonal _
              · rcases hA with hA | hA
                · subst A; exact BD_pow K hK g
                · rcases hA with hA | hA
                  · subst A; exact BD_diagonal _
                  · rcases hA with hA | hA
                    · subst A; exact BD_pow K hK i
                    · simp at hA
  have hys : ∀ A, A ∈ ([K ^ k] : List (Matrix W W ℂ)) → BD cp A := by
    intro A hA
    simp only [List.mem_singleton] at hA
    simpa [hA] using (BD_pow K hK k)
  simpa [List.prod_cons, Matrix.mul_assoc] using
    (trace_two_N_word G
      ([K ^ a,
        Matrix.diagonal (fun y => if G.g y then (K ^ b) (G.σ y) (G.σ y) else 0),
        K ^ c,
        Matrix.diagonal (fun y => if G.g y then (K ^ d) (G.σ y) (G.σ y) else 0),
        K ^ e,
        Matrix.diagonal (fun y => if G.g y then (K ^ f) (G.σ y) (G.σ y) else 0),
        K ^ g,
        Matrix.diagonal (fun y => if G.g y then (K ^ h) (G.σ y) (G.σ y) else 0),
        K ^ i] : List (Matrix W W ℂ))
      ([K ^ k] : List (Matrix W W ℂ)) (K ^ j) (BD_pow K hK j) hkgJ)


/-- The cyclic four-N class (1,1,6,2) has four distinct cyclic
rotations, hence multiplicity ten. This is a boundary-sum reduction only;
no cancellation with other strata is asserted. -/
theorem trace_p10_four_N_class_1162 {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 9 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    10 * Matrix.trace
      (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 6 * G.N * K ^ 2 * G.N * K ^ 0) =
    10 * (∑ x, if G.g x then
      (∑ y, if G.g y then
        ((K ^ 0 * K ^ 1) x y * (K ^ 1) (G.σ y) (G.σ y)) *
          (K ^ 6) y x else 0) *
        (K ^ 2) (G.σ x) (G.σ x) else 0) := by
  rw [trace_four_N_powers_explicit G K hK 1 1 6 2 0
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 1 (by omega) w w' hw hw' hcopy hne)
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 2 (by omega) w w' hw hw' hcopy hne)]

/-- Another four-N cyclic class in the tenth-moment expansion. The run
lengths (1,1,5,3) have four distinct cyclic rotations, hence multiplicity
10. This is a class-level boundary reduction only; it does not assert that
different cyclic classes cancel. -/
theorem trace_p10_four_N_class_1153 {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 9 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    10 * Matrix.trace
      (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 5 * G.N * K ^ 3 * G.N * K ^ 0) =
    10 * (∑ x, if G.g x then
      (∑ y, if G.g y then
        ((K ^ 0 * K ^ 1) x y * (K ^ 1) (G.σ y) (G.σ y)) *
          (K ^ 5) y x else 0) *
        (K ^ 3) (G.σ x) (G.σ x) else 0) := by
  rw [trace_four_N_powers_explicit G K hK 1 1 5 3 0
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 1 (by omega) w w' hw hw' hcopy hne)
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 3 (by omega) w w' hw hw' hcopy hne)]

/-- One four-N cyclic class in the tenth-moment expansion. The run lengths
(1,1,1,7) have cyclic orbit size four, hence multiplicity 10 among the
length-ten words. This records its exact boundary-kernel expression; it does
not identify it with any other class or claim cancellation. -/
theorem trace_p10_four_N_class_1117 {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 9 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    10 * Matrix.trace
      (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 1 * G.N * K ^ 7 * G.N * K ^ 0) =
    10 * (∑ x, if G.g x then
      (∑ y, if G.g y then
        ((K ^ 0 * K ^ 1) x y * (K ^ 1) (G.σ y) (G.σ y)) *
          (K ^ 1) y x else 0) *
        (K ^ 7) (G.σ x) (G.σ x) else 0) := by
  rw [trace_four_N_powers_explicit G K hK 1 1 1 7 0
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 1 (by omega) w w' hw hw' hcopy hne)
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 7 (by omega) w w' hw hw' hcopy hne)]


/-- A second four-N cyclic class in the tenth-moment expansion. The run
lengths (1,1,2,6) have four distinct cyclic rotations, so the word
multiplicity is 10. This gives the class's boundary-sum form without
identifying it with other classes or asserting cancellation. -/
theorem trace_p10_four_N_class_1126 {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 9 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    10 * Matrix.trace
      (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 2 * G.N * K ^ 6 * G.N * K ^ 0) =
    10 * (∑ x, if G.g x then
      (∑ y, if G.g y then
        ((K ^ 0 * K ^ 1) x y * (K ^ 1) (G.σ y) (G.σ y)) *
          (K ^ 2) y x else 0) *
        (K ^ 6) (G.σ x) (G.σ x) else 0) := by
  rw [trace_four_N_powers_explicit G K hK 1 1 2 6 0
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 1 (by omega) w w' hw hw' hcopy hne)
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 6 (by omega) w w' hw hw' hcopy hne)]


/-- A third four-N cyclic class in the tenth-moment expansion. The run
lengths (1,1,3,5) have four distinct cyclic rotations, giving multiplicity
10 among length-ten words. No identification with other classes or
cancellation is asserted. -/
/-- The cyclic four-N class (1,2,1,6) has four distinct cyclic rotations,
hence multiplicity ten among the length-ten words. This records its exact
boundary-sum expression and does not assert cancellation with other classes. -/
theorem trace_p10_four_N_class_1216 {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 9 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    10 * Matrix.trace
      (K ^ 1 * G.N * K ^ 2 * G.N * K ^ 1 * G.N * K ^ 6 * G.N * K ^ 0) =
    10 * (∑ x, if G.g x then
      (∑ y, if G.g y then
        ((K ^ 0 * K ^ 1) x y * (K ^ 2) (G.σ y) (G.σ y)) *
          (K ^ 1) y x else 0) *
        (K ^ 6) (G.σ x) (G.σ x) else 0) := by
  rw [trace_four_N_powers_explicit G K hK 1 2 1 6 0
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 2 (by omega) w w' hw hw' hcopy hne)
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 6 (by omega) w w' hw hw' hcopy hne)]

theorem trace_p10_four_N_class_1135 {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 9 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    10 * Matrix.trace
      (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 3 * G.N * K ^ 5 * G.N * K ^ 0) =
    10 * (∑ x, if G.g x then
      (∑ y, if G.g y then
        ((K ^ 0 * K ^ 1) x y * (K ^ 1) (G.σ y) (G.σ y)) *
          (K ^ 3) y x else 0) *
        (K ^ 5) (G.σ x) (G.σ x) else 0) := by
  rw [trace_four_N_powers_explicit G K hK 1 1 3 5 0
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 1 (by omega) w w' hw hw' hcopy hne)
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 5 (by omega) w w' hw hw' hcopy hne)]


/-- The cyclic four-N class (1,1,4,4) has four distinct cyclic
rotations, hence multiplicity ten. It is distinct from the alternating
class (1,4,1,4), whose multiplicity is five. -/
theorem trace_p10_four_N_class_1144 {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 9 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    10 * Matrix.trace
      (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 4 * G.N * K ^ 4 * G.N * K ^ 0) =
    10 * (∑ x, if G.g x then
      (∑ y, if G.g y then
        ((K ^ 0 * K ^ 1) x y * (K ^ 1) (G.σ y) (G.σ y)) *
          (K ^ 4) y x else 0) *
        (K ^ 4) (G.σ x) (G.σ x) else 0) := by
  rw [trace_four_N_powers_explicit G K hK 1 1 4 4 0
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 1 (by omega) w w' hw hw' hcopy hne)
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 4 (by omega) w w' hw hw' hcopy hne)]

/-- The cyclic four-N class (1,4,1,4) has two distinct cyclic rotations,
hence multiplicity five. The nested boundary-sum formula preserves the exact order of factors. -/
theorem trace_p10_four_N_class_1414 {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 9 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    5 * Matrix.trace
      (K ^ 1 * G.N * K ^ 4 * G.N * K ^ 1 * G.N * K ^ 4 * G.N * K ^ 0) =
    5 * (∑ x, if G.g x then
      (∑ y, if G.g y then
        ((K ^ 0 * K ^ 1) x y * (K ^ 4) (G.σ y) (G.σ y)) *
          (K ^ 1) y x else 0) *
        (K ^ 4) (G.σ x) (G.σ x) else 0) := by
  rw [trace_four_N_powers_explicit G K hK 1 4 1 4 0
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 4 (by omega) w w' hw hw' hcopy hne)
    (by
      intro w w' hw hw' hcopy hne
      exact hkg 4 (by omega) w w' hw hw' hcopy hne)]

/-- **Gluing identity.** -/
theorem glue_trace4 {cp : W → ι} (G : GlueData cp) (K : Matrix W W ℂ) (hbd : BD cp K)
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → K w w' = 0)
    (hu2 : GlueDiag G (K * K)) :
    Matrix.trace ((K + K * G.N) * (K + K * G.N) * (K + K * G.N) * (K + K * G.N)) =
      Matrix.trace (K * K * K * K) +
        4 * ∑ a, (if G.g a then (K * K * K) a a * K (G.σ a) (G.σ a) else 0) +
        2 * ∑ a, (if G.g a then (K * K) a a * (K * K) (G.σ a) (G.σ a) else 0) +
        ∑ a, (if G.g a then K a a * K a a * (K (G.σ a) (G.σ a) * K (G.σ a) (G.σ a))
          else 0) := by
  have h := trace_sub_pow4 K (-(K * G.N))
  simp only [sub_neg_eq_add] at h
  rw [h]
  have hK2 : BD cp (K * K) := BD_mul hbd hbd
  have hK3 : BD cp (K * K * K) := BD_mul hK2 hbd
  have hK4 : BD cp (K * K * K * K) := BD_mul hK3 hbd
  have hQ : BD cp (G.N * K * G.N) := by
    rw [Q_eq_diag G K hbd hkg]
    exact BD_diagonal _
  have r1 : Matrix.trace (K * K * K * K * G.N) = 0 := trace_BD_N G hK4
  have r4 : Matrix.trace (K * K * (G.N * K * G.N) * K * G.N) = 0 :=
    trace_BD_N G (BD_mul (BD_mul hK2 hQ) hbd)
  have r3 := trace_mul_Q G K hbd hkg (K * K * K)
  have r2 := trace_XNXN G hK2 hu2
  have r5 := trace_KQKQ G K hbd hkg
  have e1 : Matrix.trace (K * K * K * -(K * G.N)) = - Matrix.trace (K * K * K * K * G.N) := by
    simp only [Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_assoc]
  have e2 : Matrix.trace (K * K * -(K * G.N) * -(K * G.N)) =
      Matrix.trace (K * K * K * (G.N * K * G.N)) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have e3 : Matrix.trace (K * -(K * G.N) * K * -(K * G.N)) =
      Matrix.trace (K * K * G.N * (K * K) * G.N) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have e4 : Matrix.trace (K * -(K * G.N) * -(K * G.N) * -(K * G.N)) =
      - Matrix.trace (K * K * (G.N * K * G.N) * K * G.N) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.trace_neg, Matrix.mul_assoc]
  have e5 : Matrix.trace (-(K * G.N) * -(K * G.N) * -(K * G.N) * -(K * G.N)) =
      Matrix.trace ((K * (G.N * K * G.N)) * (K * (G.N * K * G.N))) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have e3' : Matrix.trace (K * K * G.N * (K * K) * G.N) =
      Matrix.trace ((K * K) * G.N * (K * K) * G.N) := by
    simp only [Matrix.mul_assoc]
  rw [e1, e2, e3, e4, e5, e3', r1, r4, r2, r5]
  have r3' : Matrix.trace (K * K * K * (G.N * K * G.N)) =
      ∑ a, if G.g a then (K * K * K) a a * K (G.σ a) (G.σ a) else 0 := r3
  rw [r3']
  ring



/-- Block diagonality across copies plus the glued-corner hypothesis
implies that K has no off-diagonal entries anywhere on the glued locus. -/
theorem glued_offdiag_of_BD {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ)
    (hbd : BD cp K)
    (hkg : ∀ x y, G.g x → G.g y → cp x = cp y → x ≠ y → K x y = 0) :
    ∀ x y, G.g x → G.g y → x ≠ y → K x y = 0 := by
  intro x y gx gy hne
  by_cases hc : cp x = cp y
  · exact hkg x y gx gy hc hne
  · exact hbd x y hc

/-- If the restriction of K to glued points is diagonal, a nested boundary
sum collapses to its diagonal kernel. This isolates the support step needed
before comparing the p=6 four-pairing terms. -/
theorem glued_boundary_kernel_sum_diagonal {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ)
    (hKoff : ∀ x y, G.g x → G.g y → x ≠ y → K x y = 0)
    (F : W → W → ℂ) (H : W → ℂ) :
    (∑ x, if G.g x then
      (∑ y, if G.g y then K x y * F y x else 0) * H x else 0) =
      ∑ x, if G.g x then K x x * F x x * H x else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro x hx
  by_cases gx : G.g x
  · simp only [gx, if_pos]
    have hinner :
        (∑ y, if G.g y then K x y * F y x else 0) = K x x * F x x := by
      rw [Finset.sum_eq_single x]
      · simp [gx]
      · intro y hy hne
        by_cases gy : G.g y
        · simp [gy, hKoff x y gx gy hne.symm]
        · simp [gy]
      · simp
    rw [hinner]
  · simp [gx]

/-- Convenient form of the diagonal collapse: its support premise follows
from the standard block-diagonal and glued-corner hypotheses. -/
theorem glued_boundary_kernel_sum_diagonal_of_BD {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hbd : BD cp K)
    (hkg : ∀ x y, G.g x → G.g y → cp x = cp y → x ≠ y → K x y = 0)
    (F : W → W → ℂ) (H : W → ℂ) :
    (∑ x, if G.g x then
      (∑ y, if G.g y then K x y * F y x else 0) * H x else 0) =
      ∑ x, if G.g x then K x x * F x x * H x else 0 := by
  exact glued_boundary_kernel_sum_diagonal G K
    (glued_offdiag_of_BD G K hbd hkg) F H

/-- Four-pairing words whose left boundary power is K have a fully
diagonal two-boundary kernel. The remaining powers may be arbitrary; only
the middle and right powers need the usual glued-corner vanishing. -/
theorem trace_four_N_powers_diagonal_left_one {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (b c d : ℕ)
    (hkgK : ∀ x y, G.g x → G.g y → cp x = cp y → x ≠ y → K x y = 0)
    (hkgB : ∀ x y, G.g x → G.g y → cp x = cp y → x ≠ y →
      (K ^ b) x y = 0)
    (hkgD : ∀ x y, G.g x → G.g y → cp x = cp y → x ≠ y →
      (K ^ d) x y = 0) :
    Matrix.trace (K ^ 1 * G.N * K ^ b * G.N * K ^ c * G.N * K ^ d * G.N * K ^ 0) =
      ∑ x, if G.g x then
        (K x x * (K ^ b) (G.σ x) (G.σ x) * (K ^ c) x x) *
          (K ^ d) (G.σ x) (G.σ x) else 0 := by
  have hexp := trace_four_N_powers_explicit G K hK 1 b c d 0 hkgB hkgD
  rw [hexp]
  have hcollapse := glued_boundary_kernel_sum_diagonal_of_BD
    G K hK hkgK
    (fun y x => (K ^ b) (G.σ y) (G.σ y) * (K ^ c) y x)
    (fun x => (K ^ d) (G.σ x) (G.σ x))
  simpa [pow_zero, Matrix.one_mul, mul_assoc] using hcollapse

/-- Exact weighted boundary reduction for the two lower even strata of the
sixth moment. The coefficients 6, 6, 3 are the orbit multiplicities of the
cyclic classes; no reversal-pair equality is assumed. This lemma only exposes
the boundary kernels. Comparing them for two concrete operators is a separate
geometric obligation. -/
theorem trace_p6_lower_even_strata_boundary {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 5 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    6 * Matrix.trace (K ^ 1 * G.N * K ^ 5 * G.N * K ^ 0) +
    6 * Matrix.trace (K ^ 2 * G.N * K ^ 4 * G.N * K ^ 0) +
    3 * Matrix.trace (K ^ 3 * G.N * K ^ 3 * G.N * K ^ 0) +
    6 * Matrix.trace (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 1 * G.N * K ^ 3 * G.N * K ^ 0) +
    6 * Matrix.trace (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 2 * G.N * K ^ 2 * G.N * K ^ 0) +
    3 * Matrix.trace (K ^ 1 * G.N * K ^ 2 * G.N * K ^ 1 * G.N * K ^ 2 * G.N * K ^ 0) =
    6 * (∑ x, if G.g x then
      (K ^ 1) x x * (K ^ 5) (G.σ x) (G.σ x) else 0) +
    6 * (∑ x, if G.g x then
      (K ^ 2) x x * (K ^ 4) (G.σ x) (G.σ x) else 0) +
    3 * (∑ x, if G.g x then
      (K ^ 3) x x * (K ^ 3) (G.σ x) (G.σ x) else 0) +
    6 * (∑ x, if G.g x then
      (K x x * (K ^ 1) (G.σ x) (G.σ x) * (K ^ 1) x x) *
        (K ^ 3) (G.σ x) (G.σ x) else 0) +
    6 * (∑ x, if G.g x then
      (K x x * (K ^ 1) (G.σ x) (G.σ x) * (K ^ 2) x x) *
        (K ^ 2) (G.σ x) (G.σ x) else 0) +
    3 * (∑ x, if G.g x then
      (K x x * (K ^ 2) (G.σ x) (G.σ x) * (K ^ 1) x x) *
        (K ^ 2) (G.σ x) (G.σ x) else 0) := by
  have h21 :
      Matrix.trace (K ^ 1 * G.N * K ^ 5 * G.N * K ^ 0) =
        ∑ x, if G.g x then
          (K ^ 1) x x * (K ^ 5) (G.σ x) (G.σ x) else 0 := by
    simpa [pow_zero, pow_one] using
      (trace_two_N_powers G K 1 5 0 (BD_pow K hK 5) (by
        intro w w' hw hw' hcopy hne
        exact hkg 5 (by omega) w w' hw hw' hcopy hne))
  have h22 :
      Matrix.trace (K ^ 2 * G.N * K ^ 4 * G.N * K ^ 0) =
        ∑ x, if G.g x then
          (K ^ 2) x x * (K ^ 4) (G.σ x) (G.σ x) else 0 := by
    simpa [pow_zero] using
      (trace_two_N_powers G K 2 4 0 (BD_pow K hK 4) (by
        intro w w' hw hw' hcopy hne
        exact hkg 4 (by omega) w w' hw hw' hcopy hne))
  have h23 :
      Matrix.trace (K ^ 3 * G.N * K ^ 3 * G.N * K ^ 0) =
        ∑ x, if G.g x then
          (K ^ 3) x x * (K ^ 3) (G.σ x) (G.σ x) else 0 := by
    simpa [pow_zero] using
      (trace_two_N_powers G K 3 3 0 (BD_pow K hK 3) (by
        intro w w' hw hw' hcopy hne
        exact hkg 3 (by omega) w w' hw hw' hcopy hne))
  have h41 :
      Matrix.trace (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 1 * G.N *
        K ^ 3 * G.N * K ^ 0) =
        ∑ x, if G.g x then
          ((K x x * (K ^ 1) (G.σ x) (G.σ x) * (K ^ 1) x x) *
            (K ^ 3) (G.σ x) (G.σ x)) else 0 := by
    simpa [pow_zero, pow_one] using
      (trace_four_N_powers_diagonal_left_one G K hK 1 1 3
        (by intro w w' hw hw' hcopy hne; simpa [pow_one] using (hkg 1 (by omega) w w' hw hw' hcopy hne))
        (by intro w w' hw hw' hcopy hne; simpa [pow_one] using (hkg 1 (by omega) w w' hw hw' hcopy hne))
        (by intro w w' hw hw' hcopy hne; exact hkg 3 (by omega) w w' hw hw' hcopy hne))
  have h42 :
      Matrix.trace (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 2 * G.N *
        K ^ 2 * G.N * K ^ 0) =
        ∑ x, if G.g x then
          ((K x x * (K ^ 1) (G.σ x) (G.σ x) * (K ^ 2) x x) *
            (K ^ 2) (G.σ x) (G.σ x)) else 0 := by
    simpa [pow_zero, pow_one] using
      (trace_four_N_powers_diagonal_left_one G K hK 1 2 2
        (by intro w w' hw hw' hcopy hne; simpa [pow_one] using (hkg 1 (by omega) w w' hw hw' hcopy hne))
        (by intro w w' hw hw' hcopy hne; simpa [pow_one] using (hkg 1 (by omega) w w' hw hw' hcopy hne))
        (by intro w w' hw hw' hcopy hne; exact hkg 2 (by omega) w w' hw hw' hcopy hne))
  have h43 :
      Matrix.trace (K ^ 1 * G.N * K ^ 2 * G.N * K ^ 1 * G.N *
        K ^ 2 * G.N * K ^ 0) =
        ∑ x, if G.g x then
          ((K x x * (K ^ 2) (G.σ x) (G.σ x) * (K ^ 1) x x) *
            (K ^ 2) (G.σ x) (G.σ x)) else 0 := by
    simpa [pow_zero, pow_one] using
      (trace_four_N_powers_diagonal_left_one G K hK 2 1 2
        (by intro w w' hw hw' hcopy hne; simpa [pow_one] using (hkg 1 (by omega) w w' hw hw' hcopy hne))
        (by intro w w' hw hw' hcopy hne; exact hkg 2 (by omega) w w' hw hw' hcopy hne)
        (by intro w w' hw hw' hcopy hne; exact hkg 2 (by omega) w w' hw hw' hcopy hne))
  rw [h21, h22, h23, h41, h42, h43]




/-- The two-N stratum of the tenth moment, grouped by cyclic rotations.
The five classes of positive run lengths are (1,9), (2,8), (3,7),
(4,6), and (5,5), with multiplicities 10, 10, 10, 10, and 5.
This theorem only reduces these five trace classes to boundary sums. -/
theorem trace_p10_two_N_stratum_boundary {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 9 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    10 * Matrix.trace (K ^ 1 * G.N * K ^ 9 * G.N * K ^ 0) +
    10 * Matrix.trace (K ^ 2 * G.N * K ^ 8 * G.N * K ^ 0) +
    10 * Matrix.trace (K ^ 3 * G.N * K ^ 7 * G.N * K ^ 0) +
    10 * Matrix.trace (K ^ 4 * G.N * K ^ 6 * G.N * K ^ 0) +
    5 * Matrix.trace (K ^ 5 * G.N * K ^ 5 * G.N * K ^ 0) =
    10 * (∑ x, if G.g x then
      (K ^ 1) x x * (K ^ 9) (G.σ x) (G.σ x) else 0) +
    10 * (∑ x, if G.g x then
      (K ^ 2) x x * (K ^ 8) (G.σ x) (G.σ x) else 0) +
    10 * (∑ x, if G.g x then
      (K ^ 3) x x * (K ^ 7) (G.σ x) (G.σ x) else 0) +
    10 * (∑ x, if G.g x then
      (K ^ 4) x x * (K ^ 6) (G.σ x) (G.σ x) else 0) +
    5 * (∑ x, if G.g x then
      (K ^ 5) x x * (K ^ 5) (G.σ x) (G.σ x) else 0) := by
  have h19 :
      Matrix.trace (K ^ 1 * G.N * K ^ 9 * G.N * K ^ 0) =
        ∑ x, if G.g x then
          (K ^ 1) x x * (K ^ 9) (G.σ x) (G.σ x) else 0 := by
    simpa [pow_zero] using
      (trace_two_N_powers G K 1 9 0 (BD_pow K hK 9) (by
        intro w w' hw hw' hcopy hne
        exact hkg 9 (by omega) w w' hw hw' hcopy hne))
  have h28 :
      Matrix.trace (K ^ 2 * G.N * K ^ 8 * G.N * K ^ 0) =
        ∑ x, if G.g x then
          (K ^ 2) x x * (K ^ 8) (G.σ x) (G.σ x) else 0 := by
    simpa [pow_zero] using
      (trace_two_N_powers G K 2 8 0 (BD_pow K hK 8) (by
        intro w w' hw hw' hcopy hne
        exact hkg 8 (by omega) w w' hw hw' hcopy hne))
  have h37 :
      Matrix.trace (K ^ 3 * G.N * K ^ 7 * G.N * K ^ 0) =
        ∑ x, if G.g x then
          (K ^ 3) x x * (K ^ 7) (G.σ x) (G.σ x) else 0 := by
    simpa [pow_zero] using
      (trace_two_N_powers G K 3 7 0 (BD_pow K hK 7) (by
        intro w w' hw hw' hcopy hne
        exact hkg 7 (by omega) w w' hw hw' hcopy hne))
  have h46 :
      Matrix.trace (K ^ 4 * G.N * K ^ 6 * G.N * K ^ 0) =
        ∑ x, if G.g x then
          (K ^ 4) x x * (K ^ 6) (G.σ x) (G.σ x) else 0 := by
    simpa [pow_zero] using
      (trace_two_N_powers G K 4 6 0 (BD_pow K hK 6) (by
        intro w w' hw hw' hcopy hne
        exact hkg 6 (by omega) w w' hw hw' hcopy hne))
  have h55 :
      Matrix.trace (K ^ 5 * G.N * K ^ 5 * G.N * K ^ 0) =
        ∑ x, if G.g x then
          (K ^ 5) x x * (K ^ 5) (G.σ x) (G.σ x) else 0 := by
    simpa [pow_zero] using
      (trace_two_N_powers G K 5 5 0 (BD_pow K hK 5) (by
        intro w w' hw hw' hcopy hne
        exact hkg 5 (by omega) w w' hw hw' hcopy hne))
  rw [h19, h28, h37, h46, h55]

/-- The top even stratum of the sixth moment is a three-step boundary trace.
This specialization deliberately does not assert vanishing: its value must be
compared with the other even strata (or with the corresponding operator's
boundary correction). -/
theorem trace_p6_top_stratum_boundary {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 5 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    Matrix.trace (K * G.N * K * G.N * K * G.N *
      K * G.N * K * G.N * K * G.N) =
    Matrix.trace (K * Matrix.diagonal (fun y =>
      if G.g y then K (G.σ y) (G.σ y) else 0) *
      K * Matrix.diagonal (fun y =>
      if G.g y then K (G.σ y) (G.σ y) else 0) *
      K * Matrix.diagonal (fun y =>
      if G.g y then K (G.σ y) (G.σ y) else 0)) := by
  simpa [pow_zero, pow_one] using
    (trace_six_N_powers_boundary G K hK 1 1 1 1 1 1 0
      (by
        intro w w' hw hw' hcopy hne
        simpa [pow_one] using (hkg 1 (by omega) w w' hw hw' hcopy hne))
      (by
        intro w w' hw hw' hcopy hne
        simpa [pow_one] using (hkg 1 (by omega) w w' hw hw' hcopy hne))
      (by
        intro w w' hw hw' hcopy hne
        simpa [pow_one] using (hkg 1 (by omega) w w' hw hw' hcopy hne)))



/-- The complete even-stratum contribution at moment six, assembled with the
exact cyclic multiplicities. The lower two strata are expanded into their
boundary sums; the top stratum is retained as its exact diagonal-sandwich
trace. This is an assembly identity only: it makes no cancellation claim. -/
theorem trace_p6_all_even_strata_boundary {cp : W → ι}
    (G : GlueData cp) (K : Matrix W W ℂ) (hK : BD cp K)
    (hkg : ∀ n, n ≤ 5 → ∀ w w', G.g w → G.g w' → cp w = cp w' →
      w ≠ w' → (K ^ n) w w' = 0) :
    6 * Matrix.trace (K ^ 1 * G.N * K ^ 5 * G.N * K ^ 0) +
    6 * Matrix.trace (K ^ 2 * G.N * K ^ 4 * G.N * K ^ 0) +
    3 * Matrix.trace (K ^ 3 * G.N * K ^ 3 * G.N * K ^ 0) +
    6 * Matrix.trace (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 1 * G.N * K ^ 3 * G.N * K ^ 0) +
    6 * Matrix.trace (K ^ 1 * G.N * K ^ 1 * G.N * K ^ 2 * G.N * K ^ 2 * G.N * K ^ 0) +
    3 * Matrix.trace (K ^ 1 * G.N * K ^ 2 * G.N * K ^ 1 * G.N * K ^ 2 * G.N * K ^ 0) +
    Matrix.trace (K * G.N * K * G.N * K * G.N * K * G.N * K * G.N * K * G.N) =
    6 * (∑ x, if G.g x then
      (K ^ 1) x x * (K ^ 5) (G.σ x) (G.σ x) else 0) +
    6 * (∑ x, if G.g x then
      (K ^ 2) x x * (K ^ 4) (G.σ x) (G.σ x) else 0) +
    3 * (∑ x, if G.g x then
      (K ^ 3) x x * (K ^ 3) (G.σ x) (G.σ x) else 0) +
    6 * (∑ x, if G.g x then
      (K x x * (K ^ 1) (G.σ x) (G.σ x) * (K ^ 1) x x) *
        (K ^ 3) (G.σ x) (G.σ x) else 0) +
    6 * (∑ x, if G.g x then
      (K x x * (K ^ 1) (G.σ x) (G.σ x) * (K ^ 2) x x) *
        (K ^ 2) (G.σ x) (G.σ x) else 0) +
    3 * (∑ x, if G.g x then
      (K x x * (K ^ 2) (G.σ x) (G.σ x) * (K ^ 1) x x) *
        (K ^ 2) (G.σ x) (G.σ x) else 0) +
    Matrix.trace (K * Matrix.diagonal (fun y =>
      if G.g y then K (G.σ y) (G.σ y) else 0) *
      K * Matrix.diagonal (fun y =>
      if G.g y then K (G.σ y) (G.σ y) else 0) *
      K * Matrix.diagonal (fun y =>
      if G.g y then K (G.σ y) (G.σ y) else 0)) := by
  rw [trace_p6_lower_even_strata_boundary G K hK hkg,
    trace_p6_top_stratum_boundary G K hK hkg]


/-- Multiplication on the right by a diagonal matrix weights the diagonal
entries before taking the trace. -/
theorem trace_mul_diagonal_eq_sum (A : Matrix W W ℂ) (d : W → ℂ) :
    Matrix.trace (A * Matrix.diagonal d) = ∑ x, A x x * d x := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]


/-- A supported diagonal factor converts a diagonal-entry sum into a trace,
without expanding the matrix product that precedes it. -/
theorem trace_list_prod_mul_diagonal_supported_sum
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : X → Prop) [DecidablePred g]
    (M : List (Matrix X X ℂ)) (d : X → ℂ)
    (hd : ∀ x, ¬ g x → d x = 0) :
    Matrix.trace (M.prod * Matrix.diagonal d) =
      ∑ x, if g x then M.prod x x * d x else 0 := by
  classical
  have htrace :
      Matrix.trace (M.prod * Matrix.diagonal d) =
        ∑ x, M.prod x x * d x := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [htrace]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hg : g x
  · simp [hg]
  · simp [hg, hd x hg]


/-- Normalize the eight-factor list used by the p=8 boundary reduction.
Kept separate from the operator-specific theorem so Lean checks only this
short matrix-product identity here. -/
theorem prod_p8_alternating_kernel_diagonal_word
    {X : Type*} [Fintype X] [DecidableEq X]
    (K D : Matrix X X ℂ) :
    ([K ^ 0, K ^ 1, D, K ^ 1, D, K ^ 1, D, K ^ 1] :
      List (Matrix X X ℂ)).prod =
      K * D * K * D * K * D * K := by
  simp only [List.prod_cons, List.prod_nil, pow_zero, pow_one,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]


/-- Generic p=8 boundary-sum bridge. The supported sum is exactly the trace
of the alternating four-kernel/four-diagonal word; this theorem contains no
operator-specific hypotheses and does not assert that the trace collapses
further to a fourth-power sum. -/
theorem trace_p8_supported_boundary_sum_as_alternating_trace
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : X → Prop) [DecidablePred g]
    (K : Matrix X X ℂ) (d : X → ℂ)
    (hd : ∀ x, ¬ g x → d x = 0) :
    Matrix.trace
        (([K ^ 0, K ^ 1, Matrix.diagonal d, K ^ 1,
          Matrix.diagonal d, K ^ 1, Matrix.diagonal d, K ^ 1] :
          List (Matrix X X ℂ)).prod * Matrix.diagonal d) =
      ∑ x, if g x then
        (([K ^ 0, K ^ 1, Matrix.diagonal d, K ^ 1,
          Matrix.diagonal d, K ^ 1, Matrix.diagonal d, K ^ 1] :
          List (Matrix X X ℂ)).prod) x x * d x else 0 := by
  exact trace_list_prod_mul_diagonal_supported_sum g
    ([K ^ 0, K ^ 1, Matrix.diagonal d, K ^ 1,
      Matrix.diagonal d, K ^ 1, Matrix.diagonal d, K ^ 1] :
      List (Matrix X X ℂ)) d hd


/-- Reassociate the alternating eight-factor trace as a fourth power.
This is a purely algebraic normalization; it makes no claim about the
operator-specific boundary sum. -/
theorem trace_K_D_alternating_eight_eq_four
    {X : Type*} [Fintype X] [DecidableEq X]
    (K D : Matrix X X ℂ) :
    Matrix.trace (K * D * K * D * K * D * K * D) =
      Matrix.trace ((K * D) ^ 4) := by
  rw [pow_succ, pow_succ, pow_succ]
  simp only [pow_one, Matrix.mul_assoc]


/-- Combine the support restriction and matrix-word normalization: the
supported p=8 boundary sum is the fourth-power trace of the kernel-diagonal
product. This remains a generic algebraic identity, not an operator-specific
cancellation theorem. -/
theorem trace_p8_supported_boundary_sum_as_fourth_power
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : X → Prop) [DecidablePred g]
    (K : Matrix X X ℂ) (d : X → ℂ)
    (hd : ∀ x, ¬ g x → d x = 0) :
    (∑ x, if g x then
      (([K ^ 0, K ^ 1, Matrix.diagonal d, K ^ 1,
        Matrix.diagonal d, K ^ 1, Matrix.diagonal d, K ^ 1] :
        List (Matrix X X ℂ)).prod) x x * d x else 0) =
      Matrix.trace ((K * Matrix.diagonal d) ^ 4) := by
  calc
    (∑ x, if g x then
        (([K ^ 0, K ^ 1, Matrix.diagonal d, K ^ 1,
          Matrix.diagonal d, K ^ 1, Matrix.diagonal d, K ^ 1] :
          List (Matrix X X ℂ)).prod) x x * d x else 0)
        = Matrix.trace
            (([K ^ 0, K ^ 1, Matrix.diagonal d, K ^ 1,
              Matrix.diagonal d, K ^ 1, Matrix.diagonal d, K ^ 1] :
              List (Matrix X X ℂ)).prod * Matrix.diagonal d) := by
              symm
              exact trace_p8_supported_boundary_sum_as_alternating_trace
                g K d hd
    _ = Matrix.trace
          (K * Matrix.diagonal d * K * Matrix.diagonal d *
            K * Matrix.diagonal d * K * Matrix.diagonal d) := by
          rw [prod_p8_alternating_kernel_diagonal_word]
    _ = Matrix.trace ((K * Matrix.diagonal d) ^ 4) := by
          exact trace_K_D_alternating_eight_eq_four K (Matrix.diagonal d)


/-- Normalize the ten-factor list used by the p=10 boundary reduction.
The list contains five kernel factors and four explicit diagonal factors;
the final diagonal weight is supplied by right multiplication. -/
theorem prod_p10_alternating_kernel_diagonal_word
    {X : Type*} [Fintype X] [DecidableEq X]
    (K D : Matrix X X ℂ) :
    ([K ^ 0, K ^ 1, D, K ^ 1, D, K ^ 1, D, K ^ 1, D, K ^ 1] :
      List (Matrix X X ℂ)).prod =
      K * D * K * D * K * D * K * D * K := by
  simp only [List.prod_cons, List.prod_nil, pow_zero, pow_one,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]


/-- Reassociate the alternating ten-factor trace as a fifth power. -/
theorem trace_K_D_alternating_ten_eq_five
    {X : Type*} [Fintype X] [DecidableEq X]
    (K D : Matrix X X ℂ) :
    Matrix.trace (K * D * K * D * K * D * K * D * K * D) =
      Matrix.trace ((K * D) ^ 5) := by
  rw [pow_succ, pow_succ, pow_succ, pow_succ]
  simp only [pow_one, Matrix.mul_assoc]


/-- Convert a supported p=10 boundary sum to the fifth-power trace of
the kernel-diagonal product. This is an algebraic bridge only; it does not
claim cancellation with lower boundary strata. -/
theorem trace_p10_supported_boundary_sum_as_fifth_power
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : X → Prop) [DecidablePred g]
    (K : Matrix X X ℂ) (d : X → ℂ)
    (hd : ∀ x, ¬ g x → d x = 0) :
    (∑ x, if g x then
      (([K ^ 0, K ^ 1, Matrix.diagonal d, K ^ 1,
        Matrix.diagonal d, K ^ 1, Matrix.diagonal d, K ^ 1,
        Matrix.diagonal d, K ^ 1] : List (Matrix X X ℂ)).prod) x x * d x else 0) =
      Matrix.trace ((K * Matrix.diagonal d) ^ 5) := by
  calc
    (∑ x, if g x then
        (([K ^ 0, K ^ 1, Matrix.diagonal d, K ^ 1,
          Matrix.diagonal d, K ^ 1, Matrix.diagonal d, K ^ 1,
          Matrix.diagonal d, K ^ 1] : List (Matrix X X ℂ)).prod) x x * d x else 0)
        = Matrix.trace
            (([K ^ 0, K ^ 1, Matrix.diagonal d, K ^ 1,
              Matrix.diagonal d, K ^ 1, Matrix.diagonal d, K ^ 1,
              Matrix.diagonal d, K ^ 1] : List (Matrix X X ℂ)).prod *
              Matrix.diagonal d) := by
              symm
              exact trace_list_prod_mul_diagonal_supported_sum g
                ([K ^ 0, K ^ 1, Matrix.diagonal d, K ^ 1,
                  Matrix.diagonal d, K ^ 1, Matrix.diagonal d, K ^ 1,
                  Matrix.diagonal d, K ^ 1] : List (Matrix X X ℂ)) d hd
    _ = Matrix.trace
          (K * Matrix.diagonal d * K * Matrix.diagonal d *
            K * Matrix.diagonal d * K * Matrix.diagonal d *
            K * Matrix.diagonal d) := by
          rw [prod_p10_alternating_kernel_diagonal_word]
    _ = Matrix.trace ((K * Matrix.diagonal d) ^ 5) := by
          exact trace_K_D_alternating_ten_eq_five K (Matrix.diagonal d)

/-- The trace of a diagonal matrix is the finite sum of its diagonal weights. -/
theorem trace_diagonal_eq_sum (d : W → ℂ) :
    Matrix.trace (Matrix.diagonal d) = ∑ x, d x := by
  simp [Matrix.trace, Matrix.diagonal_apply]

/-- The trace of a product of two diagonal matrices is the sum
of the pointwise products of their weights. -/
theorem trace_diagonal_mul_diagonal_eq_sum (d e : W → ℂ) :
    Matrix.trace (Matrix.diagonal d * Matrix.diagonal e) =
      ∑ x, d x * e x := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

/-- Entrywise formula for a diagonal sandwich. -/
theorem diagonal_sandwich_apply
    (d : W → ℂ) (K : Matrix W W ℂ) (x y : W) :
    (Matrix.diagonal d * K * Matrix.diagonal d) x y =
      d x * K x y * d y := by
  classical
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

/-- If a diagonal weight is supported on a set on which K has no
off-diagonal entries, then sandwiching K by that weight is diagonal.
This is the local matrix fact needed to collapse the p=6 top boundary trace. -/
theorem diagonal_sandwich_offdiag_zero
    (g : W → Prop)
    (d : W → ℂ) (K : Matrix W W ℂ)
    (hd : ∀ x, ¬ g x → d x = 0)
    (hK : ∀ x y, g x → g y → x ≠ y → K x y = 0) :
    ∀ x y, x ≠ y →
      (Matrix.diagonal d * K * Matrix.diagonal d) x y = 0 := by
  classical
  intro x y hxy
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hx : g x
  · by_cases hy : g y
    · have hzero : K x y = 0 := hK x y hx hy hxy
      simp [hzero]
    · have hdy : d y = 0 := hd y hy
      simp [hdy]
  · have hdx : d x = 0 := hd x hx
    simp [hdx]


/-- Trace formula for a diagonal sandwich. The support of the diagonal weight
and off-diagonal vanishing of K on that support make the sandwich diagonal;
its trace is therefore the finite sum of its diagonal entries. -/
theorem trace_diagonal_sandwich_eq_sum
    (g : W → Prop) [DecidablePred g] (d : W → ℂ) (K : Matrix W W ℂ)
    (hd : ∀ x, ¬ g x → d x = 0)
    (hK : ∀ x y, g x → g y → x ≠ y → K x y = 0) :
    Matrix.trace (Matrix.diagonal d * K * Matrix.diagonal d) =
      ∑ x, if g x then d x * K x x * d x else 0 := by
  classical
  have hdiag :
      Matrix.diagonal d * K * Matrix.diagonal d =
        Matrix.diagonal (fun x => d x * K x x * d x) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      rw [Matrix.diagonal_apply]
      simp [diagonal_sandwich_apply]
    · rw [Matrix.diagonal_apply]
      simp only [if_neg hxy]
      exact diagonal_sandwich_offdiag_zero g d K hd hK x y hxy
  rw [hdiag, trace_diagonal_eq_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hg : g x
  · simp [hg]
  · simp [hg, hd x hg]



end GlueAlg

end EvgenyTheorem
