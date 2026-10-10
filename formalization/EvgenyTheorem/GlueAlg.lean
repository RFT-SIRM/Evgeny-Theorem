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
  uniq : ∀ w w', g w → g w' → cp w = cp w' → cp (σ w) = cp (σ w') → w = w'

attribute [instance] GlueData.dg

/-- The pairing matrix. -/
noncomputable def GlueData.N {cp : W → ι} (G : GlueData cp) : Matrix W W ℂ :=
  fun w a => if G.g w ∧ a = G.σ w then 1 else 0

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

theorem trace_XNXN {cp : W → ι} (G : GlueData cp) {X : Matrix W W ℂ} (hX : BD cp X) :
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
            · exfalso
              apply hc
              have hu := G.uniq a (G.σ c) ga (G.g_σ c gc) h1 (by rw [G.σσ c gc]; exact h2.symm)
              rw [← G.σσ c gc, ← hu]
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

/-- **Gluing identity.** -/
theorem glue_trace4 {cp : W → ι} (G : GlueData cp) (K : Matrix W W ℂ) (hbd : BD cp K)
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → K w w' = 0) :
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
  have r2 := trace_XNXN G hK2
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

end GlueAlg

end EvgenyTheorem
