import EvgenyTheorem.GlueAlg

namespace EvgenyTheorem

open Matrix

section GlueBridge

variable {V W ι : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [DecidableEq ι]

/-- The "pushforward" matrix of a map `π : W → V`: `E v w = 1` iff `π w = v`. -/
def Emat (π : W → V) : Matrix V W ℂ := fun v w => if π w = v then 1 else 0

theorem EtE_apply (π : W → V) (w w' : W) :
    ((Emat π)ᵀ * Emat π) w w' = if π w = π w' then 1 else 0 := by
  rw [Matrix.mul_apply]
  have key : ∀ v : V, (Emat π)ᵀ w v * Emat π v w' = if π w = v ∧ π w' = v then 1 else 0 := by
    intro v
    simp only [Matrix.transpose_apply, Emat]
    by_cases h1 : π w = v <;> by_cases h2 : π w' = v <;> simp [h1, h2]
  simp only [key]
  by_cases h : π w = π w'
  · rw [if_pos h, Finset.sum_eq_single (π w)]
    · rw [if_pos ⟨rfl, h.symm⟩]
    · intro v _ hv
      rw [if_neg (by rintro ⟨h1, _⟩; exact hv h1.symm)]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun v _ => ?_)
    rw [if_neg (by rintro ⟨h1, h2⟩; exact h (h1.trans h2.symm))]

/-- `Eᵀ E = 1 + N` when the fibres of `π` are exactly the singletons and the glued pairs. -/
theorem EtE_eq_one_add_N {cp : W → ι} (G : GlueData cp) (π : W → V)
    (hπ : ∀ w w', π w = π w' ↔ (w = w' ∨ (G.g w ∧ w' = G.σ w))) :
    (Emat π)ᵀ * Emat π = 1 + G.N := by
  ext w w'
  rw [EtE_apply, Matrix.add_apply, Matrix.one_apply]
  simp only [GlueData.N]
  have hp := hπ w w'
  by_cases h1 : w = w'
  · have h2 : ¬ (G.g w ∧ w' = G.σ w) := by
      rintro ⟨hg, h⟩
      exact G.cp_σ w hg (by rw [← h, ← h1])
    have hpi : π w = π w' := hp.mpr (Or.inl h1)
    rw [if_pos hpi, if_pos h1, if_neg h2, add_zero]
  · by_cases h2 : (G.g w ∧ w' = G.σ w)
    · have hpi : π w = π w' := hp.mpr (Or.inr h2)
      rw [if_pos hpi, if_neg h1, if_pos h2, zero_add]
    · have hpi : ¬ π w = π w' := fun h => (hp.mp h).elim h1 h2
      rw [if_neg hpi, if_neg h1, if_neg h2, add_zero]

/-- Cyclic rearrangement: the fourth power of `E K Eᵀ` has the same trace as `(K (Eᵀ E))⁴`. -/
theorem trace4_sandwich (E : Matrix V W ℂ) (K : Matrix W W ℂ) :
    Matrix.trace ((E * K * Eᵀ) * (E * K * Eᵀ) * (E * K * Eᵀ) * (E * K * Eᵀ)) =
      Matrix.trace ((K * (Eᵀ * E)) * (K * (Eᵀ * E)) * (K * (Eᵀ * E)) * (K * (Eᵀ * E))) := by
  have e : (E * K * Eᵀ) * (E * K * Eᵀ) * (E * K * Eᵀ) * (E * K * Eᵀ) =
      E * ((K * (Eᵀ * E)) * (K * (Eᵀ * E)) * (K * (Eᵀ * E)) * K * Eᵀ) := by
    simp only [Matrix.mul_assoc]
  have e2 : (K * (Eᵀ * E)) * (K * (Eᵀ * E)) * (K * (Eᵀ * E)) * (K * (Eᵀ * E)) =
      ((K * (Eᵀ * E)) * (K * (Eᵀ * E)) * (K * (Eᵀ * E)) * K * Eᵀ) * E := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← e2]

theorem trace4_push {cp : W → ι} (G : GlueData cp) (π : W → V)
    (hπ : ∀ w w', π w = π w' ↔ (w = w' ∨ (G.g w ∧ w' = G.σ w)))
    (K : Matrix W W ℂ) :
    Matrix.trace ((Emat π * K * (Emat π)ᵀ) * (Emat π * K * (Emat π)ᵀ) *
        (Emat π * K * (Emat π)ᵀ) * (Emat π * K * (Emat π)ᵀ)) =
      Matrix.trace ((K + K * G.N) * (K + K * G.N) * (K + K * G.N) * (K + K * G.N)) := by
  have hKT : K * (1 + G.N) = K + K * G.N := by
    rw [Matrix.mul_add, Matrix.mul_one]
  rw [trace4_sandwich, EtE_eq_one_add_N G π hπ, hKT]

/-- **Pushforward gluing identity**: the fourth-power trace of `E K Eᵀ`, expressed through the
diagonal entries of `K, K², K³` at glued points. -/
theorem trace4_glue_formula {cp : W → ι} (G : GlueData cp) (π : W → V)
    (hπ : ∀ w w', π w = π w' ↔ (w = w' ∨ (G.g w ∧ w' = G.σ w)))
    (K : Matrix W W ℂ) (hbd : BD cp K)
    (hkg : ∀ w w', G.g w → G.g w' → cp w = cp w' → w ≠ w' → K w w' = 0)
    (hu2 : GlueDiag G (K * K)) :
    Matrix.trace ((Emat π * K * (Emat π)ᵀ) * (Emat π * K * (Emat π)ᵀ) *
        (Emat π * K * (Emat π)ᵀ) * (Emat π * K * (Emat π)ᵀ)) =
      Matrix.trace (K * K * K * K) +
        4 * ∑ a, (if G.g a then (K * K * K) a a * K (G.σ a) (G.σ a) else 0) +
        2 * ∑ a, (if G.g a then (K * K) a a * (K * K) (G.σ a) (G.σ a) else 0) +
        ∑ a, (if G.g a then K a a * K a a * (K (G.σ a) (G.σ a) * K (G.σ a) (G.σ a))
          else 0) := by
  rw [trace4_push G π hπ K]
  exact glue_trace4 G K hbd hkg hu2


/-- Rectangular cyclic-power identity.  It moves the final rectangular factor
through a power without assuming that either product is commutative. -/
theorem mul_pow_mul_left_rect {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : Matrix V W ℂ) (B : Matrix W V ℂ) (n : ℕ) :
    (A * B) ^ n * A = A * (B * A) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (A * B) ^ (n + 1) * A = ((A * B) ^ n * (A * B)) * A := by
          rw [pow_succ]
        _ = ((A * B) ^ n * A) * (B * A) := by
          simp only [Matrix.mul_assoc]
        _ = (A * (B * A) ^ n) * (B * A) := by
          rw [ih]
        _ = A * ((B * A) ^ n * (B * A)) := by
          simp only [Matrix.mul_assoc]
        _ = A * (B * A) ^ (n + 1) := by
          rw [pow_succ]

/-- For rectangular matrices A and B, the traces of (A B)^n and (B A)^n
agree for every natural power. This is the dimension-changing trace identity
needed to handle graph gluing at arbitrary moment order. -/
theorem trace_mul_pow_rect {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : Matrix V W ℂ) (B : Matrix W V ℂ) (n : ℕ) :
    Matrix.trace ((A * B) ^ n) = Matrix.trace ((B * A) ^ n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        Matrix.trace ((A * B) ^ n * (A * B)) =
            Matrix.trace (((A * B) ^ n * A) * B) := by
              simp only [Matrix.mul_assoc]
        _ = Matrix.trace (B * ((A * B) ^ n * A)) :=
              Matrix.trace_mul_comm _ _
        _ = Matrix.trace (B * (A * (B * A) ^ n)) := by
              rw [mul_pow_mul_left_rect]
        _ = Matrix.trace ((B * A) ^ (n + 1)) := by
              congr 1
              rw [← Matrix.mul_assoc, pow_succ]

/-- Arbitrary-power push-through identity for graph gluing. Unlike the former
fourth-power lemma, this holds for every natural moment order p. -/
theorem trace_sandwich_pow {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (E : Matrix V W ℂ) (K : Matrix W W ℂ) (p : ℕ) :
    Matrix.trace ((E * K * Eᵀ) ^ p) =
      Matrix.trace ((K * (Eᵀ * E)) ^ p) := by
  simpa [Matrix.mul_assoc] using
    (trace_mul_pow_rect E (K * Eᵀ) p)

end GlueBridge

end EvgenyTheorem
