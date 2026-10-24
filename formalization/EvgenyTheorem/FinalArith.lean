import EvgenyTheorem.FinalOrient

namespace EvgenyTheorem

/-- Closed form of the defect from the two recursions and the two base values. -/
theorem defect_closed_form (D Dt : ℕ → ℂ) (s2 : ℂ)
    (h1 : D 1 = -32 * s2) (ht1 : Dt 1 = 0)
    (hD : ∀ m, 1 ≤ m → D (m + 1) = 2 * D m + Dt m)
    (hDt : ∀ m, 1 ≤ m → Dt (m + 1) = D m + 2 * Dt m) :
    ∀ m, 1 ≤ m →
      D m = -16 * ((3 : ℂ) ^ (m - 1) + 1) * s2 ∧
        Dt m = -16 * ((3 : ℂ) ^ (m - 1) - 1) * s2 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have h0 : (3 : ℂ) ^ (1 - 1) = 1 := by norm_num
    refine ⟨?_, ?_⟩
    · rw [h1, h0]; ring
    · rw [ht1, h0]; ring
  | succ n hn ih =>
    obtain ⟨a, b⟩ := ih
    have e : (3 : ℂ) ^ n = 3 * 3 ^ (n - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
    refine ⟨?_, ?_⟩
    · rw [hD n hn, a, b, Nat.add_sub_cancel, e]; ring
    · rw [hDt n hn, a, b, Nat.add_sub_cancel, e]; ring


/-- Closed form for any stabilized third-order growth law: if the
one-step residual `D (n+4) - 3 * D (n+3)` is constant, then the tail is
an affine function of `3^n`. This is the arithmetic bridge needed once a
moment-specific residual identity has been proved. -/
theorem affine_three_recurrence (D : ℕ → ℂ) (C : ℂ)
    (hrec : ∀ n, D (n + 4) = 3 * D (n + 3) + C) :
    ∀ n, D (n + 3) = (3 : ℂ) ^ n * (D 3 + C / 2) - C / 2 := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ← ih, hrec n]
      ring

end EvgenyTheorem
