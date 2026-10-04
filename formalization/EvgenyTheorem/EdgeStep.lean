import EvgenyTheorem.SGStruct

namespace EvgenyTheorem

/-- The six neighbour directions of the triangular lattice. -/
def Step6 (x y X Y : ℕ) : Prop :=
  (X = x + 1 ∧ Y = y) ∨ (X = x ∧ Y = y + 1) ∨ (X = x + 1 ∧ y = Y + 1) ∨
  (x = X + 1 ∧ Y = y) ∨ (X = x ∧ y = Y + 1) ∨ (x = X + 1 ∧ Y = y + 1)

/-- Adjacent vertices of `SG(m)` are neighbours in the triangular lattice. -/
theorem EdgeB_step : ∀ (m x y X Y : ℕ), EdgeB m x y X Y = true → Step6 x y X Y
  | 0, x, y, X, Y, h => by
    simp [EdgeB] at h
    simp only [Step6]
    omega
  | m + 1, x, y, X, Y, h => by
    simp only [EdgeB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := EdgeB_step m
    rcases h with (⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩) |
        ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    · exact ih x y X Y h5
    · have := ih (x - 2 ^ m) y (X - 2 ^ m) Y h5
      simp only [Step6] at this ⊢
      omega
    · have := ih x (y - 2 ^ m) X (Y - 2 ^ m) h5
      simp only [Step6] at this ⊢
      omega

theorem EdgeB_dist {m x y X Y : ℕ} (h : EdgeB m x y X Y = true) :
    x ≤ X + 1 ∧ X ≤ x + 1 ∧ y ≤ Y + 1 ∧ Y ≤ y + 1 := by
  have := EdgeB_step m x y X Y h
  simp only [Step6] at this
  omega

/-- For `m ≥ 1` the three corners of `SG(m)` are pairwise non-adjacent. -/
theorem corners_not_adj {m : ℕ} (hm : 1 ≤ m) :
    EdgeB m 0 0 (2 ^ m) 0 = false ∧ EdgeB m 0 0 0 (2 ^ m) = false ∧
      EdgeB m (2 ^ m) 0 0 (2 ^ m) = false := by
  have hs2 : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨?_, ?_, ?_⟩ <;>
  · cases h : EdgeB m _ _ _ _
    · rfl
    · have := EdgeB_dist h
      omega

end EvgenyTheorem
