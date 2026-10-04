import EvgenyTheorem.VertexIndex

namespace EvgenyTheorem

theorem InSG_sum_le : ∀ (m x y : ℕ), InSG m x y → x + y ≤ 2 ^ m
  | 0, x, y, h => by simpa [InSG] using h
  | m + 1, x, y, h => by
    simp only [InSG] at h
    have ih := InSG_sum_le m
    have hp : 2 ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have := ih x y h3
      omega
    · have := ih (x - 2 ^ m) y h3
      omega
    · have := ih x (y - 2 ^ m) h3
      omega

/-- The list `vertexOrder m` is exactly the set of points of `SG(m)`. -/
theorem mem_vertexOrder_iff (m : ℕ) (p : Point) : p ∈ vertexOrder m ↔ InSG m p.1 p.2 := by
  induction m generalizing p with
  | zero =>
    obtain ⟨x, y⟩ := p
    simp [vertexOrder, InSG]
    omega
  | succ m ih =>
    rw [mem_vertexOrder_succ_iff]
    simp only [InSG]
    constructor
    · rintro (h | h | h)
      · have h' := (ih p).mp h
        have := InSG_sum_le m p.1 p.2 h'
        exact Or.inl ⟨by omega, by omega, h'⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
        have h' := (ih q).mp hq
        have := InSG_sum_le m q.1 q.2 h'
        refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
        · simp [shiftPoint]
        · simp only [shiftPoint]
          omega
        · simpa [shiftPoint] using h'
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
        have h' := (ih q).mp hq
        have := InSG_sum_le m q.1 q.2 h'
        refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
        · simp only [shiftPoint]
          omega
        · simp [shiftPoint]
        · simpa [shiftPoint] using h'
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact Or.inl ((ih p).mpr h3)
      · refine Or.inr (Or.inl (List.mem_map.mpr ⟨(p.1 - 2 ^ m, p.2), (ih _).mpr h3, ?_⟩))
        simp only [shiftPoint]
        ext <;> simp <;> omega
      · refine Or.inr (Or.inr (List.mem_map.mpr ⟨(p.1, p.2 - 2 ^ m), (ih _).mpr h3, ?_⟩))
        simp only [shiftPoint]
        ext <;> simp <;> omega

/-- Both endpoints of an edge lie in `SG(m)`'s bounding triangle. -/
theorem EdgeB_sound : ∀ (m x y X Y : ℕ), EdgeB m x y X Y = true →
    x + y ≤ 2 ^ m ∧ X + Y ≤ 2 ^ m
  | 0, x, y, X, Y, h => by
    simp [EdgeB] at h <;> omega
  | m + 1, x, y, X, Y, h => by
    simp only [EdgeB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := EdgeB_sound m
    have hp : 2 ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
    rcases h with (⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩) | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    · have := ih x y X Y h5
      omega
    · have := ih (x - 2 ^ m) y (X - 2 ^ m) Y h5
      omega
    · have := ih x (y - 2 ^ m) X (Y - 2 ^ m) h5
      omega

theorem EdgeB_irrefl_aux : ∀ (m x y : ℕ), EdgeB m x y x y = true → False
  | 0, x, y, h => by
    simp [EdgeB] at h <;> omega
  | m + 1, x, y, h => by
    simp only [EdgeB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with (⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩) | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    · exact EdgeB_irrefl_aux m x y h5
    · exact EdgeB_irrefl_aux m (x - 2 ^ m) y h5
    · exact EdgeB_irrefl_aux m x (y - 2 ^ m) h5

theorem EdgeB_irrefl (m x y : ℕ) : EdgeB m x y x y = false := by
  cases h : EdgeB m x y x y
  · rfl
  · exact (EdgeB_irrefl_aux m x y h).elim

end EvgenyTheorem
