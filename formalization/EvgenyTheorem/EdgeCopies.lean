import EvgenyTheorem.EdgeStep

namespace EvgenyTheorem

theorem EdgeB_succ_iff (m x y X Y : ℕ) :
    EdgeB (m + 1) x y X Y = true ↔
      (x ≤ 2 ^ m ∧ y ≤ 2 ^ m ∧ X ≤ 2 ^ m ∧ Y ≤ 2 ^ m ∧ EdgeB m x y X Y = true) ∨
      (2 ^ m ≤ x ∧ y ≤ 2 ^ m ∧ 2 ^ m ≤ X ∧ Y ≤ 2 ^ m ∧
        EdgeB m (x - 2 ^ m) y (X - 2 ^ m) Y = true) ∨
      (x ≤ 2 ^ m ∧ 2 ^ m ≤ y ∧ X ≤ 2 ^ m ∧ 2 ^ m ≤ Y ∧
        EdgeB m x (y - 2 ^ m) X (Y - 2 ^ m) = true) := by
  simp only [EdgeB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc, or_assoc]

/-- Copy A: points of `SG(m)` keep their adjacency at level `m+1`. -/
theorem EdgeB_copyA {m : ℕ} {p q : Point} (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) :
    EdgeB (m + 1) p.1 p.2 q.1 q.2 = EdgeB m p.1 p.2 q.1 q.2 := by
  have hp' := vertexOrder_sum_le m p hp
  have hq' := vertexOrder_sum_le m q hq
  rw [Bool.eq_iff_iff, EdgeB_succ_iff]
  constructor
  · rintro (⟨_, _, _, _, h⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩)
    · exact h
    · exfalso
      have e1 : p.1 = 2 ^ m := by omega
      have e2 : p.2 = 0 := by omega
      have e3 : q.1 = 2 ^ m := by omega
      have e4 : q.2 = 0 := by omega
      rw [e1, e2, e3, e4, Nat.sub_self, EdgeB_irrefl] at h5
      exact absurd h5 (by simp)
    · exfalso
      have e1 : p.1 = 0 := by omega
      have e2 : p.2 = 2 ^ m := by omega
      have e3 : q.1 = 0 := by omega
      have e4 : q.2 = 2 ^ m := by omega
      rw [e1, e2, e3, e4, Nat.sub_self, EdgeB_irrefl] at h5
      exact absurd h5 (by simp)
  · intro h
    exact Or.inl ⟨by omega, by omega, by omega, by omega, h⟩

/-- Copy B: shift by `(2^m, 0)`. -/
theorem EdgeB_copyB {m : ℕ} {p q : Point} (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) :
    EdgeB (m + 1) (p.1 + 2 ^ m) p.2 (q.1 + 2 ^ m) q.2 = EdgeB m p.1 p.2 q.1 q.2 := by
  have hp' := vertexOrder_sum_le m p hp
  have hq' := vertexOrder_sum_le m q hq
  rw [Bool.eq_iff_iff, EdgeB_succ_iff]
  constructor
  · rintro (⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩)
    · exfalso
      have hs := EdgeB_sound m _ _ _ _ h5
      have e1 : p.1 = 0 := by omega
      have e2 : p.2 = 0 := by omega
      have e3 : q.1 = 0 := by omega
      have e4 : q.2 = 0 := by omega
      rw [e1, e2, e3, e4, EdgeB_irrefl] at h5
      exact absurd h5 (by simp)
    · simpa using h5
    · exfalso
      have e1 : p.1 = 0 := by omega
      have e2 : p.2 = 2 ^ m := by omega
      have e3 : q.1 = 0 := by omega
      have e4 : q.2 = 2 ^ m := by omega
      rw [e1, e2, e3, e4, Nat.sub_self, EdgeB_irrefl] at h5
      exact absurd h5 (by simp)
  · intro h
    exact Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by simpa using h⟩)

/-- Copy C: shift by `(0, 2^m)`. -/
theorem EdgeB_copyC {m : ℕ} {p q : Point} (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) :
    EdgeB (m + 1) p.1 (p.2 + 2 ^ m) q.1 (q.2 + 2 ^ m) = EdgeB m p.1 p.2 q.1 q.2 := by
  have hp' := vertexOrder_sum_le m p hp
  have hq' := vertexOrder_sum_le m q hq
  rw [Bool.eq_iff_iff, EdgeB_succ_iff]
  constructor
  · rintro (⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩)
    · exfalso
      have hs := EdgeB_sound m _ _ _ _ h5
      have e1 : p.1 = 0 := by omega
      have e2 : p.2 = 0 := by omega
      have e3 : q.1 = 0 := by omega
      have e4 : q.2 = 0 := by omega
      rw [e1, e2, e3, e4, EdgeB_irrefl] at h5
      exact absurd h5 (by simp)
    · exfalso
      have e1 : p.1 = 2 ^ m := by omega
      have e2 : p.2 = 0 := by omega
      have e3 : q.1 = 2 ^ m := by omega
      have e4 : q.2 = 0 := by omega
      rw [e1, e2, e3, e4, Nat.sub_self, EdgeB_irrefl] at h5
      exact absurd h5 (by simp)
    · simpa using h5
  · intro h
    exact Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega, by simpa using h⟩)

end EvgenyTheorem
