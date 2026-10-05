import EvgenyTheorem.EdgeCopies

namespace EvgenyTheorem

/-- Both endpoints of an edge belong to `SG(m)`. -/
theorem EdgeB_mem : ∀ (m x y X Y : ℕ), EdgeB m x y X Y = true →
    InSG m x y ∧ InSG m X Y
  | 0, x, y, X, Y, h => by
    simp [EdgeB] at h
    simp only [InSG]
    omega
  | m + 1, x, y, X, Y, h => by
    simp only [EdgeB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := EdgeB_mem m
    simp only [InSG]
    rcases h with (⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩) |
        ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    · obtain ⟨a, b⟩ := ih x y X Y h5
      exact ⟨Or.inl ⟨h1, h2, a⟩, Or.inl ⟨h3, h4, b⟩⟩
    · obtain ⟨a, b⟩ := ih (x - 2 ^ m) y (X - 2 ^ m) Y h5
      exact ⟨Or.inr (Or.inl ⟨h1, h2, a⟩), Or.inr (Or.inl ⟨h3, h4, b⟩)⟩
    · obtain ⟨a, b⟩ := ih x (y - 2 ^ m) X (Y - 2 ^ m) h5
      exact ⟨Or.inr (Or.inr ⟨h1, h2, a⟩), Or.inr (Or.inr ⟨h3, h4, b⟩)⟩

/-- Edge of copy A (no shift). -/
def DA (m : ℕ) (z z' : Point) : Prop :=
  z.1 ≤ 2 ^ m ∧ z.2 ≤ 2 ^ m ∧ z'.1 ≤ 2 ^ m ∧ z'.2 ≤ 2 ^ m ∧
    EdgeB m z.1 z.2 z'.1 z'.2 = true

/-- Edge of copy B (shift `(2^m, 0)`). -/
def DB (m : ℕ) (z z' : Point) : Prop :=
  2 ^ m ≤ z.1 ∧ z.2 ≤ 2 ^ m ∧ 2 ^ m ≤ z'.1 ∧ z'.2 ≤ 2 ^ m ∧
    EdgeB m (z.1 - 2 ^ m) z.2 (z'.1 - 2 ^ m) z'.2 = true

/-- Edge of copy C (shift `(0, 2^m)`). -/
def DC (m : ℕ) (z z' : Point) : Prop :=
  z.1 ≤ 2 ^ m ∧ 2 ^ m ≤ z.2 ∧ z'.1 ≤ 2 ^ m ∧ 2 ^ m ≤ z'.2 ∧
    EdgeB m z.1 (z.2 - 2 ^ m) z'.1 (z'.2 - 2 ^ m) = true

instance (m : ℕ) (z z' : Point) : Decidable (DA m z z') := by unfold DA; infer_instance
instance (m : ℕ) (z z' : Point) : Decidable (DB m z z') := by unfold DB; infer_instance
instance (m : ℕ) (z z' : Point) : Decidable (DC m z z') := by unfold DC; infer_instance

theorem EdgeB_succ_DABC (m : ℕ) (z z' : Point) :
    EdgeB (m + 1) z.1 z.2 z'.1 z'.2 = true ↔ DA m z z' ∨ DB m z z' ∨ DC m z z' :=
  EdgeB_succ_iff m z.1 z.2 z'.1 z'.2

theorem not_DA_DB (m : ℕ) (z z' : Point) : ¬ (DA m z z' ∧ DB m z z') := by
  rintro ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4, b5⟩⟩
  have hs := EdgeB_sound m _ _ _ _ a5
  have e1 : z.1 = 2 ^ m := by omega
  have e2 : z.2 = 0 := by omega
  have e3 : z'.1 = 2 ^ m := by omega
  have e4 : z'.2 = 0 := by omega
  rw [e1, e2, e3, e4, EdgeB_irrefl] at a5
  exact absurd a5 (by simp)

theorem not_DA_DC (m : ℕ) (z z' : Point) : ¬ (DA m z z' ∧ DC m z z') := by
  rintro ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4, b5⟩⟩
  have hs := EdgeB_sound m _ _ _ _ a5
  have e1 : z.1 = 0 := by omega
  have e2 : z.2 = 2 ^ m := by omega
  have e3 : z'.1 = 0 := by omega
  have e4 : z'.2 = 2 ^ m := by omega
  rw [e1, e2, e3, e4, EdgeB_irrefl] at a5
  exact absurd a5 (by simp)

theorem not_DB_DC (m : ℕ) (z z' : Point) : ¬ (DB m z z' ∧ DC m z z') := by
  rintro ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4, b5⟩⟩
  have e1 : z.1 = 2 ^ m := by omega
  have e2 : z.2 = 2 ^ m := by omega
  have e3 : z'.1 = 2 ^ m := by omega
  have e4 : z'.2 = 2 ^ m := by omega
  rw [e1, e2, e3, e4, Nat.sub_self, EdgeB_irrefl] at a5
  exact absurd a5 (by simp)

/-- The edge indicator of level `m+1` is the sum of the three copy indicators. -/
theorem ind_succ (m : ℕ) (z z' : Point) :
    (if EdgeB (m + 1) z.1 z.2 z'.1 z'.2 = true then 1 else 0 : ℕ) =
      (if DA m z z' then 1 else 0) + (if DB m z z' then 1 else 0) +
        (if DC m z z' then 1 else 0) := by
  have key := EdgeB_succ_DABC m z z'
  by_cases hA : DA m z z'
  · have hB : ¬ DB m z z' := fun h => not_DA_DB m z z' ⟨hA, h⟩
    have hC : ¬ DC m z z' := fun h => not_DA_DC m z z' ⟨hA, h⟩
    have hE : EdgeB (m + 1) z.1 z.2 z'.1 z'.2 = true := key.mpr (Or.inl hA)
    simp [hA, hB, hC, hE]
  · by_cases hB : DB m z z'
    · have hC : ¬ DC m z z' := fun h => not_DB_DC m z z' ⟨hB, h⟩
      have hE : EdgeB (m + 1) z.1 z.2 z'.1 z'.2 = true := key.mpr (Or.inr (Or.inl hB))
      simp [hA, hB, hC, hE]
    · by_cases hC : DC m z z'
      · have hE : EdgeB (m + 1) z.1 z.2 z'.1 z'.2 = true := key.mpr (Or.inr (Or.inr hC))
        simp [hA, hB, hC, hE]
      · have hE : ¬ (EdgeB (m + 1) z.1 z.2 z'.1 z'.2 = true) := by
          intro h
          rcases key.mp h with h | h | h <;> contradiction
        simp [hA, hB, hC, hE]

end EvgenyTheorem
