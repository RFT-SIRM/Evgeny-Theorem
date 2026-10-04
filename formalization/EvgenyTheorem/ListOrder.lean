import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Basic

namespace EvgenyTheorem

/-- Filtering a list without repeats preserves the relative order of the kept elements. -/
theorem idxOf_filter_lt_iff {α : Type*} [BEq α] [LawfulBEq α] (p : α → Bool) :
    ∀ (l : List α), l.Nodup → ∀ a b, a ∈ l → b ∈ l → p a = true → p b = true →
      ((l.filter p).idxOf a < (l.filter p).idxOf b ↔ l.idxOf a < l.idxOf b)
  | [], _, a, _, ha, _, _, _ => by simp at ha
  | x :: xs, hnd, a, b, ha, hb, pa, pb => by
    have hx := List.nodup_cons.mp hnd
    by_cases hpx : p x = true
    · have hf : (x :: xs).filter p = x :: xs.filter p := by
        simp [List.filter_cons, hpx]
      rw [hf]
      by_cases hax : x = a
      · subst hax
        by_cases hbx : x = b
        · subst hbx
          simp
        · rw [List.idxOf_cons_eq _ rfl, List.idxOf_cons_eq _ rfl,
            List.idxOf_cons_ne _ hbx, List.idxOf_cons_ne _ hbx]
          simp
      · by_cases hbx : x = b
        · subst hbx
          rw [List.idxOf_cons_eq _ rfl, List.idxOf_cons_eq _ rfl]
          simp
        · have ha' : a ∈ xs := by
            rcases List.mem_cons.mp ha with h | h
            · exact absurd h.symm hax
            · exact h
          have hb' : b ∈ xs := by
            rcases List.mem_cons.mp hb with h | h
            · exact absurd h.symm hbx
            · exact h
          rw [List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hbx,
            List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hbx]
          have ih := idxOf_filter_lt_iff p xs hx.2 a b ha' hb' pa pb
          simpa using ih
    · have hf : (x :: xs).filter p = xs.filter p := by
        simp [List.filter_cons, hpx]
      rw [hf]
      have hax : x ≠ a := fun h => by subst h; exact hpx pa
      have hbx : x ≠ b := fun h => by subst h; exact hpx pb
      have ha' : a ∈ xs := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hax
        · exact h
      have hb' : b ∈ xs := by
        rcases List.mem_cons.mp hb with h | h
        · exact absurd h.symm hbx
        · exact h
      rw [List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hbx]
      have ih := idxOf_filter_lt_iff p xs hx.2 a b ha' hb' pa pb
      rw [ih]
      simp

end EvgenyTheorem
