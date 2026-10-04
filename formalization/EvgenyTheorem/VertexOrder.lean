import EvgenyTheorem.Orientation

namespace EvgenyTheorem

theorem eraseDups_of_nodup {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ l : List α, l.Nodup → l.eraseDups = l
  | [], _ => by simp
  | a :: as, h => by
    have h' := List.nodup_cons.mp h
    have hf : as.filter (fun b => !b == a) = as := by
      apply List.filter_eq_self.mpr
      intro b hb
      have hne : b ≠ a := fun e => h'.1 (e ▸ hb)
      simp [hne]
    rw [List.eraseDups_cons, hf, eraseDups_of_nodup as h'.2]

theorem nodup_eraseDups_aux {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → l.eraseDups.Nodup
  | 0, [], _ => by simp
  | 0, _ :: _, h => absurd h (by simp)
  | _ + 1, [], _ => by simp
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · rw [List.mem_eraseDups]
      simp
    · apply nodup_eraseDups_aux n
      exact le_trans (List.length_filter_le _ _) (by simpa using h)

theorem nodup_eraseDups {α : Type*} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Nodup :=
  nodup_eraseDups_aux l.length l le_rfl

theorem shiftPoint_injective (s dx dy : ℕ) : Function.Injective (shiftPoint s dx dy) := by
  intro p q h
  simp only [shiftPoint, Prod.mk.injEq] at h
  exact Prod.ext (by omega) (by omega)

theorem vertexOrder_nodup (m : ℕ) : (vertexOrder m).Nodup := by
  cases m with
  | zero => simp [vertexOrder]
  | succ m => exact nodup_eraseDups _

/-- Explicit form of `vertexOrder (m+1)`: the old list, then the new vertices of copy B,
then the new vertices of copy C. -/
theorem vertexOrder_succ (m : ℕ) :
    vertexOrder (m + 1) =
      vertexOrder m ++
        ((vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).removeAll (vertexOrder m) ++
        ((vertexOrder m).map (shiftPoint (2 ^ m) 0 1)).removeAll
          (vertexOrder m ++ (vertexOrder m).map (shiftPoint (2 ^ m) 1 0)) := by
  have hP := vertexOrder_nodup m
  have hB : ((vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).Nodup :=
    hP.map (shiftPoint_injective _ _ _)
  have hC : ((vertexOrder m).map (shiftPoint (2 ^ m) 0 1)).Nodup :=
    hP.map (shiftPoint_injective _ _ _)
  have hB' : (((vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).removeAll
      (vertexOrder m)).Nodup := by
    unfold List.removeAll
    exact hB.filter _
  have hC' : (((vertexOrder m).map (shiftPoint (2 ^ m) 0 1)).removeAll
      (vertexOrder m ++ (vertexOrder m).map (shiftPoint (2 ^ m) 1 0))).Nodup := by
    unfold List.removeAll
    exact hC.filter _
  have e : vertexOrder (m + 1) =
      (vertexOrder m ++ (vertexOrder m).map (shiftPoint (2 ^ m) 1 0) ++
        (vertexOrder m).map (shiftPoint (2 ^ m) 0 1)).eraseDups := by
    first | rfl | simp [vertexOrder]
  rw [e, List.eraseDups_append, List.eraseDups_append,
    eraseDups_of_nodup _ hP, eraseDups_of_nodup _ hB', eraseDups_of_nodup _ hC']

end EvgenyTheorem
