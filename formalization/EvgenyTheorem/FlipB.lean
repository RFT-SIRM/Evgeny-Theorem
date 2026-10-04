import EvgenyTheorem.VertexIndex
import EvgenyTheorem.ListOrder

namespace EvgenyTheorem

theorem idxOf_map_inj {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {f : α → β} (hf : Function.Injective f) :
    ∀ (l : List α) (a : α), (l.map f).idxOf (f a) = l.idxOf a
  | [], a => by simp
  | x :: xs, a => by
    by_cases h : x = a
    · subst h
      simp
    · have h' : f x ≠ f a := fun e => h (hf e)
      rw [List.map_cons, List.idxOf_cons_ne _ h', List.idxOf_cons_ne _ h,
        idxOf_map_inj hf xs a]

theorem vertexOrder_head (m : ℕ) : (vertexOrder m).head? = some (0, 0) := by
  induction m with
  | zero => simp [vertexOrder]
  | succ m ih => simp [vertexOrder_succ, List.head?_append, ih]

theorem vertexOrder_eq_cons (m : ℕ) : ∃ rest, vertexOrder m = (0, 0) :: rest := by
  have h := vertexOrder_head m
  cases hl : vertexOrder m with
  | nil => rw [hl] at h; simp at h
  | cons x xs =>
    rw [hl] at h
    simp at h
    exact ⟨xs, by rw [h]⟩

theorem vIdx_origin (m : ℕ) : vIdx m (0, 0) = 0 := by
  obtain ⟨rest, h⟩ := vertexOrder_eq_cons m
  unfold vIdx
  rw [h]
  exact List.idxOf_cons_self

theorem vIdx_pos_of_ne {m : ℕ} {p : Point} (hp : p ≠ (0, 0)) : 0 < vIdx m p := by
  obtain ⟨rest, h⟩ := vertexOrder_eq_cons m
  unfold vIdx
  rw [h, List.idxOf_cons_ne _ (Ne.symm hp)]
  exact Nat.succ_pos _

theorem not_mem_shiftB (m : ℕ) {a : Point} (h0 : a ≠ (0, 0)) :
    shiftPoint (2 ^ m) 1 0 a ∉ vertexOrder m := by
  intro hmem
  have h1 := vertexOrder_sum_le m _ hmem
  simp [shiftPoint] at h1
  apply h0
  ext <;> simp <;> omega

/-- Index of a new vertex of copy B. -/
theorem vIdx_succ_B {m : ℕ} {a : Point} (ha : a ∈ vertexOrder m) (h0 : a ≠ (0, 0)) :
    vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 a) =
      (vertexOrder m).length +
        (((vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).removeAll (vertexOrder m)).idxOf
          (shiftPoint (2 ^ m) 1 0 a) := by
  have hnot := not_mem_shiftB m h0
  have hmemX : shiftPoint (2 ^ m) 1 0 a ∈
      ((vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).removeAll (vertexOrder m) := by
    unfold List.removeAll
    rw [List.mem_filter]
    exact ⟨List.mem_map_of_mem ha, by simp [hnot]⟩
  unfold vIdx
  rw [vertexOrder_succ, List.idxOf_append_of_mem (List.mem_append_right _ hmemX),
    List.idxOf_append_of_notMem hnot]

/-- Copy B preserves the relative order of all its new vertices. -/
theorem vIdx_succ_B_lt_iff {m : ℕ} {a b : Point} (ha : a ∈ vertexOrder m)
    (hb : b ∈ vertexOrder m) (ha0 : a ≠ (0, 0)) (hb0 : b ≠ (0, 0)) :
    vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 a) < vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 b) ↔
      vIdx m a < vIdx m b := by
  rw [vIdx_succ_B ha ha0, vIdx_succ_B hb hb0, Nat.add_lt_add_iff_left]
  have hnd : ((vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).Nodup :=
    (vertexOrder_nodup m).map (shiftPoint_injective _ _ _)
  have hna := not_mem_shiftB m ha0
  have hnb := not_mem_shiftB m hb0
  unfold List.removeAll
  rw [idxOf_filter_lt_iff (fun z => !(vertexOrder m).elem z) _ hnd
    (shiftPoint (2 ^ m) 1 0 a) (shiftPoint (2 ^ m) 1 0 b)
    (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) (by simp [hna]) (by simp [hnb]),
    idxOf_map_inj (shiftPoint_injective _ _ _) (vertexOrder m) a,
    idxOf_map_inj (shiftPoint_injective _ _ _) (vertexOrder m) b]
  rfl

end EvgenyTheorem
