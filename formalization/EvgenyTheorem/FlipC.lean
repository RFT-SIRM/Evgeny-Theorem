import EvgenyTheorem.FlipB

namespace EvgenyTheorem

/-- A vertex of copy C already appears earlier (in part A or B) iff its preimage is a corner
`(0,0)` or `(2^m, 0)`. -/
theorem sC_mem_old_iff (m : ℕ) {a : Point} (ha : a ∈ vertexOrder m) :
    shiftPoint (2 ^ m) 0 1 a ∈ vertexOrder m ++ (vertexOrder m).map (shiftPoint (2 ^ m) 1 0) ↔
      a = (0, 0) ∨ a = (2 ^ m, 0) := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · left
      have h1 := vertexOrder_sum_le m _ h
      simp [shiftPoint] at h1
      ext <;> simp <;> omega
    · right
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp h
      have hq1 := vertexOrder_sum_le m q hq
      have hs := congrArg Prod.fst hqe
      have ht := congrArg Prod.snd hqe
      simp [shiftPoint] at hs ht
      have ha1 := vertexOrder_sum_le m a ha
      ext <;> simp <;> omega
  · rintro (rfl | rfl)
    · apply List.mem_append_left
      simpa [shiftPoint] using cornerY_mem m
    · apply List.mem_append_right
      refine List.mem_map.mpr ⟨(0, 2 ^ m), cornerY_mem m, ?_⟩
      simp [shiftPoint]

theorem not_mem_old_of_sC {m : ℕ} {a : Point} (ha : a ∈ vertexOrder m) (h0 : a ≠ (0, 0))
    (hs : a ≠ (2 ^ m, 0)) :
    shiftPoint (2 ^ m) 0 1 a ∉
      vertexOrder m ++ (vertexOrder m).map (shiftPoint (2 ^ m) 1 0) := by
  intro h
  rcases (sC_mem_old_iff m ha).mp h with h' | h'
  · exact h0 h'
  · exact hs h'

/-- Index of a new vertex of copy C. -/
theorem vIdx_succ_C {m : ℕ} {a : Point} (ha : a ∈ vertexOrder m) (h0 : a ≠ (0, 0))
    (hs : a ≠ (2 ^ m, 0)) :
    vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 a) =
      (vertexOrder m).length +
        (((vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).removeAll (vertexOrder m)).length +
        (((vertexOrder m).map (shiftPoint (2 ^ m) 0 1)).removeAll
          (vertexOrder m ++ (vertexOrder m).map (shiftPoint (2 ^ m) 1 0))).idxOf
          (shiftPoint (2 ^ m) 0 1 a) := by
  have hnot := not_mem_old_of_sC ha h0 hs
  have hnotX : shiftPoint (2 ^ m) 0 1 a ∉
      vertexOrder m ++ ((vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).removeAll
        (vertexOrder m) := by
    intro h
    rcases List.mem_append.mp h with h | h
    · exact hnot (List.mem_append_left _ h)
    · unfold List.removeAll at h
      exact hnot (List.mem_append_right _ (List.mem_filter.mp h).1)
  unfold vIdx
  rw [vertexOrder_succ, List.idxOf_append_of_notMem hnotX, List.length_append]

/-- Copy C preserves the relative order of its new vertices. -/
theorem vIdx_succ_C_lt_iff {m : ℕ} {a b : Point} (ha : a ∈ vertexOrder m)
    (hb : b ∈ vertexOrder m) (ha0 : a ≠ (0, 0)) (has : a ≠ (2 ^ m, 0))
    (hb0 : b ≠ (0, 0)) (hbs : b ≠ (2 ^ m, 0)) :
    vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 a) < vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 b) ↔
      vIdx m a < vIdx m b := by
  rw [vIdx_succ_C ha ha0 has, vIdx_succ_C hb hb0 hbs, Nat.add_lt_add_iff_left]
  have hnd : ((vertexOrder m).map (shiftPoint (2 ^ m) 0 1)).Nodup :=
    (vertexOrder_nodup m).map (shiftPoint_injective _ _ _)
  have hna := not_mem_old_of_sC ha ha0 has
  have hnb := not_mem_old_of_sC hb hb0 hbs
  unfold List.removeAll
  rw [idxOf_filter_lt_iff
    (fun z => !(vertexOrder m ++ (vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).elem z) _ hnd
    (shiftPoint (2 ^ m) 0 1 a) (shiftPoint (2 ^ m) 0 1 b)
    (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) (by simp [hna]) (by simp [hnb]),
    idxOf_map_inj (shiftPoint_injective _ _ _) (vertexOrder m) a,
    idxOf_map_inj (shiftPoint_injective _ _ _) (vertexOrder m) b]
  rfl

/-- Vertices of parts A and B have index below `|P| + |X'|`. -/
theorem vIdx_old_lt {m : ℕ} {z : Point}
    (hz : z ∈ vertexOrder m ++ (vertexOrder m).map (shiftPoint (2 ^ m) 1 0)) :
    vIdx (m + 1) z <
      (vertexOrder m).length +
        (((vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).removeAll (vertexOrder m)).length := by
  have hz' : z ∈ vertexOrder m ++
      ((vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).removeAll (vertexOrder m) := by
    by_cases hp : z ∈ vertexOrder m
    · exact List.mem_append_left _ hp
    · apply List.mem_append_right
      rcases List.mem_append.mp hz with h | h
      · exact absurd h hp
      · unfold List.removeAll
        rw [List.mem_filter]
        exact ⟨h, by simp [hp]⟩
  unfold vIdx
  rw [vertexOrder_succ, List.idxOf_append_of_mem hz']
  have := List.idxOf_lt_length_of_mem hz'
  rw [List.length_append] at this
  exact this

/-- New vertices of copy C have index at least `|P| + |X'|`. -/
theorem vIdx_C_ge {m : ℕ} {a : Point} (ha : a ∈ vertexOrder m) (h0 : a ≠ (0, 0))
    (hs : a ≠ (2 ^ m, 0)) :
    (vertexOrder m).length +
        (((vertexOrder m).map (shiftPoint (2 ^ m) 1 0)).removeAll (vertexOrder m)).length ≤
      vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 a) := by
  rw [vIdx_succ_C ha h0 hs]
  exact Nat.le_add_right _ _

/-- Copy C: the flipped faces are the old flipped ones, plus the face whose second endpoint is
the corner `(2^m, 0)`. -/
theorem C_flip_iff {m : ℕ} (hm : 1 ≤ m) {a b : Point} (ha : a ∈ vertexOrder m)
    (hb : b ∈ vertexOrder m) (h1 : b.1 = a.1 + 1) (h2 : b.2 = a.2) :
    vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 b) < vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 a) ↔
      (vIdx m b < vIdx m a ∨ b = (2 ^ m, 0)) := by
  have hs2 : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hbnd := vertexOrder_sum_le m b hb
  have hb0 : b ≠ (0, 0) := by
    intro h
    rw [h] at h1
    simp at h1
  by_cases ha0 : a = (0, 0)
  · subst ha0
    have hbs : b ≠ (2 ^ m, 0) := by
      intro h
      rw [h] at h1
      simp at h1
      omega
    have hold := vIdx_old_lt ((sC_mem_old_iff m ha).mpr (Or.inl rfl) |> fun h => h)
    have hge := vIdx_C_ge hb hb0 hbs
    have hLHS : ¬ (vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 b) <
        vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 (0, 0))) := by omega
    have hRHS : ¬ (vIdx m b < vIdx m (0, 0) ∨ b = (2 ^ m, 0)) := by
      rw [vIdx_origin]
      rintro (h | h)
      · omega
      · exact hbs h
    exact iff_of_false hLHS hRHS
  · by_cases hbs : b = (2 ^ m, 0)
    · subst hbs
      have has : a ≠ (2 ^ m, 0) := by
        intro h
        rw [h] at h1
        simp at h1
      have hold := vIdx_old_lt ((sC_mem_old_iff m hb).mpr (Or.inr rfl) |> fun h => h)
      have hge := vIdx_C_ge ha ha0 has
      exact iff_of_true (by omega) (Or.inr rfl)
    · have has : a ≠ (2 ^ m, 0) := by
        intro h
        rw [h] at h1
        simp at h1
        omega
      rw [vIdx_succ_C_lt_iff hb ha hb0 hbs ha0 has]
      constructor
      · intro h
        exact Or.inl h
      · rintro (h | h)
        · exact h
        · exact absurd h hbs

end EvgenyTheorem
