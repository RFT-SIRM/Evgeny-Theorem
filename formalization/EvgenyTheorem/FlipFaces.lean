import EvgenyTheorem.FlipC

namespace EvgenyTheorem

theorem shiftPoint_zero' (s : ℕ) (p : Point) : shiftPoint s 0 0 p = p := by
  simp [shiftPoint]

theorem shiftFace_zero' (s : ℕ) (f : Face) : shiftFace s 0 0 f = f := by
  simp [shiftFace, shiftPoint]

/-- A face is flipped when the vertex numbering directs its flux edge against the +x direction. -/
def flippedP (m : ℕ) (f : Face) : Prop := vIdx m f.2.1 < vIdx m f.1

theorem face_endpoints_mem (m : ℕ) :
    ∀ f ∈ facesExact m, f.1 ∈ vertexOrder m ∧ f.2.1 ∈ vertexOrder m := by
  induction m with
  | zero =>
    intro f hf
    simp [facesExact] at hf
    subst hf
    simp [vertexOrder]
  | succ m ih =>
    intro f hf
    simp only [facesExact, List.mem_append, List.mem_map] at hf
    rcases hf with (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩
    · obtain ⟨h1, h2⟩ := ih g hg
      refine ⟨(mem_vertexOrder_succ_iff m _).mpr (Or.inl ?_),
        (mem_vertexOrder_succ_iff m _).mpr (Or.inl ?_)⟩
      · rw [shiftFace_zero']; exact h1
      · rw [shiftFace_zero']; exact h2
    · obtain ⟨h1, h2⟩ := ih g hg
      exact ⟨(mem_vertexOrder_succ_iff m _).mpr
          (Or.inr (Or.inl (List.mem_map.mpr ⟨g.1, h1, rfl⟩))),
        (mem_vertexOrder_succ_iff m _).mpr
          (Or.inr (Or.inl (List.mem_map.mpr ⟨g.2.1, h2, rfl⟩)))⟩
    · obtain ⟨h1, h2⟩ := ih g hg
      exact ⟨(mem_vertexOrder_succ_iff m _).mpr
          (Or.inr (Or.inr (List.mem_map.mpr ⟨g.1, h1, rfl⟩))),
        (mem_vertexOrder_succ_iff m _).mpr
          (Or.inr (Or.inr (List.mem_map.mpr ⟨g.2.1, h2, rfl⟩)))⟩

theorem bottom_mem (m : ℕ) : ∀ k, k ≤ 2 ^ m → ((k, 0) : Point) ∈ vertexOrder m := by
  induction m with
  | zero =>
    intro k hk
    have hk' : k = 0 ∨ k = 1 := by simp at hk; omega
    rcases hk' with rfl | rfl <;> simp [vertexOrder]
  | succ m ih =>
    intro k hk
    rw [mem_vertexOrder_succ_iff]
    by_cases h : k ≤ 2 ^ m
    · exact Or.inl (ih k h)
    · right
      left
      have hk2 : k ≤ 2 ^ m * 2 := by rw [pow_succ] at hk; exact hk
      refine List.mem_map.mpr ⟨(k - 2 ^ m, 0), ih _ (by omega), ?_⟩
      simp only [shiftPoint]
      ext <;> simp <;> omega

/-- Along the bottom edge the corner `(2^m, 0)` is numbered after `(2^m - 1, 0)`. -/
theorem bottom_lt : ∀ m, 1 ≤ m → vIdx m (2 ^ m - 1, 0) < vIdx m (2 ^ m, 0) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have h2 : 2 ≤ 2 ^ m :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hmem1 : ((2 ^ m - 1, 0) : Point) ∈ vertexOrder m := bottom_mem m _ (by omega)
    have hmem2 : ((2 ^ m, 0) : Point) ∈ vertexOrder m := bottom_mem m _ le_rfl
    have hne1 : ((2 ^ m - 1, 0) : Point) ≠ (0, 0) := by
      intro h
      simp at h
      omega
    have hne2 : ((2 ^ m, 0) : Point) ≠ (0, 0) := by
      intro h
      simp at h
    have e1 : ((2 ^ (m + 1) - 1, 0) : Point) = shiftPoint (2 ^ m) 1 0 (2 ^ m - 1, 0) := by
      simp only [shiftPoint, pow_succ]
      ext <;> simp <;> omega
    have e2 : ((2 ^ (m + 1), 0) : Point) = shiftPoint (2 ^ m) 1 0 (2 ^ m, 0) := by
      simp only [shiftPoint, pow_succ]
      ext <;> simp <;> omega
    rw [e1, e2, vIdx_succ_B_lt_iff hmem1 hmem2 hne1 hne2]
    exact ih

theorem flipped_A (m : ℕ) (f : Face) (hf : f ∈ facesExact m) :
    flippedP (m + 1) (shiftFace (2 ^ m) 0 0 f) ↔ flippedP m f := by
  obtain ⟨h1, h2⟩ := face_endpoints_mem m f hf
  rw [shiftFace_zero']
  unfold flippedP
  rw [vIdx_succ_of_mem h1, vIdx_succ_of_mem h2]

theorem flipped_B (m : ℕ) (f : Face) (hf : f ∈ facesExact m) :
    flippedP (m + 1) (shiftFace (2 ^ m) 1 0 f) ↔ flippedP m f := by
  obtain ⟨ha, hb⟩ := face_endpoints_mem m f hf
  obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
  have hb0 : f.2.1 ≠ (0, 0) := by
    intro h
    rw [h] at hs1
    simp at hs1
  unfold flippedP
  change vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.2.1) < vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.1) ↔
    vIdx m f.2.1 < vIdx m f.1
  by_cases ha0 : f.1 = (0, 0)
  · rw [ha0]
    have hold : shiftPoint (2 ^ m) 1 0 ((0, 0) : Point) ∈ vertexOrder m := by
      have := cornerX_mem m
      simpa [shiftPoint] using this
    have h1 : vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 (0, 0)) < (vertexOrder m).length := by
      rw [vIdx_succ_of_mem hold]
      exact List.idxOf_lt_length_of_mem hold
    have h2 : (vertexOrder m).length ≤ vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.2.1) := by
      rw [vIdx_succ_B hb hb0]
      exact Nat.le_add_right _ _
    have hLHS : ¬ (vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.2.1) <
        vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 (0, 0))) := by omega
    have hRHS : ¬ (vIdx m f.2.1 < vIdx m (0, 0)) := by
      rw [vIdx_origin]
      omega
    exact iff_of_false hLHS hRHS
  · exact vIdx_succ_B_lt_iff hb ha hb0 ha0

theorem flipped_C (m : ℕ) (hm : 1 ≤ m) (f : Face) (hf : f ∈ facesExact m) :
    flippedP (m + 1) (shiftFace (2 ^ m) 0 1 f) ↔ (flippedP m f ∨ f.2.1 = (2 ^ m, 0)) := by
  obtain ⟨ha, hb⟩ := face_endpoints_mem m f hf
  obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
  exact C_flip_iff hm ha hb hs1.symm hs2.symm

end EvgenyTheorem
