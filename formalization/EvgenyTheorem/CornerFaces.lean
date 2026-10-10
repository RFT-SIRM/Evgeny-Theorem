import EvgenyTheorem.FluxSplit
import EvgenyTheorem.EdgeStep

namespace EvgenyTheorem

theorem face_vertices_mem (m : ℕ) :
    ∀ f ∈ facesExact m,
      f.1 ∈ vertexOrder m ∧ f.2.1 ∈ vertexOrder m ∧ f.2.2 ∈ vertexOrder m := by
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
    · obtain ⟨h1, h2, h3⟩ := ih g hg
      rw [shiftFace_zero']
      exact ⟨(mem_vertexOrder_succ_iff m _).mpr (Or.inl h1),
        (mem_vertexOrder_succ_iff m _).mpr (Or.inl h2),
        (mem_vertexOrder_succ_iff m _).mpr (Or.inl h3)⟩
    · obtain ⟨h1, h2, h3⟩ := ih g hg
      exact ⟨(mem_vertexOrder_succ_iff m _).mpr
          (Or.inr (Or.inl (List.mem_map.mpr ⟨g.1, h1, rfl⟩))),
        (mem_vertexOrder_succ_iff m _).mpr
          (Or.inr (Or.inl (List.mem_map.mpr ⟨g.2.1, h2, rfl⟩))),
        (mem_vertexOrder_succ_iff m _).mpr
          (Or.inr (Or.inl (List.mem_map.mpr ⟨g.2.2, h3, rfl⟩)))⟩
    · obtain ⟨h1, h2, h3⟩ := ih g hg
      exact ⟨(mem_vertexOrder_succ_iff m _).mpr
          (Or.inr (Or.inr (List.mem_map.mpr ⟨g.1, h1, rfl⟩))),
        (mem_vertexOrder_succ_iff m _).mpr
          (Or.inr (Or.inr (List.mem_map.mpr ⟨g.2.1, h2, rfl⟩))),
        (mem_vertexOrder_succ_iff m _).mpr
          (Or.inr (Or.inr (List.mem_map.mpr ⟨g.2.2, h3, rfl⟩)))⟩

/-- The three vertices of every face are pairwise adjacent. -/
theorem face_adj (m : ℕ) :
    ∀ f ∈ facesExact m,
      EdgeB m f.1.1 f.1.2 f.2.1.1 f.2.1.2 = true ∧
      EdgeB m f.1.1 f.1.2 f.2.2.1 f.2.2.2 = true ∧
      EdgeB m f.2.1.1 f.2.1.2 f.2.2.1 f.2.2.2 = true := by
  induction m with
  | zero =>
    intro f hf
    simp [facesExact] at hf
    subst hf
    decide
  | succ m ih =>
    intro f hf
    have hv := face_vertices_mem (m + 1) f hf
    simp only [facesExact, List.mem_append, List.mem_map] at hf
    rcases hf with (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩
    · obtain ⟨h1, h2, h3⟩ := face_vertices_mem m g hg
      obtain ⟨a1, a2, a3⟩ := ih g hg
      rw [shiftFace_zero']
      exact ⟨(EdgeB_copyA h1 h2).trans a1, (EdgeB_copyA h1 h3).trans a2,
        (EdgeB_copyA h2 h3).trans a3⟩
    · obtain ⟨h1, h2, h3⟩ := face_vertices_mem m g hg
      obtain ⟨a1, a2, a3⟩ := ih g hg
      refine ⟨?_, ?_, ?_⟩
      · simpa [shiftFace, shiftPoint] using (EdgeB_copyB h1 h2).trans a1
      · simpa [shiftFace, shiftPoint] using (EdgeB_copyB h1 h3).trans a2
      · simpa [shiftFace, shiftPoint] using (EdgeB_copyB h2 h3).trans a3
    · obtain ⟨h1, h2, h3⟩ := face_vertices_mem m g hg
      obtain ⟨a1, a2, a3⟩ := ih g hg
      refine ⟨?_, ?_, ?_⟩
      · simpa [shiftFace, shiftPoint] using (EdgeB_copyC h1 h2).trans a1
      · simpa [shiftFace, shiftPoint] using (EdgeB_copyC h1 h3).trans a2
      · simpa [shiftFace, shiftPoint] using (EdgeB_copyC h2 h3).trans a3

/-! ### The three corner faces -/

theorem face_corner_O (m : ℕ) :
    ∃ f ∈ facesExact m, f = (((0, 0) : Point), ((1, 0) : Point), ((0, 1) : Point)) := by
  induction m with
  | zero => exact ⟨_, by simp [facesExact], rfl⟩
  | succ m ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    refine ⟨shiftFace (2 ^ m) 0 0 (((0, 0) : Point), ((1, 0) : Point), ((0, 1) : Point)), ?_, ?_⟩
    · simp only [facesExact]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hf))
    · exact shiftFace_zero' _ _

theorem face_corner_X (m : ℕ) :
    ∃ f ∈ facesExact m,
      f = (((2 ^ m - 1, 0) : Point), ((2 ^ m, 0) : Point), ((2 ^ m - 1, 1) : Point)) := by
  induction m with
  | zero => exact ⟨(((0, 0) : Point), ((1, 0) : Point), ((0, 1) : Point)), by simp [facesExact], by simp⟩
  | succ m ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    refine ⟨shiftFace (2 ^ m) 1 0 (((2 ^ m - 1, 0) : Point), ((2 ^ m, 0) : Point),
      ((2 ^ m - 1, 1) : Point)), ?_, ?_⟩
    · simp only [facesExact]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hf))
    · simp only [shiftFace, shiftPoint, pow_succ]
      ext <;> simp <;> omega

theorem face_corner_Y (m : ℕ) :
    ∃ f ∈ facesExact m,
      f = (((0, 2 ^ m - 1) : Point), ((1, 2 ^ m - 1) : Point), ((0, 2 ^ m) : Point)) := by
  induction m with
  | zero => exact ⟨(((0, 0) : Point), ((1, 0) : Point), ((0, 1) : Point)), by simp [facesExact], by simp⟩
  | succ m ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    refine ⟨shiftFace (2 ^ m) 0 1 (((0, 2 ^ m - 1) : Point), ((1, 2 ^ m - 1) : Point),
      ((0, 2 ^ m) : Point)), ?_, ?_⟩
    · simp only [facesExact]
      exact List.mem_append_right _ (List.mem_map_of_mem hf)
    · simp only [shiftFace, shiftPoint, pow_succ]
      ext <;> simp <;> omega

/-! ### Neighbours of the corners -/

theorem nbr_O {m : ℕ} {r : Point} (h : EdgeB m 0 0 r.1 r.2 = true) :
    r = (1, 0) ∨ r = (0, 1) := by
  have := EdgeB_step m 0 0 r.1 r.2 h
  simp only [Step6] at this
  rcases r with ⟨x, y⟩
  simp only [Prod.mk.injEq]
  omega

theorem nbr_X {m : ℕ} {r : Point} (hr : r ∈ vertexOrder m)
    (h : EdgeB m (2 ^ m) 0 r.1 r.2 = true) :
    r = (2 ^ m - 1, 0) ∨ r = (2 ^ m - 1, 1) := by
  have h1 := EdgeB_step m (2 ^ m) 0 r.1 r.2 h
  have h2 := vertexOrder_sum_le m r hr
  have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  simp only [Step6] at h1
  rcases r with ⟨x, y⟩
  simp only [Prod.mk.injEq] at h2 ⊢
  omega

theorem nbr_Y {m : ℕ} {r : Point} (hr : r ∈ vertexOrder m)
    (h : EdgeB m 0 (2 ^ m) r.1 r.2 = true) :
    r = (0, 2 ^ m - 1) ∨ r = (1, 2 ^ m - 1) := by
  have h1 := EdgeB_step m 0 (2 ^ m) r.1 r.2 h
  have h2 := vertexOrder_sum_le m r hr
  have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  simp only [Step6] at h1
  rcases r with ⟨x, y⟩
  simp only [Prod.mk.injEq] at h2 ⊢
  omega

end EvgenyTheorem
