import EvgenyTheorem.VertexOrder

namespace EvgenyTheorem

theorem mem_vertexOrder_succ_iff (m : ℕ) (z : Point) :
    z ∈ vertexOrder (m + 1) ↔
      z ∈ vertexOrder m ∨ z ∈ (vertexOrder m).map (shiftPoint (2 ^ m) 1 0) ∨
        z ∈ (vertexOrder m).map (shiftPoint (2 ^ m) 0 1) := by
  have e : vertexOrder (m + 1) =
      (vertexOrder m ++ (vertexOrder m).map (shiftPoint (2 ^ m) 1 0) ++
        (vertexOrder m).map (shiftPoint (2 ^ m) 0 1)).eraseDups := by
    first | rfl | simp [vertexOrder]
  rw [e, List.mem_eraseDups]
  simp [List.mem_append, or_assoc]

/-- All vertices lie in the triangle `x + y ≤ 2^m`. -/
theorem vertexOrder_sum_le (m : ℕ) : ∀ z ∈ vertexOrder m, z.1 + z.2 ≤ 2 ^ m := by
  induction m with
  | zero =>
    intro z hz
    simp [vertexOrder] at hz
    rcases hz with rfl | rfl | rfl <;> simp
  | succ m ih =>
    intro z hz
    rw [mem_vertexOrder_succ_iff] at hz
    rcases hz with hz | hz | hz
    · have h1 := ih z hz
      have h2 : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
      have h1 := ih q hq
      simp only [shiftPoint, pow_succ]
      omega
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
      have h1 := ih q hq
      simp only [shiftPoint, pow_succ]
      omega

theorem corner00_mem (m : ℕ) : ((0, 0) : Point) ∈ vertexOrder m := by
  induction m with
  | zero => simp [vertexOrder]
  | succ m ih => exact (mem_vertexOrder_succ_iff m _).mpr (Or.inl ih)

theorem cornerX_mem (m : ℕ) : ((2 ^ m, 0) : Point) ∈ vertexOrder m := by
  induction m with
  | zero => simp [vertexOrder]
  | succ m ih =>
    refine (mem_vertexOrder_succ_iff m _).mpr (Or.inr (Or.inl ?_))
    refine List.mem_map.mpr ⟨(2 ^ m, 0), ih, ?_⟩
    simp only [shiftPoint, pow_succ]
    ext <;> simp <;> omega

theorem cornerY_mem (m : ℕ) : ((0, 2 ^ m) : Point) ∈ vertexOrder m := by
  induction m with
  | zero => simp [vertexOrder]
  | succ m ih =>
    refine (mem_vertexOrder_succ_iff m _).mpr (Or.inr (Or.inr ?_))
    refine List.mem_map.mpr ⟨(0, 2 ^ m), ih, ?_⟩
    simp only [shiftPoint, pow_succ]
    ext <;> simp <;> omega

/-- Old vertices keep their index when passing from level `m` to level `m + 1`. -/
theorem vIdx_succ_of_mem {m : ℕ} {p : Point} (hp : p ∈ vertexOrder m) :
    vIdx (m + 1) p = vIdx m p := by
  unfold vIdx
  rw [vertexOrder_succ, List.idxOf_append_of_mem (List.mem_append_left _ hp),
    List.idxOf_append_of_mem hp]

end EvgenyTheorem
