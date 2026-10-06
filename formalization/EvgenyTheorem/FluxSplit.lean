import EvgenyTheorem.DegSplit
import EvgenyTheorem.FlipFaces

namespace EvgenyTheorem

theorem shiftEdge_zero (s : ℕ) (e : Point × Point) : shiftEdge s 0 0 e = e := by
  simp [shiftEdge, shiftPoint]

theorem fluxEdges_succ (m : ℕ) :
    fluxEdges (m + 1) =
      (fluxEdges m).map (shiftEdge (2 ^ m) 0 0) ++ (fluxEdges m).map (shiftEdge (2 ^ m) 1 0) ++
        (fluxEdges m).map (shiftEdge (2 ^ m) 0 1) := by
  have e0 : List.map (fluxEdge ∘ shiftFace (2 ^ m) 0 0) (facesExact m) =
      List.map (shiftEdge (2 ^ m) 0 0 ∘ fluxEdge) (facesExact m) :=
    List.map_congr_left (fun f hf => fluxEdge_shift m 0 0 f hf)
  have e1 : List.map (fluxEdge ∘ shiftFace (2 ^ m) 1 0) (facesExact m) =
      List.map (shiftEdge (2 ^ m) 1 0 ∘ fluxEdge) (facesExact m) :=
    List.map_congr_left (fun f hf => fluxEdge_shift m 1 0 f hf)
  have e2 : List.map (fluxEdge ∘ shiftFace (2 ^ m) 0 1) (facesExact m) =
      List.map (shiftEdge (2 ^ m) 0 1 ∘ fluxEdge) (facesExact m) :=
    List.map_congr_left (fun f hf => fluxEdge_shift m 0 1 f hf)
  unfold fluxEdges
  simp only [facesExact, List.map_append, List.map_map]
  rw [e0, e1, e2]

theorem fluxIndex_eq_idxOf (m : ℕ) (e : Point × Point) :
    fluxIndex m e = (fluxEdges m).idxOf e := by
  unfold fluxIndex List.idxOf
  congr 1
  funext f
  first
    | rfl
    | simp
    | (rw [Bool.eq_iff_iff]; simp)

theorem fluxEdges_length (m : ℕ) : (fluxEdges m).length = 3 ^ m := by
  simp [fluxEdges, facesExact_length]

theorem fluxEdges_endpoints {m : ℕ} {e : Point × Point} (he : e ∈ fluxEdges m) :
    e.1 ∈ vertexOrder m ∧ e.2 ∈ vertexOrder m := by
  unfold fluxEdges at he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  have hle := flux_edge_order m f hf
  have hmem := face_endpoints_mem m f hf
  have h : fluxEdge f = (f.1, f.2.1) := by simp [fluxEdge, hle]
  rw [h]
  exact hmem

/-! ### Lattice facts about the copies -/

theorem sB_mem_imp {m : ℕ} {p : Point} (hp : p ∈ vertexOrder m)
    (h : shiftPoint (2 ^ m) 1 0 p ∈ vertexOrder m) : p = (0, 0) := by
  have h1 := vertexOrder_sum_le m p hp
  have h2 := vertexOrder_sum_le m _ h
  simp [shiftPoint] at h2
  ext <;> simp <;> omega

theorem sC_mem_imp {m : ℕ} {p : Point} (hp : p ∈ vertexOrder m)
    (h : shiftPoint (2 ^ m) 0 1 p ∈ vertexOrder m) : p = (0, 0) := by
  have h1 := vertexOrder_sum_le m p hp
  have h2 := vertexOrder_sum_le m _ h
  simp [shiftPoint] at h2
  ext <;> simp <;> omega

theorem sB_eq_sC {m : ℕ} {p q : Point} (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (h : shiftPoint (2 ^ m) 1 0 p = shiftPoint (2 ^ m) 0 1 q) :
    p = (0, 2 ^ m) ∧ q = (2 ^ m, 0) := by
  have h1 := vertexOrder_sum_le m p hp
  have h2 := vertexOrder_sum_le m q hq
  simp only [shiftPoint, Prod.mk.injEq] at h
  constructor
  · ext <;> simp <;> omega
  · ext <;> simp <;> omega

/-! ### Non-membership of shifted flux edges in earlier parts -/

theorem shiftB_not_mem_A {m : ℕ} {e : Point × Point} (he : e ∈ fluxEdges m) :
    shiftEdge (2 ^ m) 1 0 e ∉ (fluxEdges m).map (shiftEdge (2 ^ m) 0 0) := by
  intro h
  obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
  unfold fluxEdges at he he2
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he2
  rw [← fluxEdge_shift m 0 0 f hf, ← fluxEdge_shift m 1 0 g hg] at heq
  exact flux_block_disjoint_01 m f g hf hg heq

theorem shiftC_not_mem_A {m : ℕ} {e : Point × Point} (he : e ∈ fluxEdges m) :
    shiftEdge (2 ^ m) 0 1 e ∉ (fluxEdges m).map (shiftEdge (2 ^ m) 0 0) := by
  intro h
  obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
  unfold fluxEdges at he he2
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he2
  rw [← fluxEdge_shift m 0 0 f hf, ← fluxEdge_shift m 0 1 g hg] at heq
  exact flux_block_disjoint_02 m f g hf hg heq

theorem shiftC_not_mem_B {m : ℕ} {e : Point × Point} (he : e ∈ fluxEdges m) :
    shiftEdge (2 ^ m) 0 1 e ∉ (fluxEdges m).map (shiftEdge (2 ^ m) 1 0) := by
  intro h
  obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
  unfold fluxEdges at he he2
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he2
  rw [← fluxEdge_shift m 1 0 f hf, ← fluxEdge_shift m 0 1 g hg] at heq
  exact flux_block_disjoint_12 m f g hf hg heq

/-! ### Indices of flux edges in the three copies -/

theorem fluxIndex_succ_A {m : ℕ} {e : Point × Point} (he : e ∈ fluxEdges m) :
    fluxIndex (m + 1) e = fluxIndex m e := by
  rw [fluxIndex_eq_idxOf, fluxIndex_eq_idxOf, fluxEdges_succ]
  have hmem : e ∈ (fluxEdges m).map (shiftEdge (2 ^ m) 0 0) := by
    have := List.mem_map_of_mem (f := shiftEdge (2 ^ m) 0 0) he
    rwa [shiftEdge_zero] at this
  rw [List.idxOf_append_of_mem (List.mem_append_left _ hmem), List.idxOf_append_of_mem hmem]
  have := idxOf_map_inj (shiftEdge_injective (2 ^ m) 0 0) (fluxEdges m) e
  rw [shiftEdge_zero] at this
  exact this

theorem fluxIndex_succ_B {m : ℕ} {e : Point × Point} (he : e ∈ fluxEdges m) :
    fluxIndex (m + 1) (shiftEdge (2 ^ m) 1 0 e) = 3 ^ m + fluxIndex m e := by
  rw [fluxIndex_eq_idxOf, fluxIndex_eq_idxOf, fluxEdges_succ]
  have hmemB : shiftEdge (2 ^ m) 1 0 e ∈ (fluxEdges m).map (shiftEdge (2 ^ m) 1 0) :=
    List.mem_map_of_mem he
  rw [List.idxOf_append_of_mem (List.mem_append_right _ hmemB),
    List.idxOf_append_of_notMem (shiftB_not_mem_A he), List.length_map,
    idxOf_map_inj (shiftEdge_injective (2 ^ m) 1 0) (fluxEdges m) e, fluxEdges_length]

theorem fluxIndex_succ_C {m : ℕ} {e : Point × Point} (he : e ∈ fluxEdges m) :
    fluxIndex (m + 1) (shiftEdge (2 ^ m) 0 1 e) = 2 * 3 ^ m + fluxIndex m e := by
  rw [fluxIndex_eq_idxOf, fluxIndex_eq_idxOf, fluxEdges_succ]
  have hmemC : shiftEdge (2 ^ m) 0 1 e ∈ (fluxEdges m).map (shiftEdge (2 ^ m) 0 1) :=
    List.mem_map_of_mem he
  have hnot : shiftEdge (2 ^ m) 0 1 e ∉
      (fluxEdges m).map (shiftEdge (2 ^ m) 0 0) ++ (fluxEdges m).map (shiftEdge (2 ^ m) 1 0) := by
    intro h
    rcases List.mem_append.mp h with h | h
    · exact shiftC_not_mem_A he h
    · exact shiftC_not_mem_B he h
  rw [List.idxOf_append_of_notMem hnot, List.length_append, List.length_map, List.length_map,
    idxOf_map_inj (shiftEdge_injective (2 ^ m) 0 1) (fluxEdges m) e, fluxEdges_length]
  ring

/-! ### Membership criteria -/

theorem shiftB_mem_fluxEdges_succ_iff {m : ℕ} {p q : Point} (hp : p ∈ vertexOrder m)
    (hq : q ∈ vertexOrder m) (hpq : p ≠ q) :
    shiftEdge (2 ^ m) 1 0 (p, q) ∈ fluxEdges (m + 1) ↔ (p, q) ∈ fluxEdges m := by
  rw [fluxEdges_succ]
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · -- edge of copy A: both endpoints of the shifted edge lie in `V m`
        exfalso
        obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
        rw [shiftEdge_zero] at heq
        have hend := fluxEdges_endpoints (heq ▸ he2)
        have hp' := sB_mem_imp hp hend.1
        have hq' := sB_mem_imp hq hend.2
        exact hpq (hp'.trans hq'.symm)
      · obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
        have := shiftEdge_injective (2 ^ m) 1 0 heq
        rw [← this]
        exact he2
    · exfalso
      obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
      have hend := fluxEdges_endpoints he2
      have e1 : shiftPoint (2 ^ m) 0 1 e2.1 = shiftPoint (2 ^ m) 1 0 p := by
        have := congrArg Prod.fst heq
        simpa [shiftEdge] using this
      have e2' : shiftPoint (2 ^ m) 0 1 e2.2 = shiftPoint (2 ^ m) 1 0 q := by
        have := congrArg Prod.snd heq
        simpa [shiftEdge] using this
      have a1 := sB_eq_sC hp hend.1 e1.symm
      have a2 := sB_eq_sC hq hend.2 e2'.symm
      exact hpq (a1.1.trans a2.1.symm)
  · intro h
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem h))

theorem shiftC_mem_fluxEdges_succ_iff {m : ℕ} {p q : Point} (hp : p ∈ vertexOrder m)
    (hq : q ∈ vertexOrder m) (hpq : p ≠ q) :
    shiftEdge (2 ^ m) 0 1 (p, q) ∈ fluxEdges (m + 1) ↔ (p, q) ∈ fluxEdges m := by
  rw [fluxEdges_succ]
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exfalso
        obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
        rw [shiftEdge_zero] at heq
        have hend := fluxEdges_endpoints (heq ▸ he2)
        have hp' := sC_mem_imp hp hend.1
        have hq' := sC_mem_imp hq hend.2
        exact hpq (hp'.trans hq'.symm)
      · exfalso
        obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
        have hend := fluxEdges_endpoints he2
        have e1 : shiftPoint (2 ^ m) 1 0 e2.1 = shiftPoint (2 ^ m) 0 1 p := by
          have := congrArg Prod.fst heq
          simpa [shiftEdge] using this
        have e2' : shiftPoint (2 ^ m) 1 0 e2.2 = shiftPoint (2 ^ m) 0 1 q := by
          have := congrArg Prod.snd heq
          simpa [shiftEdge] using this
        have a1 := sB_eq_sC hend.1 hp e1
        have a2 := sB_eq_sC hend.2 hq e2'
        exact hpq (a1.2.trans a2.2.symm)
    · obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
      have := shiftEdge_injective (2 ^ m) 0 1 heq
      rw [← this]
      exact he2
  · intro h
    exact List.mem_append_right _ (List.mem_map_of_mem h)

theorem shiftA_mem_fluxEdges_succ_iff {m : ℕ} {p q : Point} (hp : p ∈ vertexOrder m)
    (hq : q ∈ vertexOrder m) (hpq : p ≠ q) :
    (p, q) ∈ fluxEdges (m + 1) ↔ (p, q) ∈ fluxEdges m := by
  rw [fluxEdges_succ]
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
        rw [shiftEdge_zero] at heq
        rw [← heq]
        exact he2
      · exfalso
        obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
        have hend := fluxEdges_endpoints he2
        have e1 : shiftPoint (2 ^ m) 1 0 e2.1 = p := by
          have := congrArg Prod.fst heq
          simpa [shiftEdge] using this
        have e2' : shiftPoint (2 ^ m) 1 0 e2.2 = q := by
          have := congrArg Prod.snd heq
          simpa [shiftEdge] using this
        have a1 := sB_mem_imp hend.1 (e1 ▸ hp)
        have a2 := sB_mem_imp hend.2 (e2' ▸ hq)
        apply hpq
        rw [← e1, ← e2', a1, a2]
    · exfalso
      obtain ⟨e2, he2, heq⟩ := List.mem_map.mp h
      have hend := fluxEdges_endpoints he2
      have e1 : shiftPoint (2 ^ m) 0 1 e2.1 = p := by
        have := congrArg Prod.fst heq
        simpa [shiftEdge] using this
      have e2' : shiftPoint (2 ^ m) 0 1 e2.2 = q := by
        have := congrArg Prod.snd heq
        simpa [shiftEdge] using this
      have a1 := sC_mem_imp hend.1 (e1 ▸ hp)
      have a2 := sC_mem_imp hend.2 (e2' ▸ hq)
      apply hpq
      rw [← e1, ← e2', a1, a2]
  · intro h
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    have := List.mem_map_of_mem (f := shiftEdge (2 ^ m) 0 0) h
    rwa [shiftEdge_zero] at this

end EvgenyTheorem
