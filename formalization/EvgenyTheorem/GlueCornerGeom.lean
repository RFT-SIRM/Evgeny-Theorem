import EvgenyTheorem.GlueCornerSum
import EvgenyTheorem.CornerFaces

namespace EvgenyTheorem

open Matrix

theorem flux_horizontal {m : ℕ} {e : Point × Point} (he : e ∈ fluxEdges m) :
    e.1.1 + 1 = e.2.1 ∧ e.1.2 = e.2.2 := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  have h := flux_edge_order m f hf
  have h' : fluxEdge f = (f.1, f.2.1) := by simp [fluxEdge, h]
  rw [h']
  exact flux_edge_shape m f hf

theorem mem_flux_of_face {m : ℕ} {f : Face} (hf : f ∈ facesExact m) :
    (f.1, f.2.1) ∈ fluxEdges m := by
  have h := flux_edge_order m f hf
  have h' : fluxEdge f = (f.1, f.2.1) := by simp [fluxEdge, h]
  rw [← h']
  exact List.mem_map_of_mem hf

theorem not_flux_of_not_horiz (m a1 a2 b1 b2 : ℕ)
    (h1 : ¬ (a1 + 1 = b1 ∧ a2 = b2)) (h2 : ¬ (b1 + 1 = a1 ∧ b2 = a2)) :
    (if ((a1, a2) : Point) ≤ (b1, b2) then (((a1, a2) : Point), ((b1, b2) : Point))
      else (((b1, b2) : Point), ((a1, a2) : Point))) ∉ fluxEdges m := by
  intro h
  by_cases hab : ((a1, a2) : Point) ≤ (b1, b2)
  · rw [if_pos hab] at h
    exact h1 (flux_horizontal h)
  · rw [if_neg hab] at h
    exact h2 (flux_horizontal h)

open Classical in
/-- Exactly one of the three edges of the triangle `p q r` is a flux edge. -/
def OneFlux (m : ℕ) (p q r : Point) : Prop :=
  ((if p ≤ q then (p, q) else (q, p)) ∈ fluxEdges m ∧
      (if q ≤ r then (q, r) else (r, q)) ∉ fluxEdges m ∧
      (if r ≤ p then (r, p) else (p, r)) ∉ fluxEdges m) ∨
    ((if p ≤ q then (p, q) else (q, p)) ∉ fluxEdges m ∧
      (if q ≤ r then (q, r) else (r, q)) ∈ fluxEdges m ∧
      (if r ≤ p then (r, p) else (p, r)) ∉ fluxEdges m) ∨
    ((if p ≤ q then (p, q) else (q, p)) ∉ fluxEdges m ∧
      (if q ≤ r then (q, r) else (r, q)) ∉ fluxEdges m ∧
      (if r ≤ p then (r, p) else (p, r)) ∈ fluxEdges m)

/-- The corner data: `p` has exactly the neighbours `q`, `r`, which are adjacent. -/
def CornerNbrs (m : ℕ) (p q r : Point) : Prop :=
  q ∈ vertexOrder m ∧ r ∈ vertexOrder m ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    EdgeB m p.1 p.2 q.1 q.2 = true ∧ EdgeB m p.1 p.2 r.1 r.2 = true ∧
    EdgeB m q.1 q.2 r.1 r.2 = true ∧
    (∀ y ∈ vertexOrder m, EdgeB m p.1 p.2 y.1 y.2 = true → y = q ∨ y = r) ∧
    OneFlux m p q r

theorem corner_O (m : ℕ) : CornerNbrs m (0, 0) (1, 0) (0, 1) := by
  obtain ⟨f, hf, rfl⟩ := face_corner_O m
  obtain ⟨a1, a2, a3⟩ := face_adj m _ hf
  obtain ⟨v1, v2, v3⟩ := face_vertices_mem m _ hf
  have hle : ((0, 0) : Point) ≤ (1, 0) := Prod.mk_le_mk.mpr ⟨by norm_num, by norm_num⟩
  refine ⟨v2, v3, by decide, by decide, by decide, a1, a2, a3, ?_, ?_⟩
  · intro y hy hE
    rcases nbr_O hE with h | h
    · exact Or.inl h
    · exact Or.inr h
  · left
    refine ⟨?_, ?_, ?_⟩
    · rw [if_pos hle]
      exact mem_flux_of_face hf
    · exact not_flux_of_not_horiz m 1 0 0 1 (by omega) (by omega)
    · exact not_flux_of_not_horiz m 0 1 0 0 (by omega) (by omega)

theorem corner_X (m : ℕ) :
    CornerNbrs m (2 ^ m, 0) (2 ^ m - 1, 0) (2 ^ m - 1, 1) := by
  obtain ⟨f, hf, rfl⟩ := face_corner_X m
  obtain ⟨a1, a2, a3⟩ := face_adj m _ hf
  obtain ⟨v1, v2, v3⟩ := face_vertices_mem m _ hf
  have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hn : ¬ (((2 ^ m, 0) : Point) ≤ (2 ^ m - 1, 0)) := by
    intro h
    have := (Prod.mk_le_mk.mp h).1
    omega
  refine ⟨v1, v3, ?_, ?_, ?_, ?_, a3, a2, ?_, ?_⟩
  · intro h; rw [Prod.mk.injEq] at h; omega
  · intro h; rw [Prod.mk.injEq] at h; omega
  · intro h; rw [Prod.mk.injEq] at h; omega
  · rw [EdgeB_symm m]; exact a1
  · intro y hy hE
    rcases nbr_X hy hE with h | h
    · exact Or.inl h
    · exact Or.inr h
  · left
    refine ⟨?_, ?_, ?_⟩
    · rw [if_neg hn]
      exact mem_flux_of_face hf
    · exact not_flux_of_not_horiz m (2 ^ m - 1) 0 (2 ^ m - 1) 1 (by omega) (by omega)
    · exact not_flux_of_not_horiz m (2 ^ m - 1) 1 (2 ^ m) 0 (by omega) (by omega)

theorem corner_Y (m : ℕ) :
    CornerNbrs m (0, 2 ^ m) (0, 2 ^ m - 1) (1, 2 ^ m - 1) := by
  obtain ⟨f, hf, rfl⟩ := face_corner_Y m
  obtain ⟨a1, a2, a3⟩ := face_adj m _ hf
  obtain ⟨v1, v2, v3⟩ := face_vertices_mem m _ hf
  have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hle : ((0, 2 ^ m - 1) : Point) ≤ (1, 2 ^ m - 1) :=
    Prod.mk_le_mk.mpr ⟨by norm_num, le_refl _⟩
  refine ⟨v1, v2, ?_, ?_, ?_, ?_, ?_, a1, ?_, ?_⟩
  · intro h; rw [Prod.mk.injEq] at h; omega
  · intro h; rw [Prod.mk.injEq] at h; omega
  · intro h; rw [Prod.mk.injEq] at h; omega
  · rw [EdgeB_symm m]; exact a2
  · rw [EdgeB_symm m]; exact a3
  · intro y hy hE
    rcases nbr_Y hy hE with h | h
    · exact Or.inl h
    · exact Or.inr h
  · right; left
    refine ⟨?_, ?_, ?_⟩
    · exact not_flux_of_not_horiz m 0 (2 ^ m) 0 (2 ^ m - 1) (by omega) (by omega)
    · rw [if_pos hle]
      exact mem_flux_of_face hf
    · exact not_flux_of_not_horiz m 1 (2 ^ m - 1) 0 (2 ^ m) (by omega) (by omega)

end EvgenyTheorem
