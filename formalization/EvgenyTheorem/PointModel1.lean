import EvgenyTheorem.BaseCaseTheorem
import EvgenyTheorem.SGStruct

namespace EvgenyTheorem

/-- Coordinates of a vertex of `SG(m)`. -/
def vpt {m : ℕ} (v : Vertex m) : Point := ((v.1.1 : ℕ), (v.1.2 : ℕ))

theorem vpt_injective (m : ℕ) : Function.Injective (@vpt m) := by
  intro u v h
  simp only [vpt, Prod.mk.injEq] at h
  apply Subtype.ext
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

theorem vpt_mem {m : ℕ} (v : Vertex m) : vpt v ∈ vertexOrder m :=
  (mem_vertexOrder_iff m _).mpr v.2

theorem exists_vpt {m : ℕ} {p : Point} (hp : p ∈ vertexOrder m) :
    ∃ v : Vertex m, vpt v = p := by
  have h := (mem_vertexOrder_iff m p).mp hp
  have hb := InSG_sum_le m p.1 p.2 h
  have h1 : p.1 < 2 ^ m + 1 := by omega
  have h2 : p.2 < 2 ^ m + 1 := by omega
  exact ⟨⟨(⟨p.1, h1⟩, ⟨p.2, h2⟩), h⟩, rfl⟩

theorem image_vpt_eq (m : ℕ) :
    (Finset.univ : Finset (Vertex m)).image vpt = (vertexOrder m).toFinset := by
  ext p
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨v, rfl⟩
    exact vpt_mem v
  · intro hp
    exact exists_vpt hp

/-- Sums over `Vertex m` are sums over the points of `vertexOrder m`. -/
theorem sum_vertex_eq_sum_points {m : ℕ} {β : Type*} [AddCommMonoid β] (f : Point → β) :
    ∑ v : Vertex m, f (vpt v) = ∑ p ∈ (vertexOrder m).toFinset, f p := by
  rw [← image_vpt_eq, Finset.sum_image (fun a _ b _ h => vpt_injective m h)]

theorem length_filter_eq_sum {α : Type*} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length = (l.map (fun q => if p q = true then 1 else 0)).sum
  | [] => by simp
  | a :: l => by
    have ih := length_filter_eq_sum p l
    by_cases h : p a = true
    · simp [List.filter_cons, h, ih]
      omega
    · simp [List.filter_cons, h, ih]

/-- Degree of a point of `SG(m)`, computed on the list of vertices. -/
def pdeg (m : ℕ) (p : Point) : ℕ :=
  ((vertexOrder m).filter (fun q => EdgeB m p.1 p.2 q.1 q.2)).length

theorem degree_eq_pdeg {m : ℕ} (u : Vertex m) : degree m u = pdeg m (vpt u) := by
  have hnd := vertexOrder_nodup m
  have hsum : ∑ v : Vertex m, (if Adj u v then 1 else 0) =
      ∑ q ∈ (vertexOrder m).toFinset,
        (if EdgeB m (vpt u).1 (vpt u).2 q.1 q.2 = true then 1 else 0) := by
    rw [← sum_vertex_eq_sum_points (m := m)
      (fun q => if EdgeB m (vpt u).1 (vpt u).2 q.1 q.2 = true then 1 else 0)]
    rfl
  unfold degree pdeg
  rw [hsum, List.sum_toFinset _ hnd, length_filter_eq_sum]

end EvgenyTheorem
