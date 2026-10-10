import EvgenyTheorem.OpSplit3
import EvgenyTheorem.Locality

namespace EvgenyTheorem

open Matrix

theorem fluxEdges_le {m : ℕ} {e : Point × Point} (he : e ∈ fluxEdges m) : e.1 ≤ e.2 := by
  unfold fluxEdges at he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  have h := flux_edge_order m f hf
  have h' : fluxEdge f = (f.1, f.2.1) := by simp [fluxEdge, h]
  rw [h']
  exact h

open Classical in
/-- Sorting the two endpoints of an edge in either order gives the same edge unitary. -/
theorem edgeU_swap (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (p q : Point) :
    edgeUnitaryWithAxis m θ ax (if q ≤ p then (q, p) else (p, q)) =
      edgeUnitaryWithAxis m θ ax (if p ≤ q then (p, q) else (q, p)) := by
  by_cases h1 : p ≤ q <;> by_cases h2 : q ≤ p
  · have hpq : p = q := le_antisymm h1 h2
    subst hpq
    rfl
  · rw [if_neg h2, if_pos h1]
  · rw [if_pos h2, if_neg h1]
  · rw [if_neg h2, if_neg h1]
    have n1 : (p, q) ∉ fluxEdges m := fun h => h1 (fluxEdges_le h)
    have n2 : (q, p) ∉ fluxEdges m := fun h => h2 (fluxEdges_le h)
    unfold edgeUnitaryWithAxis
    rw [if_neg n1, if_neg n2]

open Classical in
theorem pHeO_edge_eq (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    {p q : Point} (hpq : p ≠ q) (hE : EdgeB m p.1 p.2 q.1 q.2 = true) (i k : C2) :
    pHeO m θ ax o p q i k =
      if o p q then
        -(edgeUnitaryWithAxis m θ ax (if p ≤ q then (p, q) else (q, p)) i k)
      else
        -((edgeUnitaryWithAxis m θ ax (if p ≤ q then (p, q) else (q, p)))ᴴ i k) := by
  unfold pHeO
  rw [if_neg hpq, if_pos hE]

open Classical in
/-- For an antisymmetric orientation, the two blocks of an edge multiply to the identity. -/
theorem pHeO_edge_mul (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    {p q : Point} (hpq : p ≠ q) (hanti : o p q ↔ ¬ o q p) (hE : EdgeB m p.1 p.2 q.1 q.2 = true) (i j : C2) :
    ∑ k : C2, pHeO m θ ax o p q i k * pHeO m θ ax o q p k j = if i = j then 1 else 0 := by
  have hqp : q ≠ p := hpq.symm
  have hE' : EdgeB m q.1 q.2 p.1 p.2 = true := by
    rw [EdgeB_symm m]
    exact hE
  have e1 := pHeO_edge_eq m θ ax o hpq hE
  have e2 := pHeO_edge_eq m θ ax o hqp hE'
  have hsw := edgeU_swap m θ ax p q
  rw [hsw] at e2
  have hUU := edgeUnitaryWithAxis_mul_conjTranspose m θ ax (if p ≤ q then (p, q) else (q, p))
  have hUU' := edgeUnitaryWithAxis_conjTranspose_mul m θ ax (if p ≤ q then (p, q) else (q, p))
  generalize edgeUnitaryWithAxis m θ ax (if p ≤ q then (p, q) else (q, p)) = U at e1 e2 hUU hUU'
  simp only [e1, e2]
  have ho := hanti
  by_cases h : o p q
  · have h' : ¬ o q p := ho.mp h
    simp only [if_pos h, if_neg h']
    have hs : ∑ k : C2, (-(U i k)) * (-(Uᴴ k j)) = (U * Uᴴ) i j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun k _ => neg_mul_neg _ _)
    rw [hs, hUU, Matrix.one_apply]
  · have h' : o q p := by
      by_contra hc
      exact h (ho.mpr hc)
    simp only [if_neg h, if_pos h']
    have hs : ∑ k : C2, (-(Uᴴ i k)) * (-(U k j)) = (Uᴴ * U) i j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun k _ => neg_mul_neg _ _)
    rw [hs, hUU', Matrix.one_apply]

end EvgenyTheorem
