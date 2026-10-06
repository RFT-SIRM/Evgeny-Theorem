import EvgenyTheorem.FluxSplit
import EvgenyTheorem.PointModel2

namespace EvgenyTheorem

open Matrix

/-! ### Orientation-parametrized entries -/

/-- Entry of the point-level operator with an arbitrary orientation relation `o`. -/
noncomputable def pHeO (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (p q : Point) (i j : C2) : ℂ := by
  classical
  exact
    if p = q then
      if i = j then ((pdeg m p : ℕ) : ℂ) else 0
    else if EdgeB m p.1 p.2 q.1 q.2 = true then
      (let e : Point × Point := if p ≤ q then (p, q) else (q, p)
       let U := edgeUnitaryWithAxis m θ ax e
       if o p q then -(U i j) else -(Uᴴ i j))
    else 0

theorem pHe_eq_pHeO (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (p q : Point) (i j : C2) :
    pHe m θ ax p q i j = pHeO m θ ax (fun p q => vIdx m p ≤ vIdx m q) p q i j := by
  unfold pHe pHeO
  rfl

/-- Orientation of copy A (no shift), induced by the numbering at level `m+1`. -/
def oA (m : ℕ) (p q : Point) : Prop := vIdx (m + 1) p ≤ vIdx (m + 1) q
/-- Orientation of copy B. -/
def oB (m : ℕ) (p q : Point) : Prop :=
  vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 p) ≤ vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 q)
/-- Orientation of copy C. -/
def oC (m : ℕ) (p q : Point) : Prop :=
  vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 p) ≤ vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 q)

instance (m : ℕ) : DecidableRel (oA m) := fun p q => by unfold oA; infer_instance
instance (m : ℕ) : DecidableRel (oB m) := fun p q => by unfold oB; infer_instance
instance (m : ℕ) : DecidableRel (oC m) := fun p q => by unfold oC; infer_instance

/-! ### Axis periodicity -/

theorem faceAxis_shift3 (a k : ℕ) : faceAxis (3 * a + k) = faceAxis k := by
  apply Fin.ext
  show (3 * a + k) % 3 = k % 3
  omega

theorem faceAxis_pow (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    faceAxis (3 ^ m + k) = faceAxis k ∧ faceAxis (2 * 3 ^ m + k) = faceAxis k := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h : 3 ^ (m' + 1) = 3 * 3 ^ m' := by rw [pow_succ]; ring
  rw [h]
  constructor
  · exact faceAxis_shift3 _ _
  · have : 2 * (3 * 3 ^ m') + k = 3 * (2 * 3 ^ m') + k := by ring
    rw [this]
    exact faceAxis_shift3 _ _

/-! ### Transport of edge unitaries to the copies -/

theorem U_succ_A {m : ℕ} (θ : ℝ) (ax : ℕ → Axis) (e : Point × Point)
    (h1 : e.1 ∈ vertexOrder m) (h2 : e.2 ∈ vertexOrder m) (hne : e.1 ≠ e.2) :
    edgeUnitaryWithAxis (m + 1) θ ax e = edgeUnitaryWithAxis m θ ax e := by
  unfold edgeUnitaryWithAxis
  have hiff : e ∈ fluxEdges (m + 1) ↔ e ∈ fluxEdges m := by
    have := shiftA_mem_fluxEdges_succ_iff h1 h2 hne
    simpa using this
  by_cases hm : e ∈ fluxEdges m
  · rw [if_pos (hiff.mpr hm), if_pos hm, fluxIndex_succ_A hm]
  · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm]

theorem U_succ_B {m : ℕ} (θ : ℝ) (ax : ℕ → Axis) (hax : ∀ k, ax (3 ^ m + k) = ax k)
    (e : Point × Point)
    (h1 : e.1 ∈ vertexOrder m) (h2 : e.2 ∈ vertexOrder m) (hne : e.1 ≠ e.2) :
    edgeUnitaryWithAxis (m + 1) θ ax (shiftEdge (2 ^ m) 1 0 e) =
      edgeUnitaryWithAxis m θ ax e := by
  unfold edgeUnitaryWithAxis
  have hiff : shiftEdge (2 ^ m) 1 0 e ∈ fluxEdges (m + 1) ↔ e ∈ fluxEdges m := by
    have := shiftB_mem_fluxEdges_succ_iff h1 h2 hne
    simpa using this
  by_cases hm : e ∈ fluxEdges m
  · rw [if_pos (hiff.mpr hm), if_pos hm, fluxIndex_succ_B hm, hax]
  · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm]

theorem U_succ_C {m : ℕ} (θ : ℝ) (ax : ℕ → Axis) (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (e : Point × Point)
    (h1 : e.1 ∈ vertexOrder m) (h2 : e.2 ∈ vertexOrder m) (hne : e.1 ≠ e.2) :
    edgeUnitaryWithAxis (m + 1) θ ax (shiftEdge (2 ^ m) 0 1 e) =
      edgeUnitaryWithAxis m θ ax e := by
  unfold edgeUnitaryWithAxis
  have hiff : shiftEdge (2 ^ m) 0 1 e ∈ fluxEdges (m + 1) ↔ e ∈ fluxEdges m := by
    have := shiftC_mem_fluxEdges_succ_iff h1 h2 hne
    simpa using this
  by_cases hm : e ∈ fluxEdges m
  · rw [if_pos (hiff.mpr hm), if_pos hm, fluxIndex_succ_C hm, hax]
  · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm]

/-! ### Sorting an edge commutes with shifting -/

open Classical in
theorem sortE_shift (s dx dy : ℕ) (p q : Point) :
    (if shiftPoint s dx dy p ≤ shiftPoint s dx dy q then
        (shiftPoint s dx dy p, shiftPoint s dx dy q)
      else (shiftPoint s dx dy q, shiftPoint s dx dy p)) =
      shiftEdge s dx dy (if p ≤ q then (p, q) else (q, p)) := by
  by_cases h : p ≤ q
  · have h' : shiftPoint s dx dy p ≤ shiftPoint s dx dy q := by
      rw [Prod.le_def] at h ⊢
      simp only [shiftPoint]
      omega
    rw [if_pos h', if_pos h]
    rfl
  · have h' : ¬ shiftPoint s dx dy p ≤ shiftPoint s dx dy q := by
      rw [Prod.le_def] at h ⊢
      simp only [shiftPoint]
      omega
    rw [if_neg h', if_neg h]
    rfl

end EvgenyTheorem
