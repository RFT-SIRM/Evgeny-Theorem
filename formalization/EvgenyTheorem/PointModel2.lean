import EvgenyTheorem.PointModel1
import EvgenyTheorem.Setup

namespace EvgenyTheorem

open Matrix

/-- Entry `(i, j)` of the `(p, q)` block of the operator, in terms of coordinates only.
It mirrors `connectionOperatorWithAxis`. -/
noncomputable def pHe (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (p q : Point) (i j : C2) : ℂ := by
  classical
  exact
    if p = q then
      if i = j then ((pdeg m p : ℕ) : ℂ) else 0
    else if EdgeB m p.1 p.2 q.1 q.2 = true then
      (let e : Point × Point := if p ≤ q then (p, q) else (q, p)
       let U := edgeUnitaryWithAxis m θ ax e
       if vIdx m p ≤ vIdx m q then -(U i j) else -(Uᴴ i j))
    else 0

/-- The points of `SG(m)` as a type. -/
abbrev Pt (m : ℕ) := ↥((vertexOrder m).toFinset)

noncomputable def pOp (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) :
    Matrix (Pt m × C2) (Pt m × C2) ℂ :=
  fun x y => pHe m θ ax x.1.1 y.1.1 x.2 y.2

noncomputable def eqPt (m : ℕ) : Vertex m ≃ Pt m :=
  Equiv.ofBijective
    (fun v => ⟨vpt v, List.mem_toFinset.mpr (vpt_mem v)⟩)
    ⟨fun a b h => vpt_injective m (congrArg Subtype.val h),
     fun ⟨p, hp⟩ => by
       obtain ⟨v, hv⟩ := exists_vpt (List.mem_toFinset.mp hp)
       exact ⟨v, Subtype.ext hv⟩⟩

noncomputable def eqPtC (m : ℕ) : HilbertIndex m ≃ Pt m × C2 :=
  (eqPt m).prodCongr (Equiv.refl C2)

theorem connOp_entry (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (u v : HilbertIndex m) :
    connectionOperatorWithAxis m θ ax u v =
      pHe m θ ax (vpt u.1) (vpt v.1) u.2 v.2 := by
  unfold connectionOperatorWithAxis
  refine ite_eq_of (fun h => ?pos) (fun h => ?neg)
  case pos =>
    have hp : vpt u.1 = vpt v.1 := by rw [h]
    unfold pHe
    rw [if_pos hp]
    refine ite_eq_of (fun h2 => ?_) (fun h2 => ?_)
    · rw [if_pos h2]
      simp [degree_eq_pdeg]
    · rw [if_neg h2]
  case neg =>
    have hne : vpt u.1 ≠ vpt v.1 := fun e => h (vpt_injective m e)
    unfold pHe
    rw [if_neg hne]
    refine ite_eq_of (fun hadj => ?_) (fun hadj => ?_)
    · have hE : EdgeB m (vpt u.1).1 (vpt u.1).2 (vpt v.1).1 (vpt v.1).2 = true := hadj
      rw [if_pos hE]
      rfl
    · have hE : ¬ (EdgeB m (vpt u.1).1 (vpt u.1).2 (vpt v.1).1 (vpt v.1).2 = true) := hadj
      rw [if_neg hE]

theorem connOp_eq_submatrix (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) :
    connectionOperatorWithAxis m θ ax = (pOp m θ ax).submatrix (eqPtC m) (eqPtC m) := by
  ext u v
  exact connOp_entry m θ ax u v

/-- `traceDefect` as the difference of two fourth-power traces (canonical instances). -/
theorem traceDefect_unfold (m : ℕ) (θ : ℝ) :
    traceDefect m θ =
      Matrix.trace (HC m θ * HC m θ * HC m θ * HC m θ) -
        Matrix.trace (HCprime m θ * HCprime m θ * HCprime m θ * HCprime m θ) := by
  unfold traceDefect
  congr <;> exact Subsingleton.elim _ _

theorem trace4_conn_eq (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) :
    Matrix.trace (connectionOperatorWithAxis m θ ax * connectionOperatorWithAxis m θ ax *
        connectionOperatorWithAxis m θ ax * connectionOperatorWithAxis m θ ax) =
      Matrix.trace (pOp m θ ax * pOp m θ ax * pOp m θ ax * pOp m θ ax) := by
  rw [connOp_eq_submatrix, ← tr4_reindex (eqPtC m) (pOp m θ ax)]

/-- **Point-level form of the trace defect.** -/
theorem traceDefect_pt (m : ℕ) (θ : ℝ) :
    traceDefect m θ =
      Matrix.trace (pOp m θ faceAxis * pOp m θ faceAxis * pOp m θ faceAxis *
          pOp m θ faceAxis) -
        Matrix.trace (pOp m θ (fun _ => 2) * pOp m θ (fun _ => 2) * pOp m θ (fun _ => 2) *
          pOp m θ (fun _ => 2)) := by
  rw [traceDefect_unfold]
  unfold HC HCprime
  rw [trace4_conn_eq, trace4_conn_eq]

end EvgenyTheorem
