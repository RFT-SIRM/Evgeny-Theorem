import EvgenyTheorem.FinalTheorem
import EvgenyTheorem.AlgebraTilde
import EvgenyTheorem.BaseCaseTheorem

namespace EvgenyTheorem

open Matrix

/-- `pHeO` depends on the orientation only through its value on the pair. -/
theorem pHeO_rel_congr (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o o' : Point → Point → Prop)
    [DecidableRel o] [DecidableRel o'] (p q : Point) (i j : C2) (h : o p q ↔ o' p q) :
    pHeO m θ ax o p q i j = pHeO m θ ax o' p q i j := by
  classical
  by_cases hpq : p = q
  · subst hpq
    rw [pHeO_diag, pHeO_diag]
  · by_cases hE : EdgeB m p.1 p.2 q.1 q.2 = true
    · rw [pHeO_edge_eq m θ ax o hpq hE, pHeO_edge_eq m θ ax o' hpq hE]
      by_cases ho : o p q
      · rw [if_pos ho, if_pos (h.mp ho)]
      · rw [if_neg ho, if_neg (fun h' => ho (h.mpr h'))]
    · rw [pHeO_zero_of_not_edge m θ ax o hpq hE, pHeO_zero_of_not_edge m θ ax o' hpq hE]

/-- Away from the corner pair, `oTil` and the numbering give the same matrix entry. -/
theorem pOpO_oTil_off (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (x y : Pt m × C2)
    (h1 : ¬ cp1 m x.1.1 y.1.1) (h2 : ¬ cp1 m y.1.1 x.1.1) :
    pOpO m θ ax (oTil m) x y = pOpO m θ ax (oNum m) x y := by
  show pHeO m θ ax (oTil m) x.1.1 y.1.1 x.2 y.2 = pHeO m θ ax (oNum m) x.1.1 y.1.1 x.2 y.2
  exact pHeO_rel_congr m θ ax _ _ _ _ _ _ (oTil_of_no_corner h1 h2)

theorem pOpO_oNum_eq_pOp (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) :
    pOpO m θ ax (oNum m) = pOp m θ ax := by
  funext x y
  show pHeO m θ ax (oNum m) x.1.1 y.1.1 x.2 y.2 = pHe m θ ax x.1.1 y.1.1 x.2 y.2
  rw [pHe_eq_pHeO m θ ax]
  exact pHeO_rel_congr m θ ax _ _ _ _ _ _ Iff.rfl

/-- Reindexing of the 12 basis states of `SG(1)` with spin onto `Pt 1 × C2`. -/
noncomputable def e12 : Fin 12 ≃ Pt 1 × C2 := eqv12.trans (eqPtC 1)

theorem sub_pOp (θ : ℝ) (ax : ℕ → Axis) :
    (pOp 1 θ ax).submatrix e12 e12 =
      (connectionOperatorWithAxis 1 θ ax).submatrix eqv12 eqv12 := by
  rw [connOp_eq_submatrix, Matrix.submatrix_submatrix]
  rfl

theorem sub_num_faceAxis (θ : ℝ) :
    (pOpO 1 θ faceAxis (oNum 1)).submatrix e12 e12 = HC12 (cC θ) (sC θ) Complex.I := by
  rw [pOpO_oNum_eq_pOp, sub_pOp]
  exact HC_sub θ

theorem sub_num_const2 (θ : ℝ) :
    (pOpO 1 θ (fun _ => 2) (oNum 1)).submatrix e12 e12 = HCp12 (cC θ) (sC θ) Complex.I := by
  rw [pOpO_oNum_eq_pOp, sub_pOp]
  exact HCprime_sub θ

/-- `Δ̃_1 = 0`, reduced to the two entrywise comparisons with the flipped matrices. -/
theorem tilde_base_of_entries (θ : ℝ)
    (h1 : ∀ a b : Fin 12, pOpO 1 θ faceAxis (oTil 1) (e12 a) (e12 b) =
      HCt12 (cC θ) (sC θ) Complex.I a b)
    (h2 : ∀ a b : Fin 12, pOpO 1 θ (fun _ => 2) (oTil 1) (e12 a) (e12 b) =
      HCtp12 (cC θ) (sC θ) Complex.I a b) :
    defectO 1 θ faceAxis (fun _ => 2) (oTil 1) = 0 := by
  have s1 : (pOpO 1 θ faceAxis (oTil 1)).submatrix e12 e12 =
      HCt12 (cC θ) (sC θ) Complex.I := by
    ext a b
    exact h1 a b
  have s2 : (pOpO 1 θ (fun _ => 2) (oTil 1)).submatrix e12 e12 =
      HCtp12 (cC θ) (sC θ) Complex.I := by
    ext a b
    exact h2 a b
  unfold defectO
  rw [tr4_reindex e12 (pOpO 1 θ faceAxis (oTil 1)),
    tr4_reindex e12 (pOpO 1 θ (fun _ => 2) (oTil 1)), s1, s2]
  exact alg_tilde _ _ _ Complex.I_sq

end EvgenyTheorem
