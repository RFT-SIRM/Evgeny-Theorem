import EvgenyTheorem.TildeBase

set_option maxHeartbeats 200000

namespace EvgenyTheorem

open Matrix

def pt12 : Fin 12 → Point :=
  ![(0, 0), (0, 0), (1, 0), (1, 0), (0, 1), (0, 1), (2, 0), (2, 0), (1, 1), (1, 1), (0, 2), (0, 2)]

/-- Index pairs of the flipped corner edge `(1,0)–(2,0)`. -/
def isC (a b : Fin 12) : Prop :=
  ((a.val = 2 ∨ a.val = 3) ∧ (b.val = 6 ∨ b.val = 7)) ∨
    ((a.val = 6 ∨ a.val = 7) ∧ (b.val = 2 ∨ b.val = 3))

/-- Swap of the two corner points, spin kept. -/
def sw : Fin 12 → Fin 12 := ![0, 1, 6, 7, 4, 5, 2, 3, 8, 9, 10, 11]

theorem e12_pt (a : Fin 12) : (e12 a).1.1 = pt12 a := by
  fin_cases a <;> rfl

theorem corner_iff (a b : Fin 12) :
    (cp1 1 (pt12 a) (pt12 b) ∨ cp1 1 (pt12 b) (pt12 a)) ↔ isC a b := by
  unfold cp1 isC pt12
  fin_cases a <;> fin_cases b <;> decide

theorem sw_facts : ∀ a b : Fin 12, isC a b →
    (e12 (sw a)).1.1 = (e12 b).1.1 ∧ (e12 (sw b)).1.1 = (e12 a).1.1 ∧
      (e12 (sw a)).2 = (e12 a).2 ∧ (e12 (sw b)).2 = (e12 b).2 := by
  intro a b
  fin_cases a <;> fin_cases b <;> intro hC <;>
    first
      | exact absurd hC (by unfold isC; decide)
      | exact ⟨rfl, rfl, rfl, rfl⟩

theorem corner_pHeO (θ : ℝ) (ax : ℕ → Axis) (i j : C2) :
    pHeO 1 θ ax (oTil 1) (1, 0) (2, 0) i j = pHeO 1 θ ax (oNum 1) (2, 0) (1, 0) i j ∧
    pHeO 1 θ ax (oTil 1) (2, 0) (1, 0) i j = pHeO 1 θ ax (oNum 1) (1, 0) (2, 0) i j := by
  classical
  have hne : ((1, 0) : Point) ≠ ((2, 0) : Point) := by decide
  have hE : EdgeB 1 1 0 2 0 = true := by decide
  have hE' : EdgeB 1 2 0 1 0 = true := by decide
  have sw1 := edgeU_swap 1 θ ax (1, 0) (2, 0)
  have o1 : ¬ oTil 1 (1, 0) (2, 0) := by unfold oTil cp1 oNum; decide
  have o2 : ¬ oNum 1 (2, 0) (1, 0) := by unfold oNum; decide
  have o3 : oTil 1 (2, 0) (1, 0) := by unfold oTil cp1 oNum; decide
  have o4 : oNum 1 (1, 0) (2, 0) := by unfold oNum; decide
  constructor
  · rw [pHeO_edge_eq 1 θ ax _ hne hE, pHeO_edge_eq 1 θ ax _ hne.symm hE', sw1,
      if_neg o1, if_neg o2]
  · rw [pHeO_edge_eq 1 θ ax _ hne.symm hE', pHeO_edge_eq 1 θ ax _ hne hE, sw1,
      if_pos o3, if_pos o4]

theorem corner_entry_pt (θ : ℝ) (ax : ℕ → Axis) (x y : Pt 1 × C2)
    (h : cp1 1 x.1.1 y.1.1 ∨ cp1 1 y.1.1 x.1.1) :
    pOpO 1 θ ax (oTil 1) x y = pHeO 1 θ ax (oNum 1) y.1.1 x.1.1 x.2 y.2 := by
  show pHeO 1 θ ax (oTil 1) x.1.1 y.1.1 x.2 y.2 = _
  have key := corner_pHeO θ ax x.2 y.2
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : x.1.1 = (1, 0) := h1.trans (by norm_num)
    have e2 : y.1.1 = (2, 0) := h2.trans (by norm_num)
    rw [e1, e2]
    exact key.1
  · have e1 : y.1.1 = (1, 0) := h1.trans (by norm_num)
    have e2 : x.1.1 = (2, 0) := h2.trans (by norm_num)
    rw [e2, e1]
    exact key.2

theorem corner_entry (θ : ℝ) (ax : ℕ → Axis) (a b : Fin 12) (hC : isC a b) :
    pOpO 1 θ ax (oTil 1) (e12 a) (e12 b) =
      pOpO 1 θ ax (oNum 1) (e12 (sw a)) (e12 (sw b)) := by
  have hcp : cp1 1 (e12 a).1.1 (e12 b).1.1 ∨ cp1 1 (e12 b).1.1 (e12 a).1.1 := by
    rw [e12_pt, e12_pt]
    exact (corner_iff a b).mpr hC
  rw [corner_entry_pt θ ax _ _ hcp]
  obtain ⟨h1, h2, h3, h4⟩ := sw_facts a b hC
  show _ = pHeO 1 θ ax (oNum 1) (e12 (sw a)).1.1 (e12 (sw b)).1.1 (e12 (sw a)).2 (e12 (sw b)).2
  rw [h1, h2, h3, h4]

theorem entries_generic (θ : ℝ) (ax : ℕ → Axis) (Hn Ht : Matrix (Fin 12) (Fin 12) ℂ)
    (hn : ∀ a b, pOpO 1 θ ax (oNum 1) (e12 a) (e12 b) = Hn a b)
    (hsame : ∀ a b, ¬ isC a b → Hn a b = Ht a b)
    (hsw : ∀ a b, isC a b → Hn (sw a) (sw b) = Ht a b) :
    ∀ a b, pOpO 1 θ ax (oTil 1) (e12 a) (e12 b) = Ht a b := by
  intro a b
  by_cases hC : isC a b
  · rw [corner_entry θ ax a b hC, hn (sw a) (sw b)]
    exact hsw a b hC
  · have hcp : ¬ (cp1 1 (e12 a).1.1 (e12 b).1.1 ∨ cp1 1 (e12 b).1.1 (e12 a).1.1) := by
      rw [e12_pt, e12_pt]
      exact fun h => hC ((corner_iff a b).mp h)
    rw [pOpO_oTil_off 1 θ ax _ _ (fun h => hcp (Or.inl h)) (fun h => hcp (Or.inr h)), hn]
    exact hsame a b hC

theorem same_t (c s j : ℂ) : ∀ a b : Fin 12, ¬ isC a b → HC12 c s j a b = HCt12 c s j a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [HC12, HCt12, isC]
theorem sw_t (c s j : ℂ) : ∀ a b : Fin 12, isC a b →
    HC12 c s j (sw a) (sw b) = HCt12 c s j a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [HC12, HCt12, isC, sw]
theorem same_p (c s j : ℂ) : ∀ a b : Fin 12, ¬ isC a b → HCp12 c s j a b = HCtp12 c s j a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [HCp12, HCtp12, isC]
theorem sw_p (c s j : ℂ) : ∀ a b : Fin 12, isC a b →
    HCp12 c s j (sw a) (sw b) = HCtp12 c s j a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [HCp12, HCtp12, isC, sw]
/-- **Base case with the flipped corner edge.** -/
theorem tilde_base (θ : ℝ) : defectO 1 θ faceAxis (fun _ => 2) (oTil 1) = 0 :=
  tilde_base_of_entries θ
    (entries_generic θ faceAxis _ _
      (fun a b => congrFun (congrFun (sub_num_faceAxis θ) a) b)
      (same_t _ _ _) (sw_t _ _ _))
    (entries_generic θ (fun _ => 2) _ _
      (fun a b => congrFun (congrFun (sub_num_const2 θ) a) b)
      (same_p _ _ _) (sw_p _ _ _))

/-- **The closed form of the trace defect, unconditional.** -/
theorem traceDefect_closed (θ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    traceDefect m θ =
      -16 * ((3 : ℂ) ^ (m - 1) + 1) * ((Real.sin (θ / 2) : ℝ) : ℂ) ^ 2 :=
  traceDefect_formula tilde_base θ m hm

end EvgenyTheorem
