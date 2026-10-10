import EvgenyTheorem.OpSplit2

namespace EvgenyTheorem

open Matrix

/-- Orientation pulled back to copy B. -/
def oBo (m : ℕ) (o : Point → Point → Prop) (p q : Point) : Prop :=
  o (shiftPoint (2 ^ m) 1 0 p) (shiftPoint (2 ^ m) 1 0 q)
/-- Orientation pulled back to copy C. -/
def oCo (m : ℕ) (o : Point → Point → Prop) (p q : Point) : Prop :=
  o (shiftPoint (2 ^ m) 0 1 p) (shiftPoint (2 ^ m) 0 1 q)

instance (m : ℕ) (o : Point → Point → Prop) [inst : DecidableRel o] :
    DecidableRel (oBo m o) :=
  fun p q => inferInstanceAs (Decidable (o (shiftPoint (2 ^ m) 1 0 p) (shiftPoint (2 ^ m) 1 0 q)))
instance (m : ℕ) (o : Point → Point → Prop) [inst : DecidableRel o] :
    DecidableRel (oCo m o) :=
  fun p q => inferInstanceAs (Decidable (o (shiftPoint (2 ^ m) 0 1 p) (shiftPoint (2 ^ m) 0 1 q)))

theorem pHeO_succ_A (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o] {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) (hpq : p ≠ q) (i j : C2) :
    pHeO (m + 1) θ ax o p q i j = pHeO m θ ax o p q i j := by
  have hE := EdgeB_copyA hp hq
  have hs := sorted_mem hp hq hpq
  unfold pHeO
  rw [if_neg hpq, if_neg hpq, hE]
  by_cases hEm : EdgeB m p.1 p.2 q.1 q.2 = true
  · rw [if_pos hEm, if_pos hEm]
    dsimp only
    rw [U_succ_A θ ax _ hs.1 hs.2.1 hs.2.2]
  · rw [if_neg hEm, if_neg hEm]

theorem pHeO_succ_B (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o] (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point} (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) (hpq : p ≠ q)
    (i j : C2) :
    pHeO (m + 1) θ ax o (shiftPoint (2 ^ m) 1 0 p) (shiftPoint (2 ^ m) 1 0 q) i j =
      pHeO m θ ax (oBo m o) p q i j := by
  have hne : shiftPoint (2 ^ m) 1 0 p ≠ shiftPoint (2 ^ m) 1 0 q :=
    fun h => hpq (shiftPoint_injective _ _ _ h)
  have hE : EdgeB (m + 1) (shiftPoint (2 ^ m) 1 0 p).1 (shiftPoint (2 ^ m) 1 0 p).2
      (shiftPoint (2 ^ m) 1 0 q).1 (shiftPoint (2 ^ m) 1 0 q).2 =
      EdgeB m p.1 p.2 q.1 q.2 := by
    simpa [shiftPoint] using EdgeB_copyB hp hq
  have hs := sorted_mem hp hq hpq
  unfold pHeO
  rw [if_neg hne, if_neg hpq, hE]
  by_cases hEm : EdgeB m p.1 p.2 q.1 q.2 = true
  · rw [if_pos hEm, if_pos hEm]
    dsimp only
    rw [sortE_shift (2 ^ m) 1 0 p q, U_succ_B θ ax hax _ hs.1 hs.2.1 hs.2.2]
    exact ite_iff_congr Iff.rfl _ _
  · rw [if_neg hEm, if_neg hEm]

theorem pHeO_succ_C (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o] (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    {p q : Point} (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) (hpq : p ≠ q)
    (i j : C2) :
    pHeO (m + 1) θ ax o (shiftPoint (2 ^ m) 0 1 p) (shiftPoint (2 ^ m) 0 1 q) i j =
      pHeO m θ ax (oCo m o) p q i j := by
  have hne : shiftPoint (2 ^ m) 0 1 p ≠ shiftPoint (2 ^ m) 0 1 q :=
    fun h => hpq (shiftPoint_injective _ _ _ h)
  have hE : EdgeB (m + 1) (shiftPoint (2 ^ m) 0 1 p).1 (shiftPoint (2 ^ m) 0 1 p).2
      (shiftPoint (2 ^ m) 0 1 q).1 (shiftPoint (2 ^ m) 0 1 q).2 =
      EdgeB m p.1 p.2 q.1 q.2 := by
    simpa [shiftPoint] using EdgeB_copyC hp hq
  have hs := sorted_mem hp hq hpq
  unfold pHeO
  rw [if_neg hne, if_neg hpq, hE]
  by_cases hEm : EdgeB m p.1 p.2 q.1 q.2 = true
  · rw [if_pos hEm, if_pos hEm]
    dsimp only
    rw [sortE_shift (2 ^ m) 0 1 p q, U_succ_C θ ax hax _ hs.1 hs.2.1 hs.2.2]
    exact ite_iff_congr Iff.rfl _ _
  · rw [if_neg hEm, if_neg hEm]

/-! ### Kernels with an arbitrary orientation -/

noncomputable def KAo (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o] (z z' : Point) (i j : C2) : ℂ :=
  if inA m z ∧ inA m z' then pHeO m θ ax o z z' i j else 0

noncomputable def KBo (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o] (z z' : Point) (i j : C2) : ℂ :=
  if inB m z ∧ inB m z' then pHeO m θ ax (oBo m o) (unB m z) (unB m z') i j else 0

noncomputable def KCo (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o] (z z' : Point) (i j : C2) : ℂ :=
  if inC m z ∧ inC m z' then pHeO m θ ax (oCo m o) (unC m z) (unC m z') i j else 0

/-- **Pointwise additivity of the operator over the three copies.** -/
theorem pHeO_succ (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o] (hax1 : ∀ k, ax (3 ^ m + k) = ax k)
    (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k) (z z' : Point) (i j : C2) :
    pHeO (m + 1) θ ax o z z' i j =
      KAo m θ ax o z z' i j + KBo m θ ax o z z' i j + KCo m θ ax o z z' i j := by
  by_cases hzz : z = z'
  · subst hzz
    rw [pHeO_diag]
    by_cases hij : i = j
    · by_cases hA : inA m z <;> by_cases hB : inB m z <;> by_cases hC : inC m z <;>
        simp [KAo, KBo, KCo, hA, hB, hC, pHeO_diag, hij, pdeg_succ']
    · simp [KAo, KBo, KCo, pHeO_diag, hij]
  · by_cases hE : EdgeB (m + 1) z.1 z.2 z'.1 z'.2 = true
    · rcases (EdgeB_succ_DABC m z z').mp hE with hA | hB | hC
      · have hm := EdgeB_mem m _ _ _ _ hA.2.2.2.2
        have hz : z ∈ vertexOrder m := (mem_vertexOrder_iff m z).mpr hm.1
        have hz' : z' ∈ vertexOrder m := (mem_vertexOrder_iff m z').mpr hm.2
        have hKA : KAo m θ ax o z z' i j = pHeO (m + 1) θ ax o z z' i j := by
          unfold KAo
          rw [if_pos ⟨List.mem_toFinset.mpr hz, List.mem_toFinset.mpr hz'⟩]
          exact (pHeO_succ_A m θ ax o hz hz' hzz i j).symm
        have hKB : KBo m θ ax o z z' i j = 0 := by
          unfold KBo
          rw [if_neg]
          rintro ⟨hb, hb'⟩
          exact hzz ((eq_of_mem_V_B hz hb).trans (eq_of_mem_V_B hz' hb').symm)
        have hKC : KCo m θ ax o z z' i j = 0 := by
          unfold KCo
          rw [if_neg]
          rintro ⟨hc, hc'⟩
          exact hzz ((eq_of_mem_V_C hz hc).trans (eq_of_mem_V_C hz' hc').symm)
        rw [hKA, hKB, hKC]
        ring
      · obtain ⟨b1, b2, b3, b4, b5⟩ := hB
        have hm := EdgeB_mem m _ _ _ _ b5
        have hp : unB m z ∈ vertexOrder m := (mem_vertexOrder_iff m _).mpr hm.1
        have hq : unB m z' ∈ vertexOrder m := (mem_vertexOrder_iff m _).mpr hm.2
        have hinB : inB m z := ⟨b1, List.mem_toFinset.mpr hp⟩
        have hinB' : inB m z' := ⟨b3, List.mem_toFinset.mpr hq⟩
        have hpq : unB m z ≠ unB m z' := fun h => hzz (by
          rw [← inB_shift hinB, ← inB_shift hinB', h])
        have hKB : KBo m θ ax o z z' i j = pHeO (m + 1) θ ax o z z' i j := by
          unfold KBo
          rw [if_pos ⟨hinB, hinB'⟩]
          have := pHeO_succ_B m θ ax o hax1 hp hq hpq i j
          rw [inB_shift hinB, inB_shift hinB'] at this
          exact this.symm
        have hKA : KAo m θ ax o z z' i j = 0 := by
          unfold KAo
          rw [if_neg]
          rintro ⟨ha, ha'⟩
          exact hzz ((eq_of_mem_V_B (List.mem_toFinset.mp ha) hinB).trans
            (eq_of_mem_V_B (List.mem_toFinset.mp ha') hinB').symm)
        have hKC : KCo m θ ax o z z' i j = 0 := by
          unfold KCo
          rw [if_neg]
          rintro ⟨hc, hc'⟩
          exact hzz ((eq_of_B_C hinB hc).trans (eq_of_B_C hinB' hc').symm)
        rw [hKA, hKB, hKC]
        ring
      · obtain ⟨c1, c2, c3, c4, c5⟩ := hC
        have hm := EdgeB_mem m _ _ _ _ c5
        have hp : unC m z ∈ vertexOrder m := (mem_vertexOrder_iff m _).mpr hm.1
        have hq : unC m z' ∈ vertexOrder m := (mem_vertexOrder_iff m _).mpr hm.2
        have hinC : inC m z := ⟨c2, List.mem_toFinset.mpr hp⟩
        have hinC' : inC m z' := ⟨c4, List.mem_toFinset.mpr hq⟩
        have hpq : unC m z ≠ unC m z' := fun h => hzz (by
          rw [← inC_shift hinC, ← inC_shift hinC', h])
        have hKC : KCo m θ ax o z z' i j = pHeO (m + 1) θ ax o z z' i j := by
          unfold KCo
          rw [if_pos ⟨hinC, hinC'⟩]
          have := pHeO_succ_C m θ ax o hax2 hp hq hpq i j
          rw [inC_shift hinC, inC_shift hinC'] at this
          exact this.symm
        have hKA : KAo m θ ax o z z' i j = 0 := by
          unfold KAo
          rw [if_neg]
          rintro ⟨ha, ha'⟩
          exact hzz ((eq_of_mem_V_C (List.mem_toFinset.mp ha) hinC).trans
            (eq_of_mem_V_C (List.mem_toFinset.mp ha') hinC').symm)
        have hKB : KBo m θ ax o z z' i j = 0 := by
          unfold KBo
          rw [if_neg]
          rintro ⟨hb, hb'⟩
          exact hzz ((eq_of_B_C hb hinC).trans (eq_of_B_C hb' hinC').symm)
        rw [hKA, hKB, hKC]
        ring
    · have h0 : pHeO (m + 1) θ ax o z z' i j = 0 := by
        unfold pHeO
        rw [if_neg hzz, if_neg hE]
      have hKA : KAo m θ ax o z z' i j = 0 := by
        unfold KAo
        by_cases hc : inA m z ∧ inA m z'
        · rw [if_pos hc]
          have hz := List.mem_toFinset.mp hc.1
          have hz' := List.mem_toFinset.mp hc.2
          refine pHeO_zero_of_not_edge m θ ax _ hzz ?_ i j
          rw [← EdgeB_copyA hz hz']
          exact hE
        · rw [if_neg hc]
      have hKB : KBo m θ ax o z z' i j = 0 := by
        unfold KBo
        by_cases hc : inB m z ∧ inB m z'
        · rw [if_pos hc]
          have hpq : unB m z ≠ unB m z' := fun h => hzz (by
            rw [← inB_shift hc.1, ← inB_shift hc.2, h])
          refine pHeO_zero_of_not_edge m θ ax _ hpq ?_ i j
          rw [← EdgeB_succ_of_inB hc.1 hc.2]
          exact hE
        · rw [if_neg hc]
      have hKC : KCo m θ ax o z z' i j = 0 := by
        unfold KCo
        by_cases hc : inC m z ∧ inC m z'
        · rw [if_pos hc]
          have hpq : unC m z ≠ unC m z' := fun h => hzz (by
            rw [← inC_shift hc.1, ← inC_shift hc.2, h])
          refine pHeO_zero_of_not_edge m θ ax _ hpq ?_ i j
          rw [← EdgeB_succ_of_inC hc.1 hc.2]
          exact hE
        · rw [if_neg hc]
      rw [h0, hKA, hKB, hKC]
      ring

end EvgenyTheorem
