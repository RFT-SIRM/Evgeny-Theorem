import EvgenyTheorem.OpSplit1

namespace EvgenyTheorem

open Matrix

theorem ite_iff_congr {α : Sort _} {c c' : Prop} {d : Decidable c} {d' : Decidable c'}
    (h : c ↔ c') (x y : α) : @ite α c d x y = @ite α c' d' x y := by
  by_cases hc : c
  · rw [if_pos hc, if_pos (h.mp hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (h.mpr h'))]

open Classical in
theorem sorted_mem {m : ℕ} {p q : Point} (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (hpq : p ≠ q) :
    (if p ≤ q then (p, q) else (q, p)).1 ∈ vertexOrder m ∧
    (if p ≤ q then (p, q) else (q, p)).2 ∈ vertexOrder m ∧
    (if p ≤ q then (p, q) else (q, p)).1 ≠ (if p ≤ q then (p, q) else (q, p)).2 := by
  by_cases h : p ≤ q
  · rw [if_pos h]
    exact ⟨hp, hq, hpq⟩
  · rw [if_neg h]
    exact ⟨hq, hp, hpq.symm⟩

theorem pHeO_diag (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (p : Point) (i j : C2) :
    pHeO m θ ax o p p i j = if i = j then ((pdeg m p : ℕ) : ℂ) else 0 := by
  unfold pHeO
  rw [if_pos rfl]

theorem pHe_diag (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (p : Point) (i j : C2) :
    pHe m θ ax p p i j = if i = j then ((pdeg m p : ℕ) : ℂ) else 0 := by
  unfold pHe
  rw [if_pos rfl]

theorem pHeO_zero_of_not_edge (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] {p q : Point} (hpq : p ≠ q)
    (hE : ¬ (EdgeB m p.1 p.2 q.1 q.2 = true)) (i j : C2) :
    pHeO m θ ax o p q i j = 0 := by
  unfold pHeO
  rw [if_neg hpq, if_neg hE]

/-! ### Transport of one entry into each copy -/

theorem pHe_succ_A (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) (hpq : p ≠ q) (i j : C2) :
    pHe (m + 1) θ ax p q i j = pHeO m θ ax (oA m) p q i j := by
  have hE := EdgeB_copyA hp hq
  have hs := sorted_mem hp hq hpq
  unfold pHe pHeO
  rw [if_neg hpq, if_neg hpq, hE]
  by_cases hEm : EdgeB m p.1 p.2 q.1 q.2 = true
  · rw [if_pos hEm, if_pos hEm]
    dsimp only
    rw [U_succ_A θ ax _ hs.1 hs.2.1 hs.2.2]
    exact ite_iff_congr Iff.rfl _ _
  · rw [if_neg hEm, if_neg hEm]

theorem pHe_succ_B (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point} (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) (hpq : p ≠ q)
    (i j : C2) :
    pHe (m + 1) θ ax (shiftPoint (2 ^ m) 1 0 p) (shiftPoint (2 ^ m) 1 0 q) i j =
      pHeO m θ ax (oB m) p q i j := by
  have hne : shiftPoint (2 ^ m) 1 0 p ≠ shiftPoint (2 ^ m) 1 0 q :=
    fun h => hpq (shiftPoint_injective _ _ _ h)
  have hE : EdgeB (m + 1) (shiftPoint (2 ^ m) 1 0 p).1 (shiftPoint (2 ^ m) 1 0 p).2
      (shiftPoint (2 ^ m) 1 0 q).1 (shiftPoint (2 ^ m) 1 0 q).2 =
      EdgeB m p.1 p.2 q.1 q.2 := by
    simpa [shiftPoint] using EdgeB_copyB hp hq
  have hs := sorted_mem hp hq hpq
  unfold pHe pHeO
  rw [if_neg hne, if_neg hpq, hE]
  by_cases hEm : EdgeB m p.1 p.2 q.1 q.2 = true
  · rw [if_pos hEm, if_pos hEm]
    dsimp only
    rw [sortE_shift (2 ^ m) 1 0 p q, U_succ_B θ ax hax _ hs.1 hs.2.1 hs.2.2]
    exact ite_iff_congr Iff.rfl _ _
  · rw [if_neg hEm, if_neg hEm]

theorem pHe_succ_C (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    {p q : Point} (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) (hpq : p ≠ q)
    (i j : C2) :
    pHe (m + 1) θ ax (shiftPoint (2 ^ m) 0 1 p) (shiftPoint (2 ^ m) 0 1 q) i j =
      pHeO m θ ax (oC m) p q i j := by
  have hne : shiftPoint (2 ^ m) 0 1 p ≠ shiftPoint (2 ^ m) 0 1 q :=
    fun h => hpq (shiftPoint_injective _ _ _ h)
  have hE : EdgeB (m + 1) (shiftPoint (2 ^ m) 0 1 p).1 (shiftPoint (2 ^ m) 0 1 p).2
      (shiftPoint (2 ^ m) 0 1 q).1 (shiftPoint (2 ^ m) 0 1 q).2 =
      EdgeB m p.1 p.2 q.1 q.2 := by
    simpa [shiftPoint] using EdgeB_copyC hp hq
  have hs := sorted_mem hp hq hpq
  unfold pHe pHeO
  rw [if_neg hne, if_neg hpq, hE]
  by_cases hEm : EdgeB m p.1 p.2 q.1 q.2 = true
  · rw [if_pos hEm, if_pos hEm]
    dsimp only
    rw [sortE_shift (2 ^ m) 0 1 p q, U_succ_C θ ax hax _ hs.1 hs.2.1 hs.2.2]
    exact ite_iff_congr Iff.rfl _ _
  · rw [if_neg hEm, if_neg hEm]

/-! ### The three copy kernels -/

abbrev inA (m : ℕ) (z : Point) : Prop := z ∈ (vertexOrder m).toFinset
abbrev inB (m : ℕ) (z : Point) : Prop :=
  2 ^ m ≤ z.1 ∧ (z.1 - 2 ^ m, z.2) ∈ (vertexOrder m).toFinset
abbrev inC (m : ℕ) (z : Point) : Prop :=
  2 ^ m ≤ z.2 ∧ (z.1, z.2 - 2 ^ m) ∈ (vertexOrder m).toFinset

def unB (m : ℕ) (z : Point) : Point := (z.1 - 2 ^ m, z.2)
def unC (m : ℕ) (z : Point) : Point := (z.1, z.2 - 2 ^ m)

noncomputable def KA (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (z z' : Point) (i j : C2) : ℂ :=
  if inA m z ∧ inA m z' then pHeO m θ ax (oA m) z z' i j else 0

noncomputable def KB (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (z z' : Point) (i j : C2) : ℂ :=
  if inB m z ∧ inB m z' then pHeO m θ ax (oB m) (unB m z) (unB m z') i j else 0

noncomputable def KC (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (z z' : Point) (i j : C2) : ℂ :=
  if inC m z ∧ inC m z' then pHeO m θ ax (oC m) (unC m z) (unC m z') i j else 0

theorem inB_shift {m : ℕ} {z : Point} (h : inB m z) : shiftPoint (2 ^ m) 1 0 (unB m z) = z := by
  obtain ⟨h1, _⟩ := h
  simp only [unB, shiftPoint]
  ext <;> simp <;> omega

theorem inC_shift {m : ℕ} {z : Point} (h : inC m z) : shiftPoint (2 ^ m) 0 1 (unC m z) = z := by
  obtain ⟨h1, _⟩ := h
  simp only [unC, shiftPoint]
  ext <;> simp <;> omega

theorem inB_mem {m : ℕ} {z : Point} (h : inB m z) : unB m z ∈ vertexOrder m :=
  List.mem_toFinset.mp h.2

theorem inC_mem {m : ℕ} {z : Point} (h : inC m z) : unC m z ∈ vertexOrder m :=
  List.mem_toFinset.mp h.2

theorem eq_of_mem_V_B {m : ℕ} {z : Point} (hz : z ∈ vertexOrder m) (hB : inB m z) :
    z = (2 ^ m, 0) := by
  have hA' : shiftPoint (2 ^ m) 1 0 (unB m z) ∈ vertexOrder m := by
    rw [inB_shift hB]
    exact hz
  have h0 := sB_mem_imp (inB_mem hB) hA'
  rw [← inB_shift hB, h0]
  simp [shiftPoint]

theorem eq_of_mem_V_C {m : ℕ} {z : Point} (hz : z ∈ vertexOrder m) (hC : inC m z) :
    z = (0, 2 ^ m) := by
  have hA' : shiftPoint (2 ^ m) 0 1 (unC m z) ∈ vertexOrder m := by
    rw [inC_shift hC]
    exact hz
  have h0 := sC_mem_imp (inC_mem hC) hA'
  rw [← inC_shift hC, h0]
  simp [shiftPoint]

theorem eq_of_B_C {m : ℕ} {z : Point} (hB : inB m z) (hC : inC m z) :
    z = (2 ^ m, 2 ^ m) := by
  have h := sB_eq_sC (inB_mem hB) (inC_mem hC) ((inB_shift hB).trans (inC_shift hC).symm)
  rw [← inB_shift hB, h.1]
  simp [shiftPoint]

theorem EdgeB_succ_of_inB {m : ℕ} {z z' : Point} (hB : inB m z) (hB' : inB m z') :
    EdgeB (m + 1) z.1 z.2 z'.1 z'.2 =
      EdgeB m (unB m z).1 (unB m z).2 (unB m z').1 (unB m z').2 := by
  have := EdgeB_copyB (inB_mem hB) (inB_mem hB')
  have h1 : z.1 - 2 ^ m + 2 ^ m = z.1 := Nat.sub_add_cancel hB.1
  have h1' : z'.1 - 2 ^ m + 2 ^ m = z'.1 := Nat.sub_add_cancel hB'.1
  simp only [unB] at this ⊢
  rw [h1, h1'] at this
  exact this

theorem EdgeB_succ_of_inC {m : ℕ} {z z' : Point} (hC : inC m z) (hC' : inC m z') :
    EdgeB (m + 1) z.1 z.2 z'.1 z'.2 =
      EdgeB m (unC m z).1 (unC m z).2 (unC m z').1 (unC m z').2 := by
  have := EdgeB_copyC (inC_mem hC) (inC_mem hC')
  have h1 : z.2 - 2 ^ m + 2 ^ m = z.2 := Nat.sub_add_cancel hC.1
  have h1' : z'.2 - 2 ^ m + 2 ^ m = z'.2 := Nat.sub_add_cancel hC'.1
  simp only [unC] at this ⊢
  rw [h1, h1'] at this
  exact this

theorem pdeg_succ' (m : ℕ) (q : Point) :
    pdeg (m + 1) q = (if inA m q then pdeg m q else 0) +
      (if inB m q then pdeg m (unB m q) else 0) +
      (if inC m q then pdeg m (unC m q) else 0) := pdeg_succ m q

/-- **Pointwise additivity of the operator over the three copies.** -/
theorem pHe_succ (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (hax1 : ∀ k, ax (3 ^ m + k) = ax k)
    (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k) (z z' : Point) (i j : C2) :
    pHe (m + 1) θ ax z z' i j =
      KA m θ ax z z' i j + KB m θ ax z z' i j + KC m θ ax z z' i j := by
  by_cases hzz : z = z'
  · subst hzz
    rw [pHe_diag]
    by_cases hij : i = j
    · by_cases hA : inA m z <;> by_cases hB : inB m z <;> by_cases hC : inC m z <;>
        simp [KA, KB, KC, hA, hB, hC, pHeO_diag, hij, pdeg_succ']
    · simp [KA, KB, KC, pHeO_diag, hij]
  · by_cases hE : EdgeB (m + 1) z.1 z.2 z'.1 z'.2 = true
    · rcases (EdgeB_succ_DABC m z z').mp hE with hA | hB | hC
      · have hm := EdgeB_mem m _ _ _ _ hA.2.2.2.2
        have hz : z ∈ vertexOrder m := (mem_vertexOrder_iff m z).mpr hm.1
        have hz' : z' ∈ vertexOrder m := (mem_vertexOrder_iff m z').mpr hm.2
        have hKA : KA m θ ax z z' i j = pHe (m + 1) θ ax z z' i j := by
          unfold KA
          rw [if_pos ⟨List.mem_toFinset.mpr hz, List.mem_toFinset.mpr hz'⟩]
          exact (pHe_succ_A m θ ax hz hz' hzz i j).symm
        have hKB : KB m θ ax z z' i j = 0 := by
          unfold KB
          rw [if_neg]
          rintro ⟨hb, hb'⟩
          exact hzz ((eq_of_mem_V_B hz hb).trans (eq_of_mem_V_B hz' hb').symm)
        have hKC : KC m θ ax z z' i j = 0 := by
          unfold KC
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
        have hKB : KB m θ ax z z' i j = pHe (m + 1) θ ax z z' i j := by
          unfold KB
          rw [if_pos ⟨hinB, hinB'⟩]
          have := pHe_succ_B m θ ax hax1 hp hq hpq i j
          rw [inB_shift hinB, inB_shift hinB'] at this
          exact this.symm
        have hKA : KA m θ ax z z' i j = 0 := by
          unfold KA
          rw [if_neg]
          rintro ⟨ha, ha'⟩
          exact hzz ((eq_of_mem_V_B (List.mem_toFinset.mp ha) hinB).trans
            (eq_of_mem_V_B (List.mem_toFinset.mp ha') hinB').symm)
        have hKC : KC m θ ax z z' i j = 0 := by
          unfold KC
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
        have hKC : KC m θ ax z z' i j = pHe (m + 1) θ ax z z' i j := by
          unfold KC
          rw [if_pos ⟨hinC, hinC'⟩]
          have := pHe_succ_C m θ ax hax2 hp hq hpq i j
          rw [inC_shift hinC, inC_shift hinC'] at this
          exact this.symm
        have hKA : KA m θ ax z z' i j = 0 := by
          unfold KA
          rw [if_neg]
          rintro ⟨ha, ha'⟩
          exact hzz ((eq_of_mem_V_C (List.mem_toFinset.mp ha) hinC).trans
            (eq_of_mem_V_C (List.mem_toFinset.mp ha') hinC').symm)
        have hKB : KB m θ ax z z' i j = 0 := by
          unfold KB
          rw [if_neg]
          rintro ⟨hb, hb'⟩
          exact hzz ((eq_of_B_C hb hinC).trans (eq_of_B_C hb' hinC').symm)
        rw [hKA, hKB, hKC]
        ring
    · have h0 : pHe (m + 1) θ ax z z' i j = 0 := by
        unfold pHe
        rw [if_neg hzz, if_neg hE]
      have hKA : KA m θ ax z z' i j = 0 := by
        unfold KA
        by_cases hc : inA m z ∧ inA m z'
        · rw [if_pos hc]
          have hz := List.mem_toFinset.mp hc.1
          have hz' := List.mem_toFinset.mp hc.2
          refine pHeO_zero_of_not_edge m θ ax _ hzz ?_ i j
          rw [← EdgeB_copyA hz hz']
          exact hE
        · rw [if_neg hc]
      have hKB : KB m θ ax z z' i j = 0 := by
        unfold KB
        by_cases hc : inB m z ∧ inB m z'
        · rw [if_pos hc]
          have hpq : unB m z ≠ unB m z' := fun h => hzz (by
            rw [← inB_shift hc.1, ← inB_shift hc.2, h])
          refine pHeO_zero_of_not_edge m θ ax _ hpq ?_ i j
          rw [← EdgeB_succ_of_inB hc.1 hc.2]
          exact hE
        · rw [if_neg hc]
      have hKC : KC m θ ax z z' i j = 0 := by
        unfold KC
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
