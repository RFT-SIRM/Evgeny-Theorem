import EvgenyTheorem.EdgeSplit
import EvgenyTheorem.PointModel1

namespace EvgenyTheorem

theorem pdeg_eq_sum (m : ℕ) (q : Point) :
    pdeg m q = ∑ r ∈ (vertexOrder m).toFinset,
      if EdgeB m q.1 q.2 r.1 r.2 = true then 1 else 0 := by
  unfold pdeg
  rw [length_filter_eq_sum, ← List.sum_toFinset _ (vertexOrder_nodup m)]

theorem V_subset_succ (m : ℕ) :
    (vertexOrder m).toFinset ⊆ (vertexOrder (m + 1)).toFinset := by
  intro p hp
  rw [List.mem_toFinset] at hp ⊢
  exact (mem_vertexOrder_succ_iff m p).mpr (Or.inl hp)

theorem imageB_subset (m : ℕ) :
    (vertexOrder m).toFinset.image (shiftPoint (2 ^ m) 1 0) ⊆
      (vertexOrder (m + 1)).toFinset := by
  intro z hz
  rw [Finset.mem_image] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  rw [List.mem_toFinset]
  exact (mem_vertexOrder_succ_iff m _).mpr
    (Or.inr (Or.inl (List.mem_map_of_mem (List.mem_toFinset.mp hp))))

theorem imageC_subset (m : ℕ) :
    (vertexOrder m).toFinset.image (shiftPoint (2 ^ m) 0 1) ⊆
      (vertexOrder (m + 1)).toFinset := by
  intro z hz
  rw [Finset.mem_image] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  rw [List.mem_toFinset]
  exact (mem_vertexOrder_succ_iff m _).mpr
    (Or.inr (Or.inr (List.mem_map_of_mem (List.mem_toFinset.mp hp))))

theorem sum_succ_A (m : ℕ) (g : Point → ℕ)
    (hg : ∀ r ∈ (vertexOrder (m + 1)).toFinset, r ∉ (vertexOrder m).toFinset → g r = 0) :
    ∑ r ∈ (vertexOrder (m + 1)).toFinset, g r = ∑ r ∈ (vertexOrder m).toFinset, g r := by
  symm
  exact Finset.sum_subset (V_subset_succ m) (fun r hr hrn => hg r hr hrn)

theorem sum_succ_B (m : ℕ) (g : Point → ℕ)
    (hg : ∀ r ∈ (vertexOrder (m + 1)).toFinset,
      r ∉ (vertexOrder m).toFinset.image (shiftPoint (2 ^ m) 1 0) → g r = 0) :
    ∑ r ∈ (vertexOrder (m + 1)).toFinset, g r =
      ∑ r ∈ (vertexOrder m).toFinset, g (shiftPoint (2 ^ m) 1 0 r) := by
  have h1 : ∑ x ∈ (vertexOrder m).toFinset.image (shiftPoint (2 ^ m) 1 0), g x =
      ∑ x ∈ (vertexOrder m).toFinset, g (shiftPoint (2 ^ m) 1 0 x) :=
    Finset.sum_image (fun a _ b _ h => shiftPoint_injective _ _ _ h)
  rw [← h1]
  symm
  exact Finset.sum_subset (imageB_subset m) (fun r hr hrn => hg r hr hrn)

theorem sum_succ_C (m : ℕ) (g : Point → ℕ)
    (hg : ∀ r ∈ (vertexOrder (m + 1)).toFinset,
      r ∉ (vertexOrder m).toFinset.image (shiftPoint (2 ^ m) 0 1) → g r = 0) :
    ∑ r ∈ (vertexOrder (m + 1)).toFinset, g r =
      ∑ r ∈ (vertexOrder m).toFinset, g (shiftPoint (2 ^ m) 0 1 r) := by
  have h1 : ∑ x ∈ (vertexOrder m).toFinset.image (shiftPoint (2 ^ m) 0 1), g x =
      ∑ x ∈ (vertexOrder m).toFinset, g (shiftPoint (2 ^ m) 0 1 x) :=
    Finset.sum_image (fun a _ b _ h => shiftPoint_injective _ _ _ h)
  rw [← h1]
  symm
  exact Finset.sum_subset (imageC_subset m) (fun r hr hrn => hg r hr hrn)

/-- Contribution of copy A to the degree of `q` at level `m+1`. -/
theorem degA (m : ℕ) (q : Point) :
    ∑ r ∈ (vertexOrder (m + 1)).toFinset, (if DA m q r then 1 else 0) =
      if q ∈ (vertexOrder m).toFinset then pdeg m q else 0 := by
  rw [sum_succ_A]
  · by_cases hq : q ∈ (vertexOrder m).toFinset
    · rw [if_pos hq, pdeg_eq_sum]
      have hqb := vertexOrder_sum_le m q (List.mem_toFinset.mp hq)
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have hrb := vertexOrder_sum_le m r (List.mem_toFinset.mp hr)
      by_cases hE : EdgeB m q.1 q.2 r.1 r.2 = true
      · have h : DA m q r := ⟨by omega, by omega, by omega, by omega, hE⟩
        simp [h, hE]
      · have h : ¬ DA m q r := fun h => hE h.2.2.2.2
        simp [h, hE]
    · rw [if_neg hq]
      refine Finset.sum_eq_zero (fun r hr => ?_)
      have h : ¬ DA m q r := by
        intro h
        have := (EdgeB_mem m _ _ _ _ h.2.2.2.2).1
        exact hq (List.mem_toFinset.mpr ((mem_vertexOrder_iff m q).mpr this))
      simp [h]
  · intro r _ hr
    have h : ¬ DA m q r := by
      intro h
      have := (EdgeB_mem m _ _ _ _ h.2.2.2.2).2
      exact hr (List.mem_toFinset.mpr ((mem_vertexOrder_iff m r).mpr this))
    simp [h]

/-- Contribution of copy B to the degree of `q` at level `m+1`. -/
theorem degB (m : ℕ) (q : Point) :
    ∑ r ∈ (vertexOrder (m + 1)).toFinset, (if DB m q r then 1 else 0) =
      if 2 ^ m ≤ q.1 ∧ (q.1 - 2 ^ m, q.2) ∈ (vertexOrder m).toFinset then
        pdeg m (q.1 - 2 ^ m, q.2) else 0 := by
  rw [sum_succ_B]
  · have e : ∀ r' ∈ (vertexOrder m).toFinset,
        DB m q (shiftPoint (2 ^ m) 1 0 r') ↔
          (2 ^ m ≤ q.1 ∧ q.2 ≤ 2 ^ m ∧ EdgeB m (q.1 - 2 ^ m) q.2 r'.1 r'.2 = true) := by
      intro r' hr'
      have hrb := vertexOrder_sum_le m r' (List.mem_toFinset.mp hr')
      simp only [DB, shiftPoint]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨h1, h2, by simpa using h5⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, by omega, by omega, by simpa using h3⟩
    by_cases hq : 2 ^ m ≤ q.1 ∧ (q.1 - 2 ^ m, q.2) ∈ (vertexOrder m).toFinset
    · rw [if_pos hq, pdeg_eq_sum]
      have hqb := vertexOrder_sum_le m _ (List.mem_toFinset.mp hq.2)
      refine Finset.sum_congr rfl (fun r' hr' => ?_)
      by_cases hE : EdgeB m (q.1 - 2 ^ m) q.2 r'.1 r'.2 = true
      · have h : DB m q (shiftPoint (2 ^ m) 1 0 r') :=
          (e r' hr').mpr ⟨hq.1, by simp at hqb; omega, hE⟩
        simp [h, hE]
      · have h : ¬ DB m q (shiftPoint (2 ^ m) 1 0 r') := fun h => hE ((e r' hr').mp h).2.2
        simp [h, hE]
    · rw [if_neg hq]
      refine Finset.sum_eq_zero (fun r' hr' => ?_)
      have h : ¬ DB m q (shiftPoint (2 ^ m) 1 0 r') := by
        intro h
        obtain ⟨h1, _, h3⟩ := (e r' hr').mp h
        have := (EdgeB_mem m _ _ _ _ h3).1
        exact hq ⟨h1, List.mem_toFinset.mpr ((mem_vertexOrder_iff m _).mpr this)⟩
      simp [h]
  · intro r _ hr
    have h : ¬ DB m q r := by
      intro h
      obtain ⟨b1, b2, b3, b4, b5⟩ := h
      have hm := (EdgeB_mem m _ _ _ _ b5).2
      apply hr
      rw [Finset.mem_image]
      refine ⟨(r.1 - 2 ^ m, r.2), List.mem_toFinset.mpr ((mem_vertexOrder_iff m _).mpr hm), ?_⟩
      simp only [shiftPoint]
      ext <;> simp <;> omega
    simp [h]

/-- Contribution of copy C to the degree of `q` at level `m+1`. -/
theorem degC (m : ℕ) (q : Point) :
    ∑ r ∈ (vertexOrder (m + 1)).toFinset, (if DC m q r then 1 else 0) =
      if 2 ^ m ≤ q.2 ∧ (q.1, q.2 - 2 ^ m) ∈ (vertexOrder m).toFinset then
        pdeg m (q.1, q.2 - 2 ^ m) else 0 := by
  rw [sum_succ_C]
  · have e : ∀ r' ∈ (vertexOrder m).toFinset,
        DC m q (shiftPoint (2 ^ m) 0 1 r') ↔
          (q.1 ≤ 2 ^ m ∧ 2 ^ m ≤ q.2 ∧ EdgeB m q.1 (q.2 - 2 ^ m) r'.1 r'.2 = true) := by
      intro r' hr'
      have hrb := vertexOrder_sum_le m r' (List.mem_toFinset.mp hr')
      simp only [DC, shiftPoint]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨h1, h2, by simpa using h5⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, by omega, by omega, by simpa using h3⟩
    by_cases hq : 2 ^ m ≤ q.2 ∧ (q.1, q.2 - 2 ^ m) ∈ (vertexOrder m).toFinset
    · rw [if_pos hq, pdeg_eq_sum]
      have hqb := vertexOrder_sum_le m _ (List.mem_toFinset.mp hq.2)
      refine Finset.sum_congr rfl (fun r' hr' => ?_)
      by_cases hE : EdgeB m q.1 (q.2 - 2 ^ m) r'.1 r'.2 = true
      · have h : DC m q (shiftPoint (2 ^ m) 0 1 r') :=
          (e r' hr').mpr ⟨by simp at hqb; omega, hq.1, hE⟩
        simp [h, hE]
      · have h : ¬ DC m q (shiftPoint (2 ^ m) 0 1 r') := fun h => hE ((e r' hr').mp h).2.2
        simp [h, hE]
    · rw [if_neg hq]
      refine Finset.sum_eq_zero (fun r' hr' => ?_)
      have h : ¬ DC m q (shiftPoint (2 ^ m) 0 1 r') := by
        intro h
        obtain ⟨_, h2, h3⟩ := (e r' hr').mp h
        have := (EdgeB_mem m _ _ _ _ h3).1
        exact hq ⟨h2, List.mem_toFinset.mpr ((mem_vertexOrder_iff m _).mpr this)⟩
      simp [h]
  · intro r _ hr
    have h : ¬ DC m q r := by
      intro h
      obtain ⟨c1, c2, c3, c4, c5⟩ := h
      have hm := (EdgeB_mem m _ _ _ _ c5).2
      apply hr
      rw [Finset.mem_image]
      refine ⟨(r.1, r.2 - 2 ^ m), List.mem_toFinset.mpr ((mem_vertexOrder_iff m _).mpr hm), ?_⟩
      simp only [shiftPoint]
      ext <;> simp <;> omega
    simp [h]

/-- **Degree additivity.** -/
theorem pdeg_succ (m : ℕ) (q : Point) :
    pdeg (m + 1) q =
      (if q ∈ (vertexOrder m).toFinset then pdeg m q else 0) +
      (if 2 ^ m ≤ q.1 ∧ (q.1 - 2 ^ m, q.2) ∈ (vertexOrder m).toFinset then
        pdeg m (q.1 - 2 ^ m, q.2) else 0) +
      (if 2 ^ m ≤ q.2 ∧ (q.1, q.2 - 2 ^ m) ∈ (vertexOrder m).toFinset then
        pdeg m (q.1, q.2 - 2 ^ m) else 0) := by
  rw [pdeg_eq_sum, ← degA, ← degB, ← degC, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => ind_succ m q r)

end EvgenyTheorem
