import EvgenyTheorem.GlueCornerCube
import EvgenyTheorem.FlipFaces

namespace EvgenyTheorem

open Matrix

def oNum (m : ℕ) (p q : Point) : Prop := vIdx m p ≤ vIdx m q

instance (m : ℕ) : DecidableRel (oNum m) := fun p q => by unfold oNum; infer_instance

theorem vIdx_inj {m : ℕ} {p q : Point} (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (h : vIdx m p = vIdx m q) : p = q := by
  unfold vIdx at h
  first
    | exact (List.idxOf_inj hp).mp h
    | exact (List.idxOf_inj hp hq).mp h

theorem oNum_anti (m : ℕ) : OAnti m (oNum m) := by
  intro p q hp hq hpq
  have hne : vIdx m p ≠ vIdx m q := fun h => hpq (vIdx_inj hp hq h)
  unfold oNum
  constructor <;> intro h <;> omega

/-- Corner edge `(2^m-1,0) → (2^m,0)`. -/
def cp1 (m : ℕ) (p q : Point) : Prop := p = (2 ^ m - 1, 0) ∧ q = (2 ^ m, 0)

/-- Numbering with the corner edge forced to point backward. -/
def oTil (m : ℕ) (p q : Point) : Prop :=
  (oNum m p q ∧ ¬ cp1 m p q ∧ ¬ cp1 m q p) ∨ cp1 m q p

open Classical in
noncomputable instance (m : ℕ) : DecidableRel (oTil m) := fun p q => Classical.propDecidable _

theorem cp1_not_both (m : ℕ) (p q : Point) : ¬ (cp1 m p q ∧ cp1 m q p) := by
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have h := h1.symm.trans h4
  have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  simp only [Prod.mk.injEq] at h
  omega

theorem oTil_anti (m : ℕ) : OAnti m (oTil m) := by
  intro p q hp hq hpq
  have hn := oNum_anti m p q hp hq hpq
  have hab := cp1_not_both m p q
  unfold oTil
  tauto

theorem orient_transfer (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis) (o o' : Point → Point → Prop)
    [DecidableRel o] [DecidableRel o'] (ha : OAnti m o) (ha' : OAnti m o')
    (h : ∀ f ∈ facesExact m, (o f.1 f.2.1 ↔ o' f.1 f.2.1)) :
    defectO m θ ax ax' o = defectO m θ ax ax' o' := by
  apply defectO_congr
  intro p q hpq hE hfl
  have hm := EdgeB_mem m _ _ _ _ hE
  have hp : p ∈ vertexOrder m := (mem_vertexOrder_iff m p).mpr hm.1
  have hq : q ∈ vertexOrder m := (mem_vertexOrder_iff m q).mpr hm.2
  have fl : ∀ a b : Point, (a, b) ∈ fluxEdges m → ∃ f ∈ facesExact m, f.1 = a ∧ f.2.1 = b := by
    intro a b hab
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hab
    have hle := flux_edge_order m f hf
    have h' : fluxEdge f = (f.1, f.2.1) := by simp [fluxEdge, hle]
    rw [h'] at hfe
    exact ⟨f, hf, (Prod.mk.inj hfe).1, (Prod.mk.inj hfe).2⟩
  by_cases hle : p ≤ q
  · rw [if_pos hle] at hfl
    obtain ⟨f, hf, h1, h2⟩ := fl p q hfl
    rw [← h1, ← h2]
    exact h f hf
  · rw [if_neg hle] at hfl
    obtain ⟨f, hf, h1, h2⟩ := fl q p hfl
    have h3 := h f hf
    rw [h1, h2] at h3
    rw [ha p q hp hq hpq, ha' p q hp hq hpq]
    exact not_congr h3

/-- Transfer of sixth-moment defects between orientations which agree on
the ordered face edges. This is the p=6 counterpart of orient_transfer. -/
theorem orient_transfer6 (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o o' : Point → Point → Prop) [DecidableRel o] [DecidableRel o']
    (ha : OAnti m o) (ha' : OAnti m o')
    (h : ∀ f ∈ facesExact m, (o f.1 f.2.1 ↔ o' f.1 f.2.1)) :
    defectO6 m θ ax ax' o = defectO6 m θ ax ax' o' := by
  apply defectO6_congr
  intro p q hpq hE hfl
  have hm := EdgeB_mem m _ _ _ _ hE
  have hp : p ∈ vertexOrder m := (mem_vertexOrder_iff m p).mpr hm.1
  have hq : q ∈ vertexOrder m := (mem_vertexOrder_iff m q).mpr hm.2
  have fl : ∀ a b : Point, (a, b) ∈ fluxEdges m →
      ∃ f ∈ facesExact m, f.1 = a ∧ f.2.1 = b := by
    intro a b hab
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hab
    have hle := flux_edge_order m f hf
    have h' : fluxEdge f = (f.1, f.2.1) := by simp [fluxEdge, hle]
    rw [h'] at hfe
    exact ⟨f, hf, (Prod.mk.inj hfe).1, (Prod.mk.inj hfe).2⟩
  by_cases hle : p ≤ q
  · rw [if_pos hle] at hfl
    obtain ⟨f, hf, h1, h2⟩ := fl p q hfl
    rw [← h1, ← h2]
    exact h f hf
  · rw [if_neg hle] at hfl
    obtain ⟨f, hf, h1, h2⟩ := fl q p hfl
    have h3 := h f hf
    rw [h1, h2] at h3
    rw [ha p q hp hq hpq, ha' p q hp hq hpq]
    exact not_congr h3


/-- Transfer of eighth-moment defects between orientations which agree on
the ordered face edges. -/
theorem orient_transfer8 (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o o' : Point → Point → Prop) [DecidableRel o] [DecidableRel o']
    (ha : OAnti m o) (ha' : OAnti m o')
    (h : ∀ f ∈ facesExact m, (o f.1 f.2.1 ↔ o' f.1 f.2.1)) :
    defectO8 m θ ax ax' o = defectO8 m θ ax ax' o' := by
  apply defectO8_congr
  intro p q hpq hE hfl
  have hm := EdgeB_mem m _ _ _ _ hE
  have hp : p ∈ vertexOrder m := (mem_vertexOrder_iff m p).mpr hm.1
  have hq : q ∈ vertexOrder m := (mem_vertexOrder_iff m q).mpr hm.2
  have fl : ∀ a b : Point, (a, b) ∈ fluxEdges m →
      ∃ f ∈ facesExact m, f.1 = a ∧ f.2.1 = b := by
    intro a b hab
    obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hab
    have hle := flux_edge_order m f hf
    have h' : fluxEdge f = (f.1, f.2.1) := by simp [fluxEdge, hle]
    rw [h'] at hfe
    exact ⟨f, hf, (Prod.mk.inj hfe).1, (Prod.mk.inj hfe).2⟩
  by_cases hle : p ≤ q
  · rw [if_pos hle] at hfl
    obtain ⟨f, hf, h1, h2⟩ := fl p q hfl
    rw [← h1, ← h2]
    exact h f hf
  · rw [if_neg hle] at hfl
    obtain ⟨f, hf, h1, h2⟩ := fl q p hfl
    have h3 := h f hf
    rw [h1, h2] at h3
    rw [ha p q hp hq hpq, ha' p q hp hq hpq]
    exact not_congr h3


theorem le_iff_of_lt_iff {a b c d : ℕ} (h : b < a ↔ d < c) : a ≤ b ↔ c ≤ d := by
  first
    | exact not_lt.symm.trans ((not_congr h).trans not_lt)
    | (constructor <;> intro x <;> omega)

theorem transfer_A (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis) (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO m θ ax ax' (oNum (m + 1)) = defectO m θ ax ax' (oNum m) := by
  refine orient_transfer m θ ax ax' _ _ (oanti_A m _ hanti) (oNum_anti m) ?_
  intro f hf
  obtain ⟨h1, h2⟩ := face_endpoints_mem m f hf
  show vIdx (m + 1) f.1 ≤ vIdx (m + 1) f.2.1 ↔ vIdx m f.1 ≤ vIdx m f.2.1
  rw [vIdx_succ_of_mem h1, vIdx_succ_of_mem h2]

/-- Copy-A orientation transfer for the sixth-moment defect.
The A-copy keeps the parent's vertex-order orientation on every face edge. -/
theorem transfer_A6 (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO6 m θ ax ax' (oNum (m + 1)) =
      defectO6 m θ ax ax' (oNum m) := by
  refine orient_transfer6 m θ ax ax' _ _ (oanti_A m _ hanti) (oNum_anti m) ?_
  intro f hf
  obtain ⟨h1, h2⟩ := face_endpoints_mem m f hf
  show vIdx (m + 1) f.1 ≤ vIdx (m + 1) f.2.1 ↔
    vIdx m f.1 ≤ vIdx m f.2.1
  rw [vIdx_succ_of_mem h1, vIdx_succ_of_mem h2]

theorem transfer_B (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis) (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO m θ ax ax' (oBo m (oNum (m + 1))) = defectO m θ ax ax' (oNum m) := by
  refine orient_transfer m θ ax ax' _ _ (oanti_B m _ hanti) (oNum_anti m) ?_
  intro f hf
  have hb := flipped_B m f hf
  unfold flippedP at hb
  change vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.2.1) < vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.1) ↔
    vIdx m f.2.1 < vIdx m f.1 at hb
  show vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.1) ≤ vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.2.1) ↔
    vIdx m f.1 ≤ vIdx m f.2.1
  exact le_iff_of_lt_iff hb

/-- Copy-B orientation transfer for the sixth-moment defect. -/
theorem transfer_B6 (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO6 m θ ax ax' (oBo m (oNum (m + 1))) =
      defectO6 m θ ax ax' (oNum m) := by
  refine orient_transfer6 m θ ax ax' _ _ (oanti_B m _ hanti) (oNum_anti m) ?_
  intro f hf
  have hb := flipped_B m f hf
  unfold flippedP at hb
  change vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.2.1) <
      vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.1) ↔
    vIdx m f.2.1 < vIdx m f.1 at hb
  show vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.1) ≤
      vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.2.1) ↔
    vIdx m f.1 ≤ vIdx m f.2.1
  exact le_iff_of_lt_iff hb

theorem transfer_C (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (ax ax' : ℕ → Axis)
    (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO m θ ax ax' (oCo m (oNum (m + 1))) = defectO m θ ax ax' (oTil m) := by
  refine orient_transfer m θ ax ax' _ _ (oanti_C m _ hanti) (oTil_anti m) ?_
  intro f hf
  obtain ⟨ha, hb⟩ := face_endpoints_mem m f hf
  obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
  have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hC := flipped_C m hm f hf
  unfold flippedP at hC
  change vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) < vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1) ↔
    (vIdx m f.2.1 < vIdx m f.1 ∨ f.2.1 = (2 ^ m, 0)) at hC
  have hcp : cp1 m f.1 f.2.1 ↔ f.2.1 = (2 ^ m, 0) := by
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have h1 : f.2.1.1 = 2 ^ m := by rw [h]
      have h2 : f.2.1.2 = 0 := by rw [h]
      ext
      · simp only; omega
      · simp only; omega
  have hcp' : ¬ cp1 m f.2.1 f.1 := by
    rintro ⟨h1, h2⟩
    have e1 : f.2.1.1 = 2 ^ m - 1 := by rw [h1]
    have e2 : f.1.1 = 2 ^ m := by rw [h2]
    omega
  show vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1) ≤ vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) ↔
    oTil m f.1 f.2.1
  have hle : vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1) ≤ vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) ↔
      ¬ (vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) < vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1)) :=
    not_lt.symm
  rw [hle, hC]
  unfold oTil oNum
  constructor
  · intro h
    left
    exact ⟨not_lt.mp (not_or.mp h).1, fun hh => (not_or.mp h).2 (hcp.mp hh), hcp'⟩
  · intro h hh
    rcases h with ⟨h1, h2, h3⟩ | h
    · rcases hh with hh | hh
      · exact absurd hh (not_lt.mpr h1)
      · exact h2 (hcp.mpr hh)
    · exact hcp' h

/-- Copy-C orientation transfer for the sixth-moment defect.
The boundary edge is handled by the same exceptional-corner clause as
the established fourth-moment transfer. -/
theorem transfer_C6 (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (ax ax' : ℕ → Axis)
    (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO6 m θ ax ax' (oCo m (oNum (m + 1))) =
      defectO6 m θ ax ax' (oTil m) := by
  refine orient_transfer6 m θ ax ax' _ _ (oanti_C m _ hanti) (oTil_anti m) ?_
  intro f hf
  obtain ⟨ha, hb⟩ := face_endpoints_mem m f hf
  obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
  have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hC := flipped_C m hm f hf
  unfold flippedP at hC
  change vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) <
      vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1) ↔
    (vIdx m f.2.1 < vIdx m f.1 ∨ f.2.1 = (2 ^ m, 0)) at hC
  have hcp : cp1 m f.1 f.2.1 ↔ f.2.1 = (2 ^ m, 0) := by
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have h1 : f.2.1.1 = 2 ^ m := by rw [h]
      have h2 : f.2.1.2 = 0 := by rw [h]
      ext
      · simp only; omega
      · simp only; omega
  have hcp' : ¬ cp1 m f.2.1 f.1 := by
    rintro ⟨h1, h2⟩
    have e1 : f.2.1.1 = 2 ^ m - 1 := by rw [h1]
    have e2 : f.1.1 = 2 ^ m := by rw [h2]
    omega
  show vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1) ≤
      vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) ↔
    oTil m f.1 f.2.1
  have hle :
      vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1) ≤
          vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) ↔
        ¬ (vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) <
          vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1)) :=
    not_lt.symm
  rw [hle, hC]
  unfold oTil oNum
  constructor
  · intro h
    left
    exact ⟨not_lt.mp (not_or.mp h).1,
      fun hh => (not_or.mp h).2 (hcp.mp hh), hcp'⟩
  · intro h hh
    rcases h with ⟨h1, h2, h3⟩ | h
    · rcases hh with hh | hh
      · exact absurd hh (not_lt.mpr h1)
      · exact h2 (hcp.mpr hh)
    · exact hcp' h


/-- Copy-A orientation transfer for the eighth-moment defect. -/
theorem transfer_A8 (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO8 m θ ax ax' (oNum (m + 1)) =
      defectO8 m θ ax ax' (oNum m) := by
  refine orient_transfer8 m θ ax ax' _ _ (oanti_A m _ hanti) (oNum_anti m) ?_
  intro f hf
  obtain ⟨h1, h2⟩ := face_endpoints_mem m f hf
  show vIdx (m + 1) f.1 ≤ vIdx (m + 1) f.2.1 ↔
    vIdx m f.1 ≤ vIdx m f.2.1
  rw [vIdx_succ_of_mem h1, vIdx_succ_of_mem h2]

/-- Copy-B orientation transfer for the eighth-moment defect. -/
theorem transfer_B8 (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO8 m θ ax ax' (oBo m (oNum (m + 1))) =
      defectO8 m θ ax ax' (oNum m) := by
  refine orient_transfer8 m θ ax ax' _ _ (oanti_B m _ hanti) (oNum_anti m) ?_
  intro f hf
  have hb := flipped_B m f hf
  unfold flippedP at hb
  change vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.2.1) <
      vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.1) ↔
    vIdx m f.2.1 < vIdx m f.1 at hb
  show vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.1) ≤
      vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.2.1) ↔
    vIdx m f.1 ≤ vIdx m f.2.1
  exact le_iff_of_lt_iff hb

/-- Copy-C orientation transfer for the eighth-moment defect. The
exceptional corner edge is retained in the oTil orientation. -/
theorem transfer_C8 (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (ax ax' : ℕ → Axis)
    (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO8 m θ ax ax' (oCo m (oNum (m + 1))) =
      defectO8 m θ ax ax' (oTil m) := by
  refine orient_transfer8 m θ ax ax' _ _ (oanti_C m _ hanti) (oTil_anti m) ?_
  intro f hf
  obtain ⟨ha, hb⟩ := face_endpoints_mem m f hf
  obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
  have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hC := flipped_C m hm f hf
  unfold flippedP at hC
  change vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) <
      vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1) ↔
    (vIdx m f.2.1 < vIdx m f.1 ∨ f.2.1 = (2 ^ m, 0)) at hC
  have hcp : cp1 m f.1 f.2.1 ↔ f.2.1 = (2 ^ m, 0) := by
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have h1 : f.2.1.1 = 2 ^ m := by rw [h]
      have h2 : f.2.1.2 = 0 := by rw [h]
      ext
      · simp only; omega
      · simp only; omega
  have hcp' : ¬ cp1 m f.2.1 f.1 := by
    rintro ⟨h1, h2⟩
    have e1 : f.2.1.1 = 2 ^ m - 1 := by rw [h1]
    have e2 : f.1.1 = 2 ^ m := by rw [h2]
    omega
  show vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1) ≤
      vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) ↔
    oTil m f.1 f.2.1
  have hle :
      vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1) ≤
          vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) ↔
        ¬ (vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.2.1) <
          vIdx (m + 1) (shiftPoint (2 ^ m) 0 1 f.1)) :=
    not_lt.symm
  rw [hle, hC]
  unfold oTil oNum
  constructor
  · intro h
    left
    exact ⟨not_lt.mp (not_or.mp h).1,
      fun hh => (not_or.mp h).2 (hcp.mp hh), hcp'⟩
  · intro h hh
    rcases h with ⟨h1, h2, h3⟩ | h
    · rcases hh with hh | hh
      · exact absurd hh (not_lt.mpr h1)
      · exact h2 (hcp.mpr hh)
    · exact hcp' h


theorem faceAxis_pow1 (m : ℕ) (hm : 1 ≤ m) : ∀ k, faceAxis (3 ^ m + k) = faceAxis k := by
  intro k
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have : 3 ^ (n + 1) + k = 3 * 3 ^ n + k := by ring
  rw [this]
  exact faceAxis_shift3 _ _

theorem faceAxis_pow2 (m : ℕ) (hm : 1 ≤ m) : ∀ k, faceAxis (2 * 3 ^ m + k) = faceAxis k := by
  intro k
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have : 2 * 3 ^ (n + 1) + k = 3 * (2 * 3 ^ n) + k := by ring
  rw [this]
  exact faceAxis_shift3 _ _

/-- First recursion: `Δ_{m+1} = 2 Δ_m + Δ̃_m`. -/
theorem defect_succ_num (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) :
    defectO (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      2 * defectO m θ faceAxis (fun _ => 2) (oNum m) +
        defectO m θ faceAxis (fun _ => 2) (oTil m) := by
  have hanti := oNum_anti (m + 1)
  rw [defectO_succ m hm θ faceAxis (fun _ => 2) (oNum (m + 1)) hanti
    (faceAxis_pow1 m hm) (faceAxis_pow2 m hm) (fun _ => rfl) (fun _ => rfl)
    (sgK_corner_data m θ faceAxis (fun _ => 2) (oNum (m + 1)) hanti),
    transfer_A m θ _ _ hanti, transfer_B m θ _ _ hanti, transfer_C m hm θ _ _ hanti]
  ring


/-- Exact recursion for the sixth-moment defect in the standard orientation.
The p=6 boundary difference remains as an explicit term; no cancellation
or level stabilization is assumed here. -/
theorem defectO6_succ_num (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    defectO6 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      2 * defectO6 m θ faceAxis (fun _ => 2) (oNum m) +
        defectO6 m θ faceAxis (fun _ => 2) (oTil m) +
        (glueRHS6 m (sgK m θ faceAxis (oNum (m + 1))) -
          glueRHS6 m (sgK m θ (fun _ => 2) (oNum (m + 1))) ) := by
  have hanti := oNum_anti (m + 1)
  rw [defectO6_succ m hm θ faceAxis (fun _ => 2) (oNum (m + 1)) hanti
      (faceAxis_pow1 m (by omega)) (faceAxis_pow2 m (by omega))
      (fun _ => rfl) (fun _ => rfl),
    transfer_A6 m θ faceAxis (fun _ => 2) hanti,
    transfer_B6 m θ faceAxis (fun _ => 2) hanti,
    transfer_C6 m (by omega) θ faceAxis (fun _ => 2) hanti]
  ring


/-- Exact eighth-moment recurrence in the standard numbering orientation.
Copy A and B transport to oNum m, while copy C transports to the
exceptional-corner orientation oTil m. The full boundary difference
between faceAxis and the fixed-Z axis is retained. -/
theorem defectO8_succ_num (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    defectO8 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      2 * defectO8 m θ faceAxis (fun _ => 2) (oNum m) +
        defectO8 m θ faceAxis (fun _ => 2) (oTil m) +
        (glueRHS8 m (sgK m θ faceAxis (oNum (m + 1))) -
          glueRHS8 m (sgK m θ (fun _ => 2) (oNum (m + 1))) ) := by
  have hanti := oNum_anti (m + 1)
  rw [defectO8_succ m hm θ faceAxis (fun _ => 2) (oNum (m + 1)) hanti
      (faceAxis_pow1 m (by omega)) (faceAxis_pow2 m (by omega))
      (fun _ => rfl) (fun _ => rfl),
    transfer_A8 m θ faceAxis (fun _ => 2) hanti,
    transfer_B8 m θ faceAxis (fun _ => 2) hanti,
    transfer_C8 m (by omega) θ faceAxis (fun _ => 2) hanti]
  ring

end EvgenyTheorem
