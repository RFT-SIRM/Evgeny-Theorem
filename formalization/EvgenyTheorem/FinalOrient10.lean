import EvgenyTheorem.FinalOrient
import EvgenyTheorem.FinalTilde
import EvgenyTheorem.GlueTrace10

namespace EvgenyTheorem

/-- Transfer of tenth-moment defects between orientations which agree on
the ordered face edges. -/
theorem orient_transfer10 (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o o' : Point → Point → Prop) [DecidableRel o] [DecidableRel o']
    (ha : OAnti m o) (ha' : OAnti m o')
    (h : ∀ f ∈ facesExact m, (o f.1 f.2.1 ↔ o' f.1 f.2.1)) :
    defectO10 m θ ax ax' o = defectO10 m θ ax ax' o' := by
  apply defectO10_congr
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

/-- Copy-A orientation transfer for the tenth-moment defect. -/
theorem transfer_A10 (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO10 m θ ax ax' (oNum (m + 1)) =
      defectO10 m θ ax ax' (oNum m) := by
  refine orient_transfer10 m θ ax ax' _ _ (oanti_A m _ hanti) (oNum_anti m) ?_
  intro f hf
  obtain ⟨h1, h2⟩ := face_endpoints_mem m f hf
  show vIdx (m + 1) f.1 ≤ vIdx (m + 1) f.2.1 ↔
    vIdx m f.1 ≤ vIdx m f.2.1
  rw [vIdx_succ_of_mem h1, vIdx_succ_of_mem h2]

/-- Copy-B orientation transfer for the tenth-moment defect. -/
theorem transfer_B10 (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO10 m θ ax ax' (oBo m (oNum (m + 1))) =
      defectO10 m θ ax ax' (oNum m) := by
  refine orient_transfer10 m θ ax ax' _ _ (oanti_B m _ hanti) (oNum_anti m) ?_
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

/-- Copy-C orientation transfer for the tenth-moment defect. The
exceptional corner edge is retained in the oTil orientation. -/
theorem transfer_C10 (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (ax ax' : ℕ → Axis)
    (hanti : OAnti (m + 1) (oNum (m + 1))) :
    defectO10 m θ ax ax' (oCo m (oNum (m + 1))) =
      defectO10 m θ ax ax' (oTil m) := by
  refine orient_transfer10 m θ ax ax' _ _ (oanti_C m _ hanti) (oTil_anti m) ?_
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

/-- Exact tenth-moment recurrence in the standard numbering orientation.
Copy A and B transport to oNum m, while copy C transports to the
exceptional-corner orientation oTil m. The full boundary difference
between faceAxis and the fixed-Z axis is retained. -/
theorem defectO10_succ_num (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) :
    defectO10 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      2 * defectO10 m θ faceAxis (fun _ => 2) (oNum m) +
        defectO10 m θ faceAxis (fun _ => 2) (oTil m) +
        (glueRHS10 m (sgK m θ faceAxis (oNum (m + 1))) -
          glueRHS10 m (sgK m θ (fun _ => 2) (oNum (m + 1))) ) := by
  have hanti := oNum_anti (m + 1)
  rw [defectO10_succ m hm θ faceAxis (fun _ => 2) (oNum (m + 1)) hanti
      (faceAxis_pow1 m (by omega)) (faceAxis_pow2 m (by omega))
      (fun _ => rfl) (fun _ => rfl),
    transfer_A10 m θ faceAxis (fun _ => 2) hanti,
    transfer_B10 m θ faceAxis (fun _ => 2) hanti,
    transfer_C10 m (by omega) θ faceAxis (fun _ => 2) hanti]
  ring

/-- Exact p=10 recursion for the flipped-corner orientation.
Copy A transports to oNum, while copies B and C transport to oTil.
The complete axis-dependent boundary difference remains explicit. -/
theorem defectO10_succ_til (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) :
    defectO10 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1)) =
      defectO10 m θ faceAxis (fun _ => 2) (oNum m) +
        2 * defectO10 m θ faceAxis (fun _ => 2) (oTil m) +
        (glueRHS10 m (sgK m θ faceAxis (oTil (m + 1))) -
          glueRHS10 m (sgK m θ (fun _ => 2) (oTil (m + 1))) ) := by
  have hanti := oTil_anti (m + 1)
  rw [defectO10_succ m hm θ faceAxis (fun _ => 2) (oTil (m + 1)) hanti
    (faceAxis_pow1 m (by omega)) (faceAxis_pow2 m (by omega))
    (fun _ => rfl) (fun _ => rfl)]
  have eA : defectO10 m θ faceAxis (fun _ => 2) (oTil (m + 1)) =
      defectO10 m θ faceAxis (fun _ => 2) (oNum m) := by
    refine orient_transfer10 m θ _ _ _ _ (oanti_A m _ hanti) (oNum_anti m) ?_
    intro f hf
    obtain ⟨h1, h2⟩ := face_endpoints_mem m f hf
    obtain ⟨c1, c2⟩ := cp1_not_A m (by omega) h1 h2
    exact (oTil_of_no_corner c1 c2).trans (faceA m f hf)
  have eB : defectO10 m θ faceAxis (fun _ => 2) (oBo m (oTil (m + 1))) =
      defectO10 m θ faceAxis (fun _ => 2) (oTil m) := by
    refine orient_transfer10 m θ _ _ _ _ (oanti_B m _ hanti) (oTil_anti m) ?_
    intro f hf
    obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
    obtain ⟨k1, k2⟩ := cp1_shiftB m hs1
    show oTil (m + 1) (shiftPoint (2 ^ m) 1 0 f.1)
        (shiftPoint (2 ^ m) 1 0 f.2.1) ↔ oTil m f.1 f.2.1
    exact oTil_transport (faceB m f hf) k1 k2
  have eC : defectO10 m θ faceAxis (fun _ => 2) (oCo m (oTil (m + 1))) =
      defectO10 m θ faceAxis (fun _ => 2) (oTil m) := by
    refine orient_transfer10 m θ _ _ _ _ (oanti_C m _ hanti) (oTil_anti m) ?_
    intro f hf
    obtain ⟨c1, c2⟩ := cp1_shiftC m (p := f.1) (q := f.2.1)
    show oTil (m + 1) (shiftPoint (2 ^ m) 0 1 f.1)
        (shiftPoint (2 ^ m) 0 1 f.2.1) ↔ oTil m f.1 f.2.1
    exact (oTil_of_no_corner c1 c2).trans (faceC m (by omega) f hf)
  rw [eA, eB, eC]
  ring

/-- Exact recurrence for the H10 difference between numbering and
flipped-corner orientations. The difference of the two boundary residuals
is retained explicitly. -/
theorem defectO10_orientation_difference_succ
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) :
    (defectO10 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) -
      defectO10 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1))) =
    (defectO10 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO10 m θ faceAxis (fun _ => 2) (oTil m)) +
    ((glueRHS10 m (sgK m θ faceAxis (oNum (m + 1))) -
        glueRHS10 m (sgK m θ (fun _ => 2) (oNum (m + 1))) ) -
      (glueRHS10 m (sgK m θ faceAxis (oTil (m + 1))) -
        glueRHS10 m (sgK m θ (fun _ => 2) (oTil (m + 1))) )) := by
  rw [defectO10_succ_num m hm θ, defectO10_succ_til m hm θ]
  ring

end EvgenyTheorem
