import EvgenyTheorem.FinalArith
import EvgenyTheorem.CornerLocality

namespace EvgenyTheorem

open Matrix

theorem two_le_pow {m : ℕ} (hm : 1 ≤ m) : 2 ≤ 2 ^ m :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

theorem oTil_of_no_corner {n : ℕ} {p q : Point} (h1 : ¬ cp1 n p q) (h2 : ¬ cp1 n q p) :
    oTil n p q ↔ oNum n p q := by
  unfold oTil
  tauto

theorem oTil_transport {n k : ℕ} {p q p' q' : Point}
    (hnum : oNum k p' q' ↔ oNum n p q) (h1 : cp1 k p' q' ↔ cp1 n p q)
    (h2 : cp1 k q' p' ↔ cp1 n q p) : oTil k p' q' ↔ oTil n p q := by
  unfold oTil
  tauto

theorem cp1_not_A (m : ℕ) (hm : 1 ≤ m) {p q : Point} (hp : p ∈ vertexOrder m)
    (hq : q ∈ vertexOrder m) : ¬ cp1 (m + 1) p q ∧ ¬ cp1 (m + 1) q p := by
  obtain ⟨x, y⟩ := p
  obtain ⟨u, v⟩ := q
  have h1 := vertexOrder_sum_le m (x, y) hp
  have h2 := vertexOrder_sum_le m (u, v) hq
  try dsimp only at h1 h2
  have hs := two_le_pow hm
  simp only [cp1, Prod.mk.injEq, pow_succ]
  omega

theorem cp1_shiftB (m : ℕ) {p q : Point} (hpq : p.1 + 1 = q.1) :
    (cp1 (m + 1) (shiftPoint (2 ^ m) 1 0 p) (shiftPoint (2 ^ m) 1 0 q) ↔ cp1 m p q) ∧
      (cp1 (m + 1) (shiftPoint (2 ^ m) 1 0 q) (shiftPoint (2 ^ m) 1 0 p) ↔ cp1 m q p) := by
  obtain ⟨x, y⟩ := p
  obtain ⟨u, v⟩ := q
  have hpq' : x + 1 = u := hpq
  have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  simp only [cp1, shiftPoint, Prod.mk.injEq, pow_succ]
  omega

theorem cp1_shiftC (m : ℕ) {p q : Point} :
    ¬ cp1 (m + 1) (shiftPoint (2 ^ m) 0 1 p) (shiftPoint (2 ^ m) 0 1 q) ∧
      ¬ cp1 (m + 1) (shiftPoint (2 ^ m) 0 1 q) (shiftPoint (2 ^ m) 0 1 p) := by
  obtain ⟨x, y⟩ := p
  obtain ⟨u, v⟩ := q
  have hs : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  simp only [cp1, shiftPoint, Prod.mk.injEq, pow_succ]
  omega

theorem faceA (m : ℕ) (f : Face) (hf : f ∈ facesExact m) :
    oNum (m + 1) f.1 f.2.1 ↔ oNum m f.1 f.2.1 := by
  obtain ⟨h1, h2⟩ := face_endpoints_mem m f hf
  show vIdx (m + 1) f.1 ≤ vIdx (m + 1) f.2.1 ↔ vIdx m f.1 ≤ vIdx m f.2.1
  rw [vIdx_succ_of_mem h1, vIdx_succ_of_mem h2]

theorem faceB (m : ℕ) (f : Face) (hf : f ∈ facesExact m) :
    oNum (m + 1) (shiftPoint (2 ^ m) 1 0 f.1) (shiftPoint (2 ^ m) 1 0 f.2.1) ↔
      oNum m f.1 f.2.1 := by
  have hb := flipped_B m f hf
  unfold flippedP at hb
  change vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.2.1) < vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.1) ↔
    vIdx m f.2.1 < vIdx m f.1 at hb
  show vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.1) ≤ vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 f.2.1) ↔
    vIdx m f.1 ≤ vIdx m f.2.1
  exact le_iff_of_lt_iff hb

theorem faceC (m : ℕ) (hm : 1 ≤ m) (f : Face) (hf : f ∈ facesExact m) :
    oNum (m + 1) (shiftPoint (2 ^ m) 0 1 f.1) (shiftPoint (2 ^ m) 0 1 f.2.1) ↔
      oTil m f.1 f.2.1 := by
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

/-- Second recursion: `Δ̃_{m+1} = Δ_m + 2 Δ̃_m`. -/
theorem defect_succ_til (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) :
    defectO (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1)) =
      defectO m θ faceAxis (fun _ => 2) (oNum m) +
        2 * defectO m θ faceAxis (fun _ => 2) (oTil m) := by
  have hanti := oTil_anti (m + 1)
  rw [defectO_succ m hm θ faceAxis (fun _ => 2) (oTil (m + 1)) hanti
    (faceAxis_pow1 m hm) (faceAxis_pow2 m hm) (fun _ => rfl) (fun _ => rfl)
    (sgK_corner_data m θ faceAxis (fun _ => 2) (oTil (m + 1)) hanti)]
  have eA : defectO m θ faceAxis (fun _ => 2) (oTil (m + 1)) =
      defectO m θ faceAxis (fun _ => 2) (oNum m) := by
    refine orient_transfer m θ _ _ _ _ (oanti_A m _ hanti) (oNum_anti m) ?_
    intro f hf
    obtain ⟨h1, h2⟩ := face_endpoints_mem m f hf
    obtain ⟨c1, c2⟩ := cp1_not_A m hm h1 h2
    exact (oTil_of_no_corner c1 c2).trans (faceA m f hf)
  have eB : defectO m θ faceAxis (fun _ => 2) (oBo m (oTil (m + 1))) =
      defectO m θ faceAxis (fun _ => 2) (oTil m) := by
    refine orient_transfer m θ _ _ _ _ (oanti_B m _ hanti) (oTil_anti m) ?_
    intro f hf
    obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
    obtain ⟨k1, k2⟩ := cp1_shiftB m hs1
    show oTil (m + 1) (shiftPoint (2 ^ m) 1 0 f.1) (shiftPoint (2 ^ m) 1 0 f.2.1) ↔
      oTil m f.1 f.2.1
    exact oTil_transport (faceB m f hf) k1 k2
  have eC : defectO m θ faceAxis (fun _ => 2) (oCo m (oTil (m + 1))) =
      defectO m θ faceAxis (fun _ => 2) (oTil m) := by
    refine orient_transfer m θ _ _ _ _ (oanti_C m _ hanti) (oTil_anti m) ?_
    intro f hf
    obtain ⟨c1, c2⟩ := cp1_shiftC m (p := f.1) (q := f.2.1)
    show oTil (m + 1) (shiftPoint (2 ^ m) 0 1 f.1) (shiftPoint (2 ^ m) 0 1 f.2.1) ↔
      oTil m f.1 f.2.1
    exact (oTil_of_no_corner c1 c2).trans (faceC m hm f hf)
  rw [eA, eB, eC]
  ring


/-- Exact p=6 recursion for the flipped-corner orientation.
The copy transports use the existing cp1 corner conditions, and the
axis-dependent boundary difference remains explicit. -/
theorem defectO6_succ_til (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    defectO6 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1)) =
      defectO6 m θ faceAxis (fun _ => 2) (oNum m) +
        2 * defectO6 m θ faceAxis (fun _ => 2) (oTil m) +
        (glueRHS6 m (sgK m θ faceAxis (oTil (m + 1))) -
          glueRHS6 m (sgK m θ (fun _ => 2) (oTil (m + 1))) ) := by
  have hanti := oTil_anti (m + 1)
  rw [defectO6_succ m hm θ faceAxis (fun _ => 2) (oTil (m + 1)) hanti
    (faceAxis_pow1 m (by omega)) (faceAxis_pow2 m (by omega))
    (fun _ => rfl) (fun _ => rfl)]
  have eA : defectO6 m θ faceAxis (fun _ => 2) (oTil (m + 1)) =
      defectO6 m θ faceAxis (fun _ => 2) (oNum m) := by
    refine orient_transfer6 m θ _ _ _ _ (oanti_A m _ hanti) (oNum_anti m) ?_
    intro f hf
    obtain ⟨h1, h2⟩ := face_endpoints_mem m f hf
    obtain ⟨c1, c2⟩ := cp1_not_A m (by omega) h1 h2
    exact (oTil_of_no_corner c1 c2).trans (faceA m f hf)
  have eB : defectO6 m θ faceAxis (fun _ => 2) (oBo m (oTil (m + 1))) =
      defectO6 m θ faceAxis (fun _ => 2) (oTil m) := by
    refine orient_transfer6 m θ _ _ _ _ (oanti_B m _ hanti) (oTil_anti m) ?_
    intro f hf
    obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
    obtain ⟨k1, k2⟩ := cp1_shiftB m hs1
    show oTil (m + 1) (shiftPoint (2 ^ m) 1 0 f.1)
        (shiftPoint (2 ^ m) 1 0 f.2.1) ↔ oTil m f.1 f.2.1
    exact oTil_transport (faceB m f hf) k1 k2
  have eC : defectO6 m θ faceAxis (fun _ => 2) (oCo m (oTil (m + 1))) =
      defectO6 m θ faceAxis (fun _ => 2) (oTil m) := by
    refine orient_transfer6 m θ _ _ _ _ (oanti_C m _ hanti) (oTil_anti m) ?_
    intro f hf
    obtain ⟨c1, c2⟩ := cp1_shiftC m (p := f.1) (q := f.2.1)
    show oTil (m + 1) (shiftPoint (2 ^ m) 0 1 f.1)
        (shiftPoint (2 ^ m) 0 1 f.2.1) ↔ oTil m f.1 f.2.1
    exact (oTil_of_no_corner c1 c2).trans (faceC m (by omega) f hf)
  rw [eA, eB, eC]
  ring


/-- Exact recurrence for the difference of the two sixth-moment orientation
defects. The difference of the boundary residuals remains explicit. -/
theorem defectO6_orientation_difference_succ
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    (defectO6 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) -
      defectO6 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1))) =
    (defectO6 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO6 m θ faceAxis (fun _ => 2) (oTil m)) +
    ((glueRHS6 m (sgK m θ faceAxis (oNum (m + 1))) -
        glueRHS6 m (sgK m θ (fun _ => 2) (oNum (m + 1))) ) -
      (glueRHS6 m (sgK m θ faceAxis (oTil (m + 1))) -
        glueRHS6 m (sgK m θ (fun _ => 2) (oTil (m + 1))) )) := by
  rw [defectO6_succ_num m hm θ, defectO6_succ_til m hm θ]
  ring


/-- Exact p=6 orientation-difference recurrence with each boundary residual
rewritten as its established power-(1,5)/(2,4) residual. No cancellation is
assumed. -/
theorem defectO6_orientation_difference_succ_highPower
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    (defectO6 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) -
      defectO6 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1))) =
    (defectO6 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO6 m θ faceAxis (fun _ => 2) (oTil m)) +
    (glueRHS6_highPowerResidual m
        (sgK m θ faceAxis (oNum (m + 1)))
        (sgK m θ (fun _ => 2) (oNum (m + 1))) -
      glueRHS6_highPowerResidual m
        (sgK m θ faceAxis (oTil (m + 1)))
        (sgK m θ (fun _ => 2) (oTil (m + 1))) ) := by
  rw [defectO6_orientation_difference_succ m hm θ,
    glueRHS6_sgK_axis_residual_of_diag123 m hm θ faceAxis (fun _ => 2)
      (oNum (m + 1)) (oNum_anti (m + 1)),
    glueRHS6_sgK_axis_residual_of_diag123 m hm θ faceAxis (fun _ => 2)
      (oTil (m + 1)) (oTil_anti (m + 1))]




/-- Exact p=8 recursion for the flipped-corner orientation.
Copy A transports to oNum, while copies B and C transport to oTil.
The complete axis-dependent boundary difference remains explicit. -/
theorem defectO8_succ_til (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    defectO8 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1)) =
      defectO8 m θ faceAxis (fun _ => 2) (oNum m) +
        2 * defectO8 m θ faceAxis (fun _ => 2) (oTil m) +
        (glueRHS8 m (sgK m θ faceAxis (oTil (m + 1))) -
          glueRHS8 m (sgK m θ (fun _ => 2) (oTil (m + 1))) ) := by
  have hanti := oTil_anti (m + 1)
  rw [defectO8_succ m hm θ faceAxis (fun _ => 2) (oTil (m + 1)) hanti
    (faceAxis_pow1 m (by omega)) (faceAxis_pow2 m (by omega))
    (fun _ => rfl) (fun _ => rfl)]
  have eA : defectO8 m θ faceAxis (fun _ => 2) (oTil (m + 1)) =
      defectO8 m θ faceAxis (fun _ => 2) (oNum m) := by
    refine orient_transfer8 m θ _ _ _ _ (oanti_A m _ hanti) (oNum_anti m) ?_
    intro f hf
    obtain ⟨h1, h2⟩ := face_endpoints_mem m f hf
    obtain ⟨c1, c2⟩ := cp1_not_A m (by omega) h1 h2
    exact (oTil_of_no_corner c1 c2).trans (faceA m f hf)
  have eB : defectO8 m θ faceAxis (fun _ => 2) (oBo m (oTil (m + 1))) =
      defectO8 m θ faceAxis (fun _ => 2) (oTil m) := by
    refine orient_transfer8 m θ _ _ _ _ (oanti_B m _ hanti) (oTil_anti m) ?_
    intro f hf
    obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
    obtain ⟨k1, k2⟩ := cp1_shiftB m hs1
    show oTil (m + 1) (shiftPoint (2 ^ m) 1 0 f.1)
        (shiftPoint (2 ^ m) 1 0 f.2.1) ↔ oTil m f.1 f.2.1
    exact oTil_transport (faceB m f hf) k1 k2
  have eC : defectO8 m θ faceAxis (fun _ => 2) (oCo m (oTil (m + 1))) =
      defectO8 m θ faceAxis (fun _ => 2) (oTil m) := by
    refine orient_transfer8 m θ _ _ _ _ (oanti_C m _ hanti) (oTil_anti m) ?_
    intro f hf
    obtain ⟨c1, c2⟩ := cp1_shiftC m (p := f.1) (q := f.2.1)
    show oTil (m + 1) (shiftPoint (2 ^ m) 0 1 f.1)
        (shiftPoint (2 ^ m) 0 1 f.2.1) ↔ oTil m f.1 f.2.1
    exact (oTil_of_no_corner c1 c2).trans (faceC m (by omega) f hf)
  rw [eA, eB, eC]
  ring



 
/-- Exact recurrence for the H8 difference between numbering and
flipped-corner orientations. The difference of the two boundary residuals
is retained explicitly. -/
theorem defectO8_orientation_difference_succ
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    (defectO8 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) -
      defectO8 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1))) =
    (defectO8 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO8 m θ faceAxis (fun _ => 2) (oTil m)) +
    ((glueRHS8 m (sgK m θ faceAxis (oNum (m + 1))) -
        glueRHS8 m (sgK m θ (fun _ => 2) (oNum (m + 1))) ) -
      (glueRHS8 m (sgK m θ faceAxis (oTil (m + 1))) -
        glueRHS8 m (sgK m θ (fun _ => 2) (oTil (m + 1))) )) := by
  rw [defectO8_succ_num m hm θ, defectO8_succ_til m hm θ]
  ring



/-- The one edge reversed by oTil, in the local coordinates of copy B. -/
def p6FlipEndpoint (m : ℕ) (w : WSG m) : Prop :=
  w.1 = GCopy.B ∧
    (w.2.1.1 = ((2 ^ m - 1, 0) : Point) ∨ w.2.1.1 = (2 ^ m, 0))

theorem oNum_iff_oTil_of_left_away
    (n : ℕ) {p q : Point}
    (hpL : p ≠ ((2 ^ n - 1, 0) : Point))
    (hpR : p ≠ (2 ^ n, 0)) :
    oNum n p q ↔ oTil n p q := by
  have h1 : ¬ cp1 n p q := by
    rintro ⟨hp, -⟩
    exact hpL hp
  have h2 : ¬ cp1 n q p := by
    rintro ⟨-, hp⟩
    exact hpR hp
  exact (oTil_of_no_corner h1 h2).symm

theorem pHeO_row_congr
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o o' : Point → Point → Prop) [DecidableRel o] [DecidableRel o']
    (p q : Point) (i j : C2)
    (hrow : ∀ r, o p r ↔ o' p r) :
    pHeO m θ ax o p q i j = pHeO m θ ax o' p q i j := by
  classical
  by_cases hpq : p = q
  · subst q
    simp [pHeO]
  · by_cases hE : EdgeB m p.1 p.2 q.1 q.2 = true
    · have hor := hrow q
      by_cases ho : o p q
      · have ho' : o' p q := hor.mp ho
        simp [pHeO, hpq, hE, ho, ho']
      · have ho' : ¬ o' p q := fun hh => ho (hor.mpr hh)
        simp [pHeO, hpq, hE, ho, ho']
    · simp [pHeO, hpq, hE]

theorem Hc_num_til_row_eq_away
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (c : GCopy) (x y : Pt m × C2)
    (hrow : c ≠ GCopy.B ∨
      (x.1.1 ≠ ((2 ^ m - 1, 0) : Point) ∧ x.1.1 ≠ (2 ^ m, 0))) :
    Hc m θ ax (oNum (m + 1)) c x y =
      Hc m θ ax (oTil (m + 1)) c x y := by
  have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
  have hs : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  cases c with
  | A =>
      change pHeO m θ ax (oNum (m + 1)) x.1.1 y.1.1 x.2 y.2 =
        pHeO m θ ax (oTil (m + 1)) x.1.1 y.1.1 x.2 y.2
      apply pHeO_row_congr
      intro q
      have hpMem : x.1.1 ∈ vertexOrder m := List.mem_toFinset.mp x.1.2
      have hsum := vertexOrder_sum_le m x.1.1 hpMem
      have hpL : x.1.1 ≠ ((2 ^ (m + 1) - 1, 0) : Point) := by
        intro hh
        have hx := congrArg Prod.fst hh
        simp only [Prod.fst] at hx
        omega
      have hpR : x.1.1 ≠ (2 ^ (m + 1), 0) := by
        intro hh
        have hx := congrArg Prod.fst hh
        simp only [Prod.fst] at hx
        omega
      exact oNum_iff_oTil_of_left_away (m + 1) (p := x.1.1) (q := q) hpL hpR
  | B =>
      rcases hrow with hfalse | haway
      · exact (hfalse rfl).elim
      · change pHeO m θ ax (oBo m (oNum (m + 1))) x.1.1 y.1.1 x.2 y.2 =
          pHeO m θ ax (oBo m (oTil (m + 1))) x.1.1 y.1.1 x.2 y.2
        apply pHeO_row_congr
        intro q
        change oNum (m + 1) (shiftPoint (2 ^ m) 1 0 x.1.1)
            (shiftPoint (2 ^ m) 1 0 q) ↔
          oTil (m + 1) (shiftPoint (2 ^ m) 1 0 x.1.1)
            (shiftPoint (2 ^ m) 1 0 q)
        apply oNum_iff_oTil_of_left_away (m + 1)
        · intro hh
          apply haway.1
          apply Prod.ext
          · have hx := congrArg Prod.fst hh
            simp [shiftPoint] at hx
            omega
          · have hy := congrArg Prod.snd hh
            simp [shiftPoint] at hy
            omega
        · intro hh
          apply haway.2
          apply Prod.ext
          · have hx := congrArg Prod.fst hh
            simp [shiftPoint] at hx
            omega
          · have hy := congrArg Prod.snd hh
            simp [shiftPoint] at hy
            omega
  | C =>
      change pHeO m θ ax (oCo m (oNum (m + 1))) x.1.1 y.1.1 x.2 y.2 =
        pHeO m θ ax (oCo m (oTil (m + 1))) x.1.1 y.1.1 x.2 y.2
      apply pHeO_row_congr
      intro q
      change oNum (m + 1) (shiftPoint (2 ^ m) 0 1 x.1.1)
          (shiftPoint (2 ^ m) 0 1 q) ↔
        oTil (m + 1) (shiftPoint (2 ^ m) 0 1 x.1.1)
          (shiftPoint (2 ^ m) 0 1 q)
      apply oNum_iff_oTil_of_left_away (m + 1)
      · intro hh
        have hy : x.1.1.2 + 2 ^ m = 0 := by
          simpa [shiftPoint] using congrArg Prod.snd hh
        have hpos : 0 < 2 ^ m := by positivity
        omega
      · intro hh
        have hy : x.1.1.2 + 2 ^ m = 0 := by
          simpa [shiftPoint] using congrArg Prod.snd hh
        have hpos : 0 < 2 ^ m := by positivity
        omega

theorem sgK_num_til_row_eq_away_flip
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (w z : WSG m) (hw : ¬ p6FlipEndpoint m w) :
    sgK m θ ax (oNum (m + 1)) w z =
      sgK m θ ax (oTil (m + 1)) w z := by
  classical
  by_cases hcopy : w.1 = z.1
  · change (if w.1 = z.1 then
        Hc m θ ax (oNum (m + 1)) w.1 w.2 z.2 else 0) =
      (if w.1 = z.1 then
        Hc m θ ax (oTil (m + 1)) w.1 w.2 z.2 else 0)
    have haway : w.1 ≠ GCopy.B ∨
        (w.2.1.1 ≠ ((2 ^ m - 1, 0) : Point) ∧
          w.2.1.1 ≠ (2 ^ m, 0)) := by
      by_cases hb : w.1 = GCopy.B
      · right
        have hnot : ¬
            (w.2.1.1 = ((2 ^ m - 1, 0) : Point) ∨
              w.2.1.1 = (2 ^ m, 0)) := by
          intro h
          exact hw ⟨hb, h⟩
        exact ⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩
      · exact Or.inl hb
    simpa only [if_pos hcopy] using
      Hc_num_til_row_eq_away m hm θ ax w.1 w.2 z.2 haway
  · simp [sgK, blockK, hcopy]

theorem glued_B_point
    (m : ℕ) {w : WSG m} (hw : (sgGlue m).g w) (hb : w.1 = GCopy.B) :
    w.2.1.1 = (0, 0) ∨ w.2.1.1 = (0, 2 ^ m) := by
  change ∃ w', glW m w w' at hw
  obtain ⟨w', hw⟩ := hw
  have hgl : gl m w.1 w.2.1.1 w'.1 w'.2.1.1 := hw.1
  have hgl' :
      (w.2.1.1 = (0, 0) ∧ w'.1 = GCopy.A ∧
        w'.2.1.1 = (2 ^ m, 0)) ∨
      (w.2.1.1 = (0, 2 ^ m) ∧ w'.1 = GCopy.C ∧
        w'.2.1.1 = (2 ^ m, 0)) := by
    simpa [gl, hb] using hgl
  rcases hgl' with ⟨hp, -, -⟩ | ⟨hp, -, -⟩
  · exact Or.inl hp
  · exact Or.inr hp

theorem sgK_pow_zero_from_glue_to_flip
    (m n : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (w z : WSG m) (hw : (sgGlue m).g w)
    (hz : p6FlipEndpoint m z) (hn : n ≤ 4) :
    (sgK m θ ax o ^ n) w z = 0 := by
  classical
  by_cases hb : w.1 = GCopy.B
  · have hpB : w.2.1.1 = (0, 0) ∨ w.2.1.1 = (0, 2 ^ m) :=
      glued_B_point m hw hb
    have hs : 7 ≤ 2 ^ m :=
      calc 7 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases hz with ⟨hzB, hzpt⟩
    have hxw : w.2.1.1.1 = 0 := by
      rcases hpB with hp | hp <;> simp [hp]
    rcases hzpt with hzpt | hzpt
    · apply sgK_pow_entry_zero_of_coord_gap m n θ ax o w z
      right
      left
      rw [hxw, congrArg Prod.fst hzpt]
      omega
    · apply sgK_pow_entry_zero_of_coord_gap m n θ ax o w z
      right
      left
      rw [hxw, congrArg Prod.fst hzpt]
      omega
  · have hcopy : w.1 ≠ z.1 := by
      intro h
      apply hb
      rw [hz.1] at h
      exact h
    change (blockK (Hc m θ ax o) ^ n) w z = 0
    rw [blockK_pow_local]
    simp [blockK, hcopy]

theorem sgK_pow_row_eq_num_til_on_glue
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (w : WSG m) (hw : (sgGlue m).g w) :
    ∀ n, n ≤ 5 → ∀ z,
      (sgK m θ ax (oNum (m + 1)) ^ n) w z =
        (sgK m θ ax (oTil (m + 1)) ^ n) w z := by
  classical
  intro n
  induction n with
  | zero =>
      intro hn z
      simp
  | succ n ih =>
      intro hn z
      have hn4 : n ≤ 4 := by omega
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hflip : p6FlipEndpoint m y
      · have hnum := sgK_pow_zero_from_glue_to_flip
          m n hm θ ax (oNum (m + 1)) w y hw hflip hn4
        have htil := sgK_pow_zero_from_glue_to_flip
          m n hm θ ax (oTil (m + 1)) w y hw hflip hn4
        rw [hnum, htil]
        simp
      · have hn5 : n ≤ 5 := by omega
        rw [ih hn5 y, sgK_num_til_row_eq_away_flip m hm θ ax y z hflip]

theorem sgK_pow_diag_eq_num_til_on_glue
    (m n : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (w : WSG m) (hw : (sgGlue m).g w) (hn : n ≤ 5) :
    (sgK m θ ax (oNum (m + 1)) ^ n) w w =
      (sgK m θ ax (oTil (m + 1)) ^ n) w w :=
  sgK_pow_row_eq_num_til_on_glue m hm θ ax w hw n hn w




/-- The flipped edge is farther than six steps from every glued state in
copy B once m ≥ 4. This is the degree-eight analogue of the p=6 bound. -/
theorem sgK_pow_zero_from_glue_to_flip_up_to_six
    (m n : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (w z : WSG m) (hw : (sgGlue m).g w)
    (hz : p6FlipEndpoint m z) (hn : n ≤ 6) :
    (sgK m θ ax o ^ n) w z = 0 := by
  classical
  by_cases hb : w.1 = GCopy.B
  · have hpB : w.2.1.1 = (0, 0) ∨ w.2.1.1 = (0, 2 ^ m) :=
      glued_B_point m hw hb
    have hpow : 16 ≤ 2 ^ m := by
      calc
        16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hside : 7 < 2 ^ m - 1 := by omega
    rcases hz with ⟨hzB, hzpt⟩
    have hxw : w.2.1.1.1 = 0 := by
      rcases hpB with hp | hp <;> simp [hp]
    rcases hzpt with hzpt | hzpt
    · apply sgK_pow_entry_zero_of_coord_gap m n θ ax o w z
      right
      left
      rw [hxw, congrArg Prod.fst hzpt]
      omega
    · apply sgK_pow_entry_zero_of_coord_gap m n θ ax o w z
      right
      left
      rw [hxw, congrArg Prod.fst hzpt]
      omega
  · have hcopy : w.1 ≠ z.1 := by
      intro h
      apply hb
      rw [hz.1] at h
      exact h
    change (blockK (Hc m θ ax o) ^ n) w z = 0
    rw [blockK_pow_local]
    simp [blockK, hcopy]

/-- For levels m ≥ 4, every row of K^n starting at a glued state is
unchanged by the single exceptional orientation flip for n ≤ 7. The
induction uses the preceding distance bound only at the penultimate step. -/
theorem sgK_pow_row_eq_num_til_on_glue_up_to_seven
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (w : WSG m) (hw : (sgGlue m).g w) :
    ∀ n, n ≤ 7 → ∀ z,
      (sgK m θ ax (oNum (m + 1)) ^ n) w z =
        (sgK m θ ax (oTil (m + 1)) ^ n) w z := by
  classical
  intro n
  induction n with
  | zero =>
      intro hn z
      simp
  | succ n ih =>
      intro hn z
      have hn6 : n ≤ 6 := by omega
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hflip : p6FlipEndpoint m y
      · have hnum := sgK_pow_zero_from_glue_to_flip_up_to_six
          m n hm θ ax (oNum (m + 1)) w y hw hflip hn6
        have htil := sgK_pow_zero_from_glue_to_flip_up_to_six
          m n hm θ ax (oTil (m + 1)) w y hw hflip hn6
        rw [hnum, htil]
        simp
      · have hn7 : n ≤ 7 := by omega
        rw [ih hn7 y, sgK_num_til_row_eq_away_flip m (by omega) θ ax y z hflip]

/-- Diagonal specialization of the seven-power glued-row comparison. -/
theorem sgK_pow_diag_eq_num_til_on_glue_up_to_seven
    (m n : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (w : WSG m) (hw : (sgGlue m).g w) (hn : n ≤ 7) :
    (sgK m θ ax (oNum (m + 1)) ^ n) w w =
      (sgK m θ ax (oTil (m + 1)) ^ n) w w :=
  sgK_pow_row_eq_num_til_on_glue_up_to_seven m hm θ ax w hw n hn w


/-- The complete H8 boundary correction is unchanged by the exceptional
orientation flip once the glued rows agree through degree seven. -/
theorem glueRHS8_num_eq_til
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis) :
    glueRHS8 m (sgK m θ ax (oNum (m + 1))) =
      glueRHS8 m (sgK m θ ax (oTil (m + 1))) := by
  apply glueRHS8_congr_of_glued_row_pow m hm θ ax
    (oNum (m + 1)) (oTil (m + 1))
    (oNum_anti (m + 1)) (oTil_anti (m + 1))
  intro w hw n hn z
  exact sgK_pow_row_eq_num_til_on_glue_up_to_seven
    m hm θ ax w hw n hn z

/-- The H8 orientation gap is level-independent from level four onward.
Its finite value at level four is retained; this is not a claim that the gap
vanishes. -/
theorem defectO8_orientation_difference_succ_invariant
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) :
    (defectO8 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) -
      defectO8 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1))) =
    (defectO8 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO8 m θ faceAxis (fun _ => 2) (oTil m)) := by
  rw [defectO8_orientation_difference_succ m (by omega) θ,
    glueRHS8_num_eq_til m hm θ faceAxis,
    glueRHS8_num_eq_til m hm θ (fun _ => 2)]
  ring

/-- All higher-level H8 orientation gaps reduce to the exact level-four
base value. No zero value is asserted for that base gap. -/
theorem defectO8_orientation_difference_eq_level4
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) :
    (defectO8 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO8 m θ faceAxis (fun _ => 2) (oTil m)) =
    (defectO8 4 θ faceAxis (fun _ => 2) (oNum 4) -
      defectO8 4 θ faceAxis (fun _ => 2) (oTil 4)) := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [defectO8_orientation_difference_succ_invariant n hn θ, ih]





/-- The p=6 boundary residual is independent of the single flipped edge.
Every glued diagonal of powers up to five is unchanged, since a walk of length
at most five from a glued corner cannot reach either endpoint of that edge. -/
theorem glueRHS6_highPowerResidual_num_eq_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax ax' : ℕ → Axis) :
    glueRHS6_highPowerResidual m
        (sgK m θ ax (oNum (m + 1)))
        (sgK m θ ax' (oNum (m + 1))) =
      glueRHS6_highPowerResidual m
        (sgK m θ ax (oTil (m + 1)))
        (sgK m θ ax' (oTil (m + 1))) := by
  classical
  have hsum15 (a : ℕ → Axis) :
      (∑ x, if (sgGlue m).g x then
        (sgK m θ a (oNum (m + 1)) ^ 1) x x *
          (sgK m θ a (oNum (m + 1)) ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x)
        else 0) =
      (∑ x, if (sgGlue m).g x then
        (sgK m θ a (oTil (m + 1)) ^ 1) x x *
          (sgK m θ a (oTil (m + 1)) ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x)
        else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hgl : (sgGlue m).g x
    · have hglσ := (sgGlue m).g_σ x hgl
      simp only [hgl, ↓reduceIte]
      rw [sgK_pow_diag_eq_num_til_on_glue m 1 hm θ a x hgl (by omega),
        sgK_pow_diag_eq_num_til_on_glue m 5 hm θ a ((sgGlue m).σ x)
          hglσ (by omega)]
    · simp [hgl]
  have hsum24 (a : ℕ → Axis) :
      (∑ x, if (sgGlue m).g x then
        (sgK m θ a (oNum (m + 1)) ^ 2) x x *
          (sgK m θ a (oNum (m + 1)) ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x)
        else 0) =
      (∑ x, if (sgGlue m).g x then
        (sgK m θ a (oTil (m + 1)) ^ 2) x x *
          (sgK m θ a (oTil (m + 1)) ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x)
        else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hgl : (sgGlue m).g x
    · have hglσ := (sgGlue m).g_σ x hgl
      simp only [hgl, ↓reduceIte]
      rw [sgK_pow_diag_eq_num_til_on_glue m 2 hm θ a x hgl (by omega),
        sgK_pow_diag_eq_num_til_on_glue m 4 hm θ a ((sgGlue m).σ x)
          hglσ (by omega)]
    · simp [hgl]
  unfold glueRHS6_highPowerResidual
  rw [hsum15 ax, hsum15 ax', hsum24 ax, hsum24 ax']

/-- The p=6 orientation difference is unchanged from level m to m+1.
This follows from the exact difference recurrence and the proved invariance
of the boundary residual under the single flipped edge. The common difference
is not claimed to be zero. -/
theorem defectO6_orientation_difference_succ_invariant
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    (defectO6 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) -
      defectO6 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1))) =
    (defectO6 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO6 m θ faceAxis (fun _ => 2) (oTil m)) := by
  rw [defectO6_orientation_difference_succ_highPower m hm θ,
    glueRHS6_highPowerResidual_num_eq_til m hm θ faceAxis (fun _ => 2)]
  ring

/-- At every level m ≥ 3, the orientation difference is the same as its
level-three value. This packages the adjacent-level invariance into a single
reduction to the finite base level; it does not assert that the value is zero. -/
theorem defectO6_orientation_difference_eq_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    (defectO6 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO6 m θ faceAxis (fun _ => 2) (oTil m)) =
    (defectO6 3 θ faceAxis (fun _ => 2) (oNum 3) -
      defectO6 3 θ faceAxis (fun _ => 2) (oTil 3)) := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [defectO6_orientation_difference_succ_invariant n hn θ, ih]

/-- The numbering-orientation sixth-moment recurrence has one explicit
boundary residual after the orientation gap is reduced to level three.
Thus the remaining affine-recurrence step is to show this residual is
independent of m; no vanishing of the residual is assumed. -/
theorem defectO6_succ_num_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    defectO6 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      3 * defectO6 m θ faceAxis (fun _ => 2) (oNum m) -
        (defectO6 3 θ faceAxis (fun _ => 2) (oNum 3) -
          defectO6 3 θ faceAxis (fun _ => 2) (oTil 3)) +
        (glueRHS6 m (sgK m θ faceAxis (oNum (m + 1))) -
          glueRHS6 m (sgK m θ (fun _ => 2) (oNum (m + 1))) ) := by
  rw [defectO6_succ_num m hm θ]
  rw [← defectO6_orientation_difference_eq_level3 m hm θ]
  ring

/-- Full entrywise transport for copy A, including diagonal entries.
Off-diagonal entries follow from the edge-copy identity; the diagonal case
uses the local degree recurrence. -/
theorem pHeO_succ_A_local_entry
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (hpX : p ≠ (2 ^ m, 0)) (hpY : p ≠ (0, 2 ^ m))
    (i j : C2) :
    pHeO (m + 1) θ ax o p q i j = pHeO m θ ax o p q i j := by
  by_cases hpq : p = q
  · subst q
    simp only [pHeO_diag, pdeg_succ_A_local m hp hpX hpY]
  · exact pHeO_succ_A m θ ax o hp hq hpq i j

/-- Full entrywise transport for copy B, including diagonal entries. -/
theorem pHeO_succ_B_local_entry
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (hp0 : p ≠ (0, 0)) (hpY : p ≠ (0, 2 ^ m))
    (i j : C2) :
    pHeO (m + 1) θ ax o
        (shiftPoint (2 ^ m) 1 0 p) (shiftPoint (2 ^ m) 1 0 q) i j =
      pHeO m θ ax (oBo m o) p q i j := by
  by_cases hpq : p = q
  · subst q
    simp only [pHeO_diag, pdeg_succ_B_local m hp hp0 hpY]
  · exact pHeO_succ_B m θ ax o hax hp hq hpq i j

/-- Full entrywise transport for copy C, including diagonal entries. -/
theorem pHeO_succ_C_local_entry
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (hp0 : p ≠ (0, 0)) (hpX : p ≠ (2 ^ m, 0))
    (i j : C2) :
    pHeO (m + 1) θ ax o
        (shiftPoint (2 ^ m) 0 1 p) (shiftPoint (2 ^ m) 0 1 q) i j =
      pHeO m θ ax (oCo m o) p q i j := by
  by_cases hpq : p = q
  · subst q
    simp only [pHeO_diag, pdeg_succ_C_local m hp hp0 hpX]
  · exact pHeO_succ_C m θ ax o hax hp hq hpq i j


/-- A nonzero point-operator entry can only preserve its geometric coordinate
or traverse one graph edge, so each coordinate changes by at most one. -/
theorem pHeO_entry_coord_dist
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (p q : Point) (i j : C2)
    (h : pHeO m θ ax o p q i j ≠ 0) :
    p.1 ≤ q.1 + 1 ∧ q.1 ≤ p.1 + 1 ∧
      p.2 ≤ q.2 + 1 ∧ q.2 ≤ p.2 + 1 := by
  by_cases hpq : p = q
  · subst q
    exact ⟨by omega, by omega, by omega, by omega⟩
  · by_cases hE : EdgeB m p.1 p.2 q.1 q.2 = true
    · exact EdgeB_dist hE
    · exact (h (pHeO_zero_of_not_edge m θ ax o hpq hE i j)).elim

/-- Every nonzero entry of a power of pOpO is supported within coordinate
distance equal to the power. This point-level locality estimate will be used
to compare the fourth- and fifth-power diagonals at outer corners across levels. -/
theorem pOpO_pow_entry_coord_dist
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    ∀ n (x y : Pt m × C2), (pOpO m θ ax o ^ n) x y ≠ 0 →
      x.1.1.1 ≤ y.1.1.1 + n ∧ y.1.1.1 ≤ x.1.1.1 + n ∧
      x.1.1.2 ≤ y.1.1.2 + n ∧ y.1.1.2 ≤ x.1.1.2 + n := by
  exact pow_entry_coord_dist
    (K := pOpO m θ ax o)
    (coord := fun x : Pt m × C2 => x.1.1)
    (by
      intro x y hxy
      exact pHeO_entry_coord_dist m θ ax o x.1.1 y.1.1 x.2 y.2
        (by simpa [pOpO] using hxy))

/-- Pulling the numbering orientation at level m+1 back to copy B preserves
the level-m order, including the shared origin. The origin remains earlier
than every genuinely new B vertex. -/
theorem oBo_num_iff_oNum (m : ℕ) {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m) :
    oBo m (oNum (m + 1)) p q ↔ oNum m p q := by
  by_cases hp0 : p = (0, 0)
  · subst p
    by_cases hq0 : q = (0, 0)
    · subst q
      simp [oBo, oNum]
    · have hnew :
          (vertexOrder m).length ≤
            vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 q) := by
        rw [vIdx_succ_B hq hq0]
        omega
      have horigin :
          vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 (0, 0)) <
            (vertexOrder m).length := by
        have hs : shiftPoint (2 ^ m) 1 0 (0, 0) = (2 ^ m, 0) := by
          simp [shiftPoint]
        rw [hs, vIdx_succ_of_mem (cornerX_mem m)]
        exact List.idxOf_lt_length_of_mem (cornerX_mem m)
      change
        vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 (0, 0)) ≤
            vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 q) ↔
          vIdx m (0, 0) ≤ vIdx m q
      have hlocal : vIdx m (0, 0) ≤ vIdx m q := by
        rw [vIdx_origin]
        omega
      have hparent :
          vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 (0, 0)) ≤
            vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 q) := by
        omega
      exact iff_of_true hparent hlocal
  · by_cases hq0 : q = (0, 0)
    · subst q
      have hnew :
          (vertexOrder m).length ≤
            vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 p) := by
        rw [vIdx_succ_B hp hp0]
        omega
      have horigin :
          vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 (0, 0)) <
            (vertexOrder m).length := by
        have hs : shiftPoint (2 ^ m) 1 0 (0, 0) = (2 ^ m, 0) := by
          simp [shiftPoint]
        rw [hs, vIdx_succ_of_mem (cornerX_mem m)]
        exact List.idxOf_lt_length_of_mem (cornerX_mem m)
      change
        vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 p) ≤
            vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 (0, 0)) ↔
          vIdx m p ≤ vIdx m (0, 0)
      have hlocal : ¬ vIdx m p ≤ vIdx m (0, 0) := by
        rw [vIdx_origin]
        have hpos := vIdx_pos_of_ne (m := m) hp0
        omega
      have hparent :
          ¬ vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 p) ≤
            vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 (0, 0)) := by
        omega
      exact iff_of_false hparent hlocal
    · change
        vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 p) ≤
            vIdx (m + 1) (shiftPoint (2 ^ m) 1 0 q) ↔
          vIdx m p ≤ vIdx m q
      exact (vIdx_succ_B_le_iff m ⟨p, hp, hp0⟩ ⟨q, hq, hq0⟩).symm

/-- The B-copy kernel at level m, with the numbering orientation inherited
from level m+1, is exactly the parent kernel with orientation oNum m.
The proof uses the copy-B orientation equivalence only on actual graph edges. -/
theorem Hc_B_num_eq_parent
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (x y : Pt m × C2) :
    Hc m θ ax (oNum (m + 1)) GCopy.B x y =
      pOpO m θ ax (oNum m) x y := by
  change pHeO m θ ax (oBo m (oNum (m + 1)))
      x.1.1 y.1.1 x.2 y.2 =
    pHeO m θ ax (oNum m) x.1.1 y.1.1 x.2 y.2
  exact pHeO_orient_congr m θ ax
    (oBo m (oNum (m + 1))) (oNum m)
    (by
      intro p q hpq hE hfl
      have hm := EdgeB_mem m p.1 p.2 q.1 q.2 hE
      have hp : p ∈ vertexOrder m :=
        (mem_vertexOrder_iff m p).mpr hm.1
      have hq : q ∈ vertexOrder m :=
        (mem_vertexOrder_iff m q).mpr hm.2
      exact oBo_num_iff_oNum m hp hq)
    x.1.1 y.1.1 x.2 y.2

/-- The C-copy kernel at level m, with numbering inherited from level m+1,
is the parent kernel with the corner-flipped orientation oTil m.
The exceptional edge ending at (2^m, 0) is handled by faceC. -/
theorem Hc_C_num_eq_parent_til
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hanti : OAnti (m + 1) (oNum (m + 1)))
    (x y : Pt m × C2) :
    Hc m θ ax (oNum (m + 1)) GCopy.C x y =
      pOpO m θ ax (oTil m) x y := by
  change pHeO m θ ax (oCo m (oNum (m + 1)))
      x.1.1 y.1.1 x.2 y.2 =
    pHeO m θ ax (oTil m) x.1.1 y.1.1 x.2 y.2
  exact pHeO_orient_congr m θ ax
    (oCo m (oNum (m + 1))) (oTil m)
    (by
      intro p q hpq hE hfl
      have hmE := EdgeB_mem m p.1 p.2 q.1 q.2 hE
      have hp : p ∈ vertexOrder m :=
        (mem_vertexOrder_iff m p).mpr hmE.1
      have hq : q ∈ vertexOrder m :=
        (mem_vertexOrder_iff m q).mpr hmE.2
      have fl : ∀ a b : Point, (a, b) ∈ fluxEdges m →
          ∃ f ∈ facesExact m, f.1 = a ∧ f.2.1 = b := by
        intro a b hab
        obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hab
        have hle := flux_edge_order m f hf
        have h' : fluxEdge f = (f.1, f.2.1) := by
          simp [fluxEdge, hle]
        rw [h'] at hfe
        exact ⟨f, hf, (Prod.mk.inj hfe).1, (Prod.mk.inj hfe).2⟩
      have hantiCo : OAnti m (oCo m (oNum (m + 1))) :=
        oanti_C m _ hanti
      by_cases hle : p ≤ q
      · rw [if_pos hle] at hfl
        obtain ⟨f, hf, h1, h2⟩ := fl p q hfl
        rw [← h1, ← h2]
        exact faceC m hm f hf
      · rw [if_neg hle] at hfl
        obtain ⟨f, hf, h1, h2⟩ := fl q p hfl
        have h3 := faceC m hm f hf
        rw [h1, h2] at h3
        rw [hantiCo p q hp hq hpq, oTil_anti m p q hp hq hpq]
        exact not_congr h3)
    x.1.1 y.1.1 x.2 y.2


/-- Across copy A, the level-(m+1) numbering orientation restricts to
the level-m numbering orientation on every old edge. -/
theorem pHeO_succ_A_num_entry
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (hpX : p ≠ (2 ^ m, 0)) (hpY : p ≠ (0, 2 ^ m))
    (i j : C2) :
    pHeO (m + 1) θ ax (oNum (m + 1)) p q i j =
      pHeO m θ ax (oNum m) p q i j := by
  calc
    pHeO (m + 1) θ ax (oNum (m + 1)) p q i j =
        pHeO m θ ax (oNum (m + 1)) p q i j :=
      pHeO_succ_A_local_entry m θ ax (oNum (m + 1))
        hp hq hpX hpY i j
    _ = pHeO m θ ax (oNum m) p q i j :=
      pHeO_orient_congr m θ ax (oNum (m + 1)) (oNum m)
        (by
          intro a b hab hE hfl
          have hm := EdgeB_mem m a.1 a.2 b.1 b.2 hE
          have ha : a ∈ vertexOrder m :=
            (mem_vertexOrder_iff m a).mpr hm.1
          have hb : b ∈ vertexOrder m :=
            (mem_vertexOrder_iff m b).mpr hm.2
          unfold oNum
          rw [vIdx_succ_of_mem ha, vIdx_succ_of_mem hb])
        p q i j

/-- Across copy B, the parent entry is transported with the parent numbering
orientation, provided the axis labels are periodic over the B face block. -/
theorem pHeO_succ_B_num_entry
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (hp0 : p ≠ (0, 0)) (hpY : p ≠ (0, 2 ^ m))
    (i j : C2) :
    pHeO (m + 1) θ ax (oNum (m + 1))
        (shiftPoint (2 ^ m) 1 0 p) (shiftPoint (2 ^ m) 1 0 q) i j =
      pHeO m θ ax (oNum m) p q i j := by
  calc
    pHeO (m + 1) θ ax (oNum (m + 1))
        (shiftPoint (2 ^ m) 1 0 p) (shiftPoint (2 ^ m) 1 0 q) i j =
        pHeO m θ ax (oBo m (oNum (m + 1))) p q i j :=
      pHeO_succ_B_local_entry m θ ax (oNum (m + 1)) hax
        hp hq hp0 hpY i j
    _ = pHeO m θ ax (oNum m) p q i j :=
      pHeO_orient_congr m θ ax (oBo m (oNum (m + 1))) (oNum m)
        (by
          intro a b hab hE hfl
          have hm := EdgeB_mem m a.1 a.2 b.1 b.2 hE
          have ha : a ∈ vertexOrder m :=
            (mem_vertexOrder_iff m a).mpr hm.1
          have hb : b ∈ vertexOrder m :=
            (mem_vertexOrder_iff m b).mpr hm.2
          exact oBo_num_iff_oNum m ha hb)
        p q i j

/-- Across copy C, the inherited numbering pulls back to the corner-flipped
orientation oTil m. The exceptional orientation is retained explicitly. -/
theorem pHeO_succ_C_num_entry_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (hanti : OAnti (m + 1) (oNum (m + 1)))
    {p q : Point}
    (hp : p ∈ vertexOrder m) (hq : q ∈ vertexOrder m)
    (hp0 : p ≠ (0, 0)) (hpX : p ≠ (2 ^ m, 0))
    (i j : C2) :
    pHeO (m + 1) θ ax (oNum (m + 1))
        (shiftPoint (2 ^ m) 0 1 p) (shiftPoint (2 ^ m) 0 1 q) i j =
      pHeO m θ ax (oTil m) p q i j := by
  calc
    pHeO (m + 1) θ ax (oNum (m + 1))
        (shiftPoint (2 ^ m) 0 1 p) (shiftPoint (2 ^ m) 0 1 q) i j =
        pHeO m θ ax (oCo m (oNum (m + 1))) p q i j :=
      pHeO_succ_C_local_entry m θ ax (oNum (m + 1)) hax
        hp hq hp0 hpX i j
    _ = pHeO m θ ax (oTil m) p q i j := by
      have horient := Hc_C_num_eq_parent_til m (by omega) θ ax hanti
        ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt m), i)
        ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt m), j)
      change pHeO m θ ax (oCo m (oNum (m + 1))) p q i j =
        pHeO m θ ax (oTil m) p q i j at horient
      exact horient


/-- At the outer corner O, all entries whose endpoints lie in the
coordinate box [0,2]² agree with the parent-level operator. -/
theorem pHeO_corner_O_box_entry
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 2) (hpy : p.2 ≤ 2)
    (hqx : q.1 ≤ 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    pHeO (m + 1) θ ax (oNum (m + 1)) p q i j =
      pHeO m θ ax (oNum m) p q i j := by
  obtain ⟨hp', hpX, hpY⟩ :=
    corner_O_radius_two_transport m hm hp hpx hpy
  obtain ⟨hq', _, _⟩ :=
    corner_O_radius_two_transport m hm hq hqx hqy
  exact pHeO_succ_A_num_entry m θ ax hp' hq' hpX hpY i j

/-- At the outer corner O, all entries whose endpoints lie in the
coordinate box [0,3]² agree with the parent-level operator. -/
theorem pHeO_corner_O_radius_three_entry
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 3) (hpy : p.2 ≤ 3)
    (hqx : q.1 ≤ 3) (hqy : q.2 ≤ 3)
    (i j : C2) :
    pHeO (m + 1) θ ax (oNum (m + 1)) p q i j =
      pHeO m θ ax (oNum m) p q i j := by
  obtain ⟨hp', hpX, hpY⟩ :=
    corner_O_radius_three_transport m hm hp hpx hpy
  obtain ⟨hq', _, _⟩ :=
    corner_O_radius_three_transport m hm hq hqx hqy
  exact pHeO_succ_A_num_entry m θ ax hp' hq' hpX hpY i j


/-- At the outer corner X, entries inside the radius-two coordinate box
pull back to copy B with the ordinary parent numbering orientation. -/
theorem pHeO_corner_X_box_entry
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : 2 ^ (m + 1) ≤ p.1 + 2) (hpy : p.2 ≤ 2)
    (hqx : 2 ^ (m + 1) ≤ q.1 + 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    ∃ p' q' : Point,
      p' ∈ vertexOrder m ∧ q' ∈ vertexOrder m ∧
      p = shiftPoint (2 ^ m) 1 0 p' ∧
      q = shiftPoint (2 ^ m) 1 0 q' ∧
      pHeO (m + 1) θ ax (oNum (m + 1)) p q i j =
        pHeO m θ ax (oNum m) p' q' i j := by
  rcases (corner_X_radius_two_box_iff m hm hp).mp ⟨hpx, hpy⟩ with
    ⟨p', hp', hpx', hpy', rfl⟩
  rcases (corner_X_radius_two_box_iff m hm hq).mp ⟨hqx, hqy⟩ with
    ⟨q', hq', hqx', hqy', rfl⟩
  have hpow : 2 < 2 ^ m := by
    calc
      2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hp0 : p' ≠ (0, 0) := by
    intro heq
    have hcoord : p'.1 = 0 := congrArg Prod.fst heq
    omega
  have hpY : p' ≠ (0, 2 ^ m) := by
    intro heq
    have hcoord : p'.1 = 0 := congrArg Prod.fst heq
    omega
  refine ⟨p', q', hp', hq', rfl, rfl, ?_⟩
  exact pHeO_succ_B_num_entry m θ ax hax hp' hq' hp0 hpY i j

/-- At the outer corner Y, entries inside the radius-two coordinate box
pull back to copy C with the exceptional corner-flipped orientation. -/
theorem pHeO_corner_Y_box_entry
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 2) (hpy : 2 ^ (m + 1) ≤ p.2 + 2)
    (hqx : q.1 ≤ 2) (hqy : 2 ^ (m + 1) ≤ q.2 + 2)
    (i j : C2) :
    ∃ p' q' : Point,
      p' ∈ vertexOrder m ∧ q' ∈ vertexOrder m ∧
      p = shiftPoint (2 ^ m) 0 1 p' ∧
      q = shiftPoint (2 ^ m) 0 1 q' ∧
      pHeO (m + 1) θ ax (oNum (m + 1)) p q i j =
        pHeO m θ ax (oTil m) p' q' i j := by
  rcases (corner_Y_radius_two_box_iff m hm hp).mp ⟨hpx, hpy⟩ with
    ⟨p', hp', hpx', hpy', rfl⟩
  rcases (corner_Y_radius_two_box_iff m hm hq).mp ⟨hqx, hqy⟩ with
    ⟨q', hq', hqx', hqy', rfl⟩
  have hpow : 2 < 2 ^ m := by
    calc
      2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hp0 : p' ≠ (0, 0) := by
    intro heq
    have hcoord : p'.2 = 0 := congrArg Prod.snd heq
    omega
  have hpX : p' ≠ (2 ^ m, 0) := by
    intro heq
    have hcoord : p'.2 = 0 := congrArg Prod.snd heq
    omega
  refine ⟨p', q', hp', hq', rfl, rfl, ?_⟩
  exact pHeO_succ_C_num_entry_til m hm θ ax hax (oNum_anti (m + 1))
    hp' hq' hp0 hpX i j


/-- A nonzero two-step entry from the outer corner O can only reach
the coordinate box [0,2]². -/
theorem pOpO_pow_two_corner_O_support
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    {x y : Pt m × C2}
    (hx : x.1.1 = (0, 0))
    (hy : (pOpO m θ ax o ^ 2) x y ≠ 0) :
    y.1.1.1 ≤ 2 ∧ y.1.1.2 ≤ 2 := by
  have hdist := pOpO_pow_entry_coord_dist m θ ax o 2 x y hy
  have hx1 : x.1.1.1 = 0 := congrArg Prod.fst hx
  have hx2 : x.1.1.2 = 0 := congrArg Prod.snd hx
  omega

/-- A nonzero two-step entry from the outer corner X can only reach
the coordinate box x ≥ 2^m - 2 and y ≤ 2. -/
theorem pOpO_pow_two_corner_X_support
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    {x y : Pt m × C2}
    (hx : x.1.1 = (2 ^ m, 0))
    (hy : (pOpO m θ ax o ^ 2) x y ≠ 0) :
    2 ^ m ≤ y.1.1.1 + 2 ∧ y.1.1.2 ≤ 2 := by
  have hdist := pOpO_pow_entry_coord_dist m θ ax o 2 x y hy
  have hx1 : x.1.1.1 = 2 ^ m := congrArg Prod.fst hx
  have hx2 : x.1.1.2 = 0 := congrArg Prod.snd hx
  omega

/-- A nonzero two-step entry from the outer corner Y can only reach
the coordinate box x ≤ 2 and y ≥ 2^m - 2. -/
theorem pOpO_pow_two_corner_Y_support
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    {x y : Pt m × C2}
    (hx : x.1.1 = (0, 2 ^ m))
    (hy : (pOpO m θ ax o ^ 2) x y ≠ 0) :
    y.1.1.1 ≤ 2 ∧ 2 ^ m ≤ y.1.1.2 + 2 := by
  have hdist := pOpO_pow_entry_coord_dist m θ ax o 2 x y hy
  have hx1 : x.1.1.1 = 0 := congrArg Prod.fst hx
  have hx2 : x.1.1.2 = 2 ^ m := congrArg Prod.snd hx
  omega


/-- The numbering orientation at level m+2 restricts to the one at level
m+1 on every level-(m+1) vertex. This is the orientation index needed when
comparing the p=6 residual at adjacent refinement levels. -/
theorem oNum_succ_restrict (m : ℕ) {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1)) :
    oNum (m + 2) p q ↔ oNum (m + 1) p q := by
  unfold oNum
  rw [vIdx_succ_of_mem hp, vIdx_succ_of_mem hq]

/-- Across the O/A corner box, the entry at level m+1 with the orientation
used by the next residual, oNum (m+2), agrees with the parent entry using
oNum (m+1). -/
theorem pHeO_corner_O_box_entry_next_num
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 2) (hpy : p.2 ≤ 2)
    (hqx : q.1 ≤ 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    pHeO (m + 1) θ ax (oNum (m + 2)) p q i j =
      pHeO m θ ax (oNum (m + 1)) p q i j := by
  obtain ⟨hp', hpX, hpY⟩ :=
    corner_O_radius_two_transport m hm hp hpx hpy
  obtain ⟨hq', _, _⟩ :=
    corner_O_radius_two_transport m hm hq hqx hqy
  calc
    pHeO (m + 1) θ ax (oNum (m + 2)) p q i j =
        pHeO m θ ax (oNum (m + 2)) p q i j :=
      pHeO_succ_A_local_entry m θ ax (oNum (m + 2))
        hp' hq' hpX hpY i j
    _ = pHeO m θ ax (oNum (m + 1)) p q i j :=
      pHeO_orient_congr m θ ax (oNum (m + 2)) (oNum (m + 1))
        (by
          intro a b hab hE hfl
          have hmEdge := EdgeB_mem m a.1 a.2 b.1 b.2 hE
          have ha : a ∈ vertexOrder m :=
            (mem_vertexOrder_iff m a).mpr hmEdge.1
          have hb : b ∈ vertexOrder m :=
            (mem_vertexOrder_iff m b).mpr hmEdge.2
          have ha' : a ∈ vertexOrder (m + 1) := by
            rw [mem_vertexOrder_succ_iff]
            exact Or.inl ha
          have hb' : b ∈ vertexOrder (m + 1) := by
            rw [mem_vertexOrder_succ_iff]
            exact Or.inl hb
          exact oNum_succ_restrict m ha' hb')
        p q i j


/-- Across the O/A radius-three box, the entry at level m+1 with
the orientation used by the next residual, oNum (m+2), agrees with the
parent entry using oNum (m+1). -/
theorem pHeO_corner_O_radius_three_entry_next_num
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 3) (hpy : p.2 ≤ 3)
    (hqx : q.1 ≤ 3) (hqy : q.2 ≤ 3)
    (i j : C2) :
    pHeO (m + 1) θ ax (oNum (m + 2)) p q i j =
      pHeO m θ ax (oNum (m + 1)) p q i j := by
  obtain ⟨hp', hpX, hpY⟩ :=
    corner_O_radius_three_transport m hm hp hpx hpy
  obtain ⟨hq', _, _⟩ :=
    corner_O_radius_three_transport m hm hq hqx hqy
  calc
    pHeO (m + 1) θ ax (oNum (m + 2)) p q i j =
        pHeO m θ ax (oNum (m + 2)) p q i j :=
      pHeO_succ_A_local_entry m θ ax (oNum (m + 2))
        hp' hq' hpX hpY i j
    _ = pHeO m θ ax (oNum (m + 1)) p q i j :=
      pHeO_orient_congr m θ ax (oNum (m + 2)) (oNum (m + 1))
        (by
          intro a b hab hE hfl
          have hmEdge := EdgeB_mem m a.1 a.2 b.1 b.2 hE
          have ha : a ∈ vertexOrder m :=
            (mem_vertexOrder_iff m a).mpr hmEdge.1
          have hb : b ∈ vertexOrder m :=
            (mem_vertexOrder_iff m b).mpr hmEdge.2
          have ha' : a ∈ vertexOrder (m + 1) := by
            rw [mem_vertexOrder_succ_iff]
            exact Or.inl ha
          have hb' : b ∈ vertexOrder (m + 1) := by
            rw [mem_vertexOrder_succ_iff]
            exact Or.inl hb
          exact oNum_succ_restrict m ha' hb')
        p q i j


/-- For operator level n, the exceptional edge used by `oTil (n+1)`
lies outside the level-n vertex set. Consequently the actual tilde
orientation and the numbering give the same point-operator entry. -/
theorem pHeO_til_eq_num_of_level_domain
    (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) (ax : ℕ → Axis)
    (p q : Point) (i j : C2) :
    pHeO n θ ax (oTil (n + 1)) p q i j =
      pHeO n θ ax (oNum (n + 1)) p q i j := by
  exact pHeO_orient_congr n θ ax (oTil (n + 1)) (oNum (n + 1))
    (by
      intro a b hab hE hfl
      have hmEdge := EdgeB_mem n a.1 a.2 b.1 b.2 hE
      have ha : a ∈ vertexOrder n :=
        (mem_vertexOrder_iff n a).mpr hmEdge.1
      have hb : b ∈ vertexOrder n :=
        (mem_vertexOrder_iff n b).mpr hmEdge.2
      obtain ⟨h1, h2⟩ := cp1_not_A n hn ha hb
      exact oTil_of_no_corner h1 h2)
    p q i j

/-- Across the O/A corner box, the level-(m+1) entry using the actual
tilde orientation pulls back to the parent-level entry using its tilde
orientation. The orientation conversion is justified by the fact that
`cp1` is outside each operator's own vertex domain. -/
theorem pHeO_corner_O_box_entry_next_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 2) (hpy : p.2 ≤ 2)
    (hqx : q.1 ≤ 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    pHeO (m + 1) θ ax (oTil (m + 2)) p q i j =
      pHeO m θ ax (oTil (m + 1)) p q i j := by
  calc
    pHeO (m + 1) θ ax (oTil (m + 2)) p q i j =
        pHeO (m + 1) θ ax (oNum (m + 2)) p q i j :=
      pHeO_til_eq_num_of_level_domain (m + 1) (by omega)
        θ ax p q i j
    _ = pHeO m θ ax (oNum (m + 1)) p q i j :=
      pHeO_corner_O_box_entry_next_num m hm θ ax
        hp hq hpx hpy hqx hqy i j
    _ = pHeO m θ ax (oTil (m + 1)) p q i j :=
      (pHeO_til_eq_num_of_level_domain m (by omega)
        θ ax p q i j).symm


/-- Across the X/B corner box, the level-(m+1) entry using oNum (m+2)
pulls back to the corresponding parent entry with its actual B-copy
orientation, oBo m (oNum (m+1)). -/
theorem pHeO_corner_X_box_entry_next_num
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : 2 ^ (m + 1) ≤ p.1 + 2) (hpy : p.2 ≤ 2)
    (hqx : 2 ^ (m + 1) ≤ q.1 + 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    ∃ p' q' : Point,
      p' ∈ vertexOrder m ∧ q' ∈ vertexOrder m ∧
      p = shiftPoint (2 ^ m) 1 0 p' ∧
      q = shiftPoint (2 ^ m) 1 0 q' ∧
      pHeO (m + 1) θ ax (oNum (m + 2)) p q i j =
        pHeO m θ ax (oBo m (oNum (m + 1))) p' q' i j := by
  rcases (corner_X_radius_two_box_iff m hm hp).mp ⟨hpx, hpy⟩ with
    ⟨p', hp', hpx', hpy', rfl⟩
  rcases (corner_X_radius_two_box_iff m hm hq).mp ⟨hqx, hqy⟩ with
    ⟨q', hq', hqx', hqy', rfl⟩
  have hpow : 2 < 2 ^ m := by
    calc
      2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hp0 : p' ≠ (0, 0) := by
    intro heq
    have hcoord : p'.1 = 0 := congrArg Prod.fst heq
    omega
  have hpY : p' ≠ (0, 2 ^ m) := by
    intro heq
    have hcoord : p'.1 = 0 := congrArg Prod.fst heq
    omega
  refine ⟨p', q', hp', hq', rfl, rfl, ?_⟩
  calc
    pHeO (m + 1) θ ax (oNum (m + 2))
        (shiftPoint (2 ^ m) 1 0 p') (shiftPoint (2 ^ m) 1 0 q') i j =
      pHeO m θ ax (oBo m (oNum (m + 2))) p' q' i j :=
        pHeO_succ_B_local_entry m θ ax (oNum (m + 2)) hax
          hp' hq' hp0 hpY i j
    _ = pHeO m θ ax (oBo m (oNum (m + 1))) p' q' i j :=
      pHeO_orient_congr m θ ax (oBo m (oNum (m + 2)))
        (oBo m (oNum (m + 1)))
        (by
          intro a b hab hE hfl
          have hmEdge := EdgeB_mem m a.1 a.2 b.1 b.2 hE
          have ha : a ∈ vertexOrder m :=
            (mem_vertexOrder_iff m a).mpr hmEdge.1
          have hb : b ∈ vertexOrder m :=
            (mem_vertexOrder_iff m b).mpr hmEdge.2
          have haB : shiftPoint (2 ^ m) 1 0 a ∈ vertexOrder (m + 1) := by
            rw [mem_vertexOrder_succ_iff]
            exact Or.inr (Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩))
          have hbB : shiftPoint (2 ^ m) 1 0 b ∈ vertexOrder (m + 1) := by
            rw [mem_vertexOrder_succ_iff]
            exact Or.inr (Or.inl (List.mem_map.mpr ⟨b, hb, rfl⟩))
          unfold oBo
          exact oNum_succ_restrict m haB hbB)
        p' q' i j

/-- Across the Y/C corner box, the level-(m+1) entry using oNum (m+2)
pulls back to the corresponding parent entry with its actual C-copy
orientation, oCo m (oNum (m+1)); this deliberately preserves the C flip. -/
theorem pHeO_corner_Y_box_entry_next_num
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 2) (hpy : 2 ^ (m + 1) ≤ p.2 + 2)
    (hqx : q.1 ≤ 2) (hqy : 2 ^ (m + 1) ≤ q.2 + 2)
    (i j : C2) :
    ∃ p' q' : Point,
      p' ∈ vertexOrder m ∧ q' ∈ vertexOrder m ∧
      p = shiftPoint (2 ^ m) 0 1 p' ∧
      q = shiftPoint (2 ^ m) 0 1 q' ∧
      pHeO (m + 1) θ ax (oNum (m + 2)) p q i j =
        pHeO m θ ax (oCo m (oNum (m + 1))) p' q' i j := by
  rcases (corner_Y_radius_two_box_iff m hm hp).mp ⟨hpx, hpy⟩ with
    ⟨p', hp', hpx', hpy', rfl⟩
  rcases (corner_Y_radius_two_box_iff m hm hq).mp ⟨hqx, hqy⟩ with
    ⟨q', hq', hqx', hqy', rfl⟩
  have hpow : 2 < 2 ^ m := by
    calc
      2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hp0 : p' ≠ (0, 0) := by
    intro heq
    have hcoord : p'.2 = 0 := congrArg Prod.snd heq
    omega
  have hpX : p' ≠ (2 ^ m, 0) := by
    intro heq
    have hcoord : p'.2 = 0 := congrArg Prod.snd heq
    omega
  refine ⟨p', q', hp', hq', rfl, rfl, ?_⟩
  calc
    pHeO (m + 1) θ ax (oNum (m + 2))
        (shiftPoint (2 ^ m) 0 1 p') (shiftPoint (2 ^ m) 0 1 q') i j =
      pHeO m θ ax (oCo m (oNum (m + 2))) p' q' i j :=
        pHeO_succ_C_local_entry m θ ax (oNum (m + 2)) hax
          hp' hq' hp0 hpX i j
    _ = pHeO m θ ax (oCo m (oNum (m + 1))) p' q' i j :=
      pHeO_orient_congr m θ ax (oCo m (oNum (m + 2)))
        (oCo m (oNum (m + 1)))
        (by
          intro a b hab hE hfl
          have hmEdge := EdgeB_mem m a.1 a.2 b.1 b.2 hE
          have ha : a ∈ vertexOrder m :=
            (mem_vertexOrder_iff m a).mpr hmEdge.1
          have hb : b ∈ vertexOrder m :=
            (mem_vertexOrder_iff m b).mpr hmEdge.2
          have haC : shiftPoint (2 ^ m) 0 1 a ∈ vertexOrder (m + 1) := by
            rw [mem_vertexOrder_succ_iff]
            exact Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))
          have hbC : shiftPoint (2 ^ m) 0 1 b ∈ vertexOrder (m + 1) := by
            rw [mem_vertexOrder_succ_iff]
            exact Or.inr (Or.inr (List.mem_map.mpr ⟨b, hb, rfl⟩))
          unfold oCo
          exact oNum_succ_restrict m haC hbC)
        p' q' i j




/-- The O/A point-entry transport is also a transport of the actual glued
matrix entries on the A block. The subtype proofs merely repackage the same
coordinates as states at the two adjacent levels. -/
theorem sgK_O_A_entry_next_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 2) (hpy : p.2 ≤ 2)
    (hqx : q.1 ≤ 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.A, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.A, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.A,
          ((⟨p, List.mem_toFinset.mpr
            (corner_O_radius_two_transport m hm hp hpx hpy).1⟩ : Pt m), i))
        (GCopy.A,
          ((⟨q, List.mem_toFinset.mpr
            (corner_O_radius_two_transport m hm hq hqx hqy).1⟩ : Pt m), j)) := by
  change pHeO (m + 1) θ ax (oTil (m + 2)) p q i j =
    pHeO m θ ax (oTil (m + 1)) p q i j
  exact pHeO_corner_O_box_entry_next_til m hm θ ax
    hp hq hpx hpy hqx hqy i j



/-- Pointwise orientation congruence for a single `pHeO` entry. Unlike
`pHeO_orient_congr`, this only needs the orientations to agree on the pair
whose entry is being evaluated. -/
private theorem pHeO_rel_congr_local
    (n : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o o' : Point → Point → Prop) [DecidableRel o] [DecidableRel o']
    (p q : Point) (i j : C2) (h : o p q ↔ o' p q) :
    pHeO n θ ax o p q i j = pHeO n θ ax o' p q i j := by
  classical
  by_cases hpq : p = q
  · subst hpq
    rw [pHeO_diag, pHeO_diag]
  · by_cases hE : EdgeB n p.1 p.2 q.1 q.2 = true
    · rw [pHeO_edge_eq n θ ax o hpq hE,
        pHeO_edge_eq n θ ax o' hpq hE]
      by_cases ho : o p q
      · rw [if_pos ho, if_pos (h.mp ho)]
      · rw [if_neg ho, if_neg (fun h' => ho (h.mpr h'))]
    · rw [pHeO_zero_of_not_edge n θ ax o hpq hE,
        pHeO_zero_of_not_edge n θ ax o' hpq hE]

/-- The exceptional edge `cp1 (n+1)` cannot enter the B-shift of an
O-radius-two box at level n. -/
private theorem cp1_not_B_shift_radius_two
    (n : ℕ) (hn : 3 ≤ n) {p q : Point}
    (hp : p.1 ≤ 2) (hq : q.1 ≤ 2) :
    ¬ cp1 (n + 1) (shiftPoint (2 ^ n) 1 0 p) (shiftPoint (2 ^ n) 1 0 q) ∧
    ¬ cp1 (n + 1) (shiftPoint (2 ^ n) 1 0 q) (shiftPoint (2 ^ n) 1 0 p) := by
  have hpow : 3 < 2 ^ n := by
    calc
      3 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hsep : 2 ^ n + 2 < 2 ^ (n + 1) - 1 := by
    rw [pow_succ]
    omega
  constructor
  · intro h
    have hx : (shiftPoint (2 ^ n) 1 0 p).1 = 2 ^ (n + 1) - 1 :=
      congrArg Prod.fst h.1
    simp only [shiftPoint] at hx
    omega
  · intro h
    have hx : (shiftPoint (2 ^ n) 1 0 q).1 = 2 ^ (n + 1) - 1 :=
      congrArg Prod.fst h.1
    simp only [shiftPoint] at hx
    omega

/-- The exceptional edge cp1 cannot enter the B-shift of an
O-radius-three box at level n. -/
private theorem cp1_not_B_shift_radius_three
    (n : ℕ) (hn : 3 ≤ n) {p q : Point}
    (hp : p.1 ≤ 3) (hq : q.1 ≤ 3) :
    ¬ cp1 (n + 1) (shiftPoint (2 ^ n) 1 0 p) (shiftPoint (2 ^ n) 1 0 q) ∧
    ¬ cp1 (n + 1) (shiftPoint (2 ^ n) 1 0 q) (shiftPoint (2 ^ n) 1 0 p) := by
  have hpow : 4 < 2 ^ n := by
    calc
      4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hsep : 2 ^ n + 3 < 2 ^ (n + 1) - 1 := by
    rw [pow_succ]
    omega
  constructor
  · intro h
    have hx : (shiftPoint (2 ^ n) 1 0 p).1 = 2 ^ (n + 1) - 1 :=
      congrArg Prod.fst h.1
    simp only [shiftPoint] at hx
    omega
  · intro h
    have hx : (shiftPoint (2 ^ n) 1 0 q).1 = 2 ^ (n + 1) - 1 :=
      congrArg Prod.fst h.1
    simp only [shiftPoint] at hx
    omega


/-- On the B-block, the level-(m+1) entry near its O corner transports to
the same B-block entry at level m. This is the B-copy representative used
for the glued X corner; the orientation flip is excluded by the radius-two
bound before reducing both entries to the already established O-box result. -/
theorem sgK_B_O_entry_next_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 2) (hpy : p.2 ≤ 2)
    (hqx : q.1 ≤ 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.B, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.B, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.B,
          ((⟨p, List.mem_toFinset.mpr
            (corner_O_radius_two_transport m hm hp hpx hpy).1⟩ : Pt m), i))
        (GCopy.B,
          ((⟨q, List.mem_toFinset.mpr
            (corner_O_radius_two_transport m hm hq hqx hqy).1⟩ : Pt m), j)) := by
  have hp' : p ∈ vertexOrder m :=
    (corner_O_radius_two_transport m hm hp hpx hpy).1
  have hq' : q ∈ vertexOrder m :=
    (corner_O_radius_two_transport m hm hq hqx hqy).1
  have hhighNoCorner :=
    cp1_not_B_shift_radius_two (m + 1) (by omega) hpx hqx
  have hhighOrient :
      oBo (m + 1) (oTil (m + 2)) p q ↔ oNum (m + 2) p q := by
    calc
      oBo (m + 1) (oTil (m + 2)) p q ↔
          oBo (m + 1) (oNum (m + 2)) p q := by
        unfold oBo
        exact oTil_of_no_corner hhighNoCorner.1 hhighNoCorner.2
      _ ↔ oNum (m + 1) p q := oBo_num_iff_oNum (m + 1) hp hq
      _ ↔ oNum (m + 2) p q := (oNum_succ_restrict m hp hq).symm
  have hlowNoCorner :=
    cp1_not_B_shift_radius_two m hm hpx hqx
  have hlowOrient :
      oBo m (oTil (m + 1)) p q ↔ oNum (m + 1) p q := by
    calc
      oBo m (oTil (m + 1)) p q ↔
          oBo m (oNum (m + 1)) p q := by
        unfold oBo
        exact oTil_of_no_corner hlowNoCorner.1 hlowNoCorner.2
      _ ↔ oNum m p q := oBo_num_iff_oNum m hp' hq'
      _ ↔ oNum (m + 1) p q := by
        unfold oNum
        rw [vIdx_succ_of_mem hp', vIdx_succ_of_mem hq']
  change
    pHeO (m + 1) θ ax (oBo (m + 1) (oTil (m + 2))) p q i j =
      pHeO m θ ax (oBo m (oTil (m + 1))) p q i j
  calc
    pHeO (m + 1) θ ax (oBo (m + 1) (oTil (m + 2))) p q i j =
        pHeO (m + 1) θ ax (oNum (m + 2)) p q i j :=
      pHeO_rel_congr_local (m + 1) θ ax
        (oBo (m + 1) (oTil (m + 2))) (oNum (m + 2))
        p q i j hhighOrient
    _ = pHeO m θ ax (oNum (m + 1)) p q i j :=
      pHeO_corner_O_box_entry_next_num m hm θ ax
        hp hq hpx hpy hqx hqy i j
    _ = pHeO m θ ax (oBo m (oTil (m + 1))) p q i j :=
      (pHeO_rel_congr_local m θ ax
        (oBo m (oTil (m + 1))) (oNum (m + 1))
        p q i j hlowOrient).symm



/-- Spin-resolved B-copy entries in the O-radius-three box transport
to the parent level with the exact tilde orientations. The radius-three
separation excludes the flipped edge before the O/A entry bridge is used. -/
theorem sgK_B_O_entry_next_til_radius_three
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 3) (hpy : p.2 ≤ 3)
    (hqx : q.1 ≤ 3) (hqy : q.2 ≤ 3)
    (i j : C2) :
    sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.B, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.B, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.B,
          ((⟨p, List.mem_toFinset.mpr
            (corner_O_radius_three_transport m hm hp hpx hpy).1⟩ : Pt m), i))
        (GCopy.B,
          ((⟨q, List.mem_toFinset.mpr
            (corner_O_radius_three_transport m hm hq hqx hqy).1⟩ : Pt m), j)) := by
  have hp' : p ∈ vertexOrder m :=
    (corner_O_radius_three_transport m hm hp hpx hpy).1
  have hq' : q ∈ vertexOrder m :=
    (corner_O_radius_three_transport m hm hq hqx hqy).1
  have hhighNoCorner :=
    cp1_not_B_shift_radius_three (m + 1) (by omega) hpx hqx
  have hhighOrient :
      oBo (m + 1) (oTil (m + 2)) p q ↔ oNum (m + 2) p q := by
    calc
      oBo (m + 1) (oTil (m + 2)) p q ↔
          oBo (m + 1) (oNum (m + 2)) p q := by
        unfold oBo
        exact oTil_of_no_corner hhighNoCorner.1 hhighNoCorner.2
      _ ↔ oNum (m + 1) p q := oBo_num_iff_oNum (m + 1) hp hq
      _ ↔ oNum (m + 2) p q := (oNum_succ_restrict m hp hq).symm
  have hlowNoCorner :=
    cp1_not_B_shift_radius_three m (by omega) hpx hqx
  have hlowOrient :
      oBo m (oTil (m + 1)) p q ↔ oNum (m + 1) p q := by
    calc
      oBo m (oTil (m + 1)) p q ↔
          oBo m (oNum (m + 1)) p q := by
        unfold oBo
        exact oTil_of_no_corner hlowNoCorner.1 hlowNoCorner.2
      _ ↔ oNum m p q := oBo_num_iff_oNum m hp' hq'
      _ ↔ oNum (m + 1) p q := by
        unfold oNum
        rw [vIdx_succ_of_mem hp', vIdx_succ_of_mem hq']
  change
    pHeO (m + 1) θ ax (oBo (m + 1) (oTil (m + 2))) p q i j =
      pHeO m θ ax (oBo m (oTil (m + 1))) p q i j
  calc
    pHeO (m + 1) θ ax (oBo (m + 1) (oTil (m + 2))) p q i j =
        pHeO (m + 1) θ ax (oNum (m + 2)) p q i j :=
      pHeO_rel_congr_local (m + 1) θ ax
        (oBo (m + 1) (oTil (m + 2))) (oNum (m + 2))
        p q i j hhighOrient
    _ = pHeO m θ ax (oNum (m + 1)) p q i j :=
      pHeO_corner_O_radius_three_entry_next_num m hm θ ax
        hp hq hpx hpy hqx hqy i j
    _ = pHeO m θ ax (oBo m (oTil (m + 1))) p q i j :=
      (pHeO_rel_congr_local m θ ax
        (oBo m (oTil (m + 1))) (oNum (m + 1))
        p q i j hlowOrient).symm


/-- On a level-n O radius-two box, the exceptional edge at either of the
next two orientation levels is absent. -/
private theorem cp1_not_O_radius_two
    (n : ℕ) (hn : 3 ≤ n) {p q : Point}
    (hp : p.1 ≤ 2) (hq : q.1 ≤ 2) :
    ¬ cp1 n p q ∧ ¬ cp1 n q p := by
  have hpow : 4 ≤ 2 ^ n := by
    calc
      4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcorner : 2 < 2 ^ n - 1 := by omega
  constructor
  · intro h
    have hx : p.1 = 2 ^ n - 1 := congrArg Prod.fst h.1
    omega
  · intro h
    have hx : q.1 = 2 ^ n - 1 := congrArg Prod.fst h.1
    omega

/-- The exceptional edge cp1 at level n cannot meet either endpoint
of an O-radius-three box. -/
private theorem cp1_not_O_radius_three
    (n : ℕ) (hn : 3 ≤ n) {p q : Point}
    (hp : p.1 ≤ 3) (hq : q.1 ≤ 3) :
    ¬ cp1 n p q ∧ ¬ cp1 n q p := by
  have hpow : 4 < 2 ^ n := by
    calc
      4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcorner : 3 < 2 ^ n - 1 := by omega
  constructor
  · intro h
    have hx : p.1 = 2 ^ n - 1 := congrArg Prod.fst h.1
    omega
  · intro h
    have hx : q.1 = 2 ^ n - 1 := congrArg Prod.fst h.1
    omega


/-- The Y/C point-entry transport with the exact tilde orientations used by
the adjacent-level residual. The parent endpoints lie in the Y box, away
from the exceptional horizontal edge, so the C-flip's `oTil m` result
can be shifted to `oTil (m+1)` on this restricted box. -/
theorem pHeO_corner_Y_box_entry_next_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 2) (hpy : 2 ^ (m + 1) ≤ p.2 + 2)
    (hqx : q.1 ≤ 2) (hqy : 2 ^ (m + 1) ≤ q.2 + 2)
    (i j : C2) :
    ∃ p' q' : Point,
      p' ∈ vertexOrder m ∧ q' ∈ vertexOrder m ∧
      p = shiftPoint (2 ^ m) 0 1 p' ∧
      q = shiftPoint (2 ^ m) 0 1 q' ∧
      pHeO (m + 1) θ ax (oTil (m + 2)) p q i j =
        pHeO m θ ax (oTil (m + 1)) p' q' i j := by
  rcases pHeO_corner_Y_box_entry_next_num m hm θ ax hax
      hp hq hpx hpy hqx hqy i j with
    ⟨p', q', hp', hq', rfl, rfl, hentry⟩
  have hpx' : p'.1 ≤ 2 := by
    simpa [shiftPoint] using hpx
  have hqx' : q'.1 ≤ 2 := by
    simpa [shiftPoint] using hqx
  have hpy' : 2 ^ m ≤ p'.2 + 2 := by
    have hh : 2 ^ (m + 1) ≤ p'.2 + 2 ^ m + 2 := by
      simpa [shiftPoint] using hpy
    rw [pow_succ] at hh
    omega
  have hqy' : 2 ^ m ≤ q'.2 + 2 := by
    have hh : 2 ^ (m + 1) ≤ q'.2 + 2 ^ m + 2 := by
      simpa [shiftPoint] using hqy
    rw [pow_succ] at hh
    omega
  have hCnum := Hc_C_num_eq_parent_til m (by omega) θ ax
    (oNum_anti (m + 1))
    ((⟨p', List.mem_toFinset.mpr hp'⟩ : Pt m), i)
    ((⟨q', List.mem_toFinset.mpr hq'⟩ : Pt m), j)
  change pHeO m θ ax (oCo m (oNum (m + 1))) p' q' i j =
    pHeO m θ ax (oTil m) p' q' i j at hCnum
  have hcpM := cp1_not_O_radius_two m hm hpx' hqx'
  have hcpM1 := cp1_not_A m (by omega) hp' hq'
  have hnum : oNum m p' q' ↔ oNum (m + 1) p' q' := by
    unfold oNum
    rw [vIdx_succ_of_mem hp', vIdx_succ_of_mem hq']
  have htil : oTil m p' q' ↔ oTil (m + 1) p' q' := by
    calc
      oTil m p' q' ↔ oNum m p' q' :=
        oTil_of_no_corner hcpM.1 hcpM.2
      _ ↔ oNum (m + 1) p' q' := hnum
      _ ↔ oTil (m + 1) p' q' :=
        (oTil_of_no_corner hcpM1.1 hcpM1.2).symm
  refine ⟨p', q', hp', hq', rfl, rfl, ?_⟩
  calc
    pHeO (m + 1) θ ax (oTil (m + 2))
        (shiftPoint (2 ^ m) 0 1 p') (shiftPoint (2 ^ m) 0 1 q') i j =
        pHeO (m + 1) θ ax (oNum (m + 2))
          (shiftPoint (2 ^ m) 0 1 p') (shiftPoint (2 ^ m) 0 1 q') i j :=
      pHeO_til_eq_num_of_level_domain (m + 1) (by omega)
        θ ax (shiftPoint (2 ^ m) 0 1 p') (shiftPoint (2 ^ m) 0 1 q') i j
    _ = pHeO m θ ax (oCo m (oNum (m + 1))) p' q' i j := hentry
    _ = pHeO m θ ax (oTil m) p' q' i j := hCnum
    _ = pHeO m θ ax (oTil (m + 1)) p' q' i j :=
      pHeO_rel_congr_local m θ ax (oTil m) (oTil (m + 1))
        p' q' i j htil

/-- State-index version of the Y/A point-entry transport. It reuses the
exact copy label, coordinate witness and spin without changing the kernel. -/
theorem sgK_A_Y_entry_next_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 2) (hpy : 2 ^ (m + 1) ≤ p.2 + 2)
    (hqx : q.1 ≤ 2) (hqy : 2 ^ (m + 1) ≤ q.2 + 2)
    (i j : C2) :
    ∃ p' q' : Pt m,
      p = shiftPoint (2 ^ m) 0 1 p'.1 ∧
      q = shiftPoint (2 ^ m) 0 1 q'.1 ∧
      sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.A, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.A, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.A, (p', i))
        (GCopy.A, (q', j)) := by
  rcases pHeO_corner_Y_box_entry_next_til m hm θ ax hax
      hp hq hpx hpy hqx hqy i j with
    ⟨p0, q0, hp0, hq0, rfl, rfl, hentry⟩
  refine ⟨(⟨p0, List.mem_toFinset.mpr hp0⟩ : Pt m),
      (⟨q0, List.mem_toFinset.mpr hq0⟩ : Pt m), rfl, rfl, ?_⟩
  change pHeO (m + 1) θ ax (oTil (m + 2))
      (shiftPoint (2 ^ m) 0 1 p0) (shiftPoint (2 ^ m) 0 1 q0) i j =
    pHeO m θ ax (oTil (m + 1)) p0 q0 i j
  exact hentry





/-- The B-block transport at its Y corner. The local Y/C refinement is
already proved pointwise; the extra B pullback is removed only on this local
box, using the exceptional-edge exclusion and the existing B-order lemma. -/
theorem sgK_B_Y_entry_next_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 2) (hpy : 2 ^ (m + 1) ≤ p.2 + 2)
    (hqx : q.1 ≤ 2) (hqy : 2 ^ (m + 1) ≤ q.2 + 2)
    (i j : C2) :
    ∃ p' q' : Pt m,
      p = shiftPoint (2 ^ m) 0 1 p'.1 ∧
      q = shiftPoint (2 ^ m) 0 1 q'.1 ∧
      sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.B, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.B, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.B, (p', i))
        (GCopy.B, (q', j)) := by
  rcases pHeO_corner_Y_box_entry_next_til m hm θ ax hax
      hp hq hpx hpy hqx hqy i j with
    ⟨p0, q0, hp0, hq0, hpEq, hqEq, hentry⟩
  have hpCoord : p.1 = p0.1 := by
    simpa [shiftPoint] using congrArg Prod.fst hpEq
  have hqCoord : q.1 = q0.1 := by
    simpa [shiftPoint] using congrArg Prod.fst hqEq
  have hpx' : p0.1 ≤ 2 := by rw [← hpCoord]; exact hpx
  have hqx' : q0.1 ≤ 2 := by rw [← hqCoord]; exact hqx
  have hHighBShift :=
    cp1_not_B_shift_radius_two (m + 1) (by omega) hpx hqx
  have hHighLocal := cp1_not_O_radius_two (m + 2) (by omega) hpx hqx
  have hHighOrient :
      oBo (m + 1) (oTil (m + 2)) p q ↔ oTil (m + 2) p q := by
    calc
      oBo (m + 1) (oTil (m + 2)) p q ↔
          oBo (m + 1) (oNum (m + 2)) p q := by
        unfold oBo
        exact oTil_of_no_corner hHighBShift.1 hHighBShift.2
      _ ↔ oNum (m + 1) p q := oBo_num_iff_oNum (m + 1) hp hq
      _ ↔ oNum (m + 2) p q := (oNum_succ_restrict m hp hq).symm
      _ ↔ oTil (m + 2) p q :=
        (oTil_of_no_corner hHighLocal.1 hHighLocal.2).symm
  have hLowBShift := cp1_not_B_shift_radius_two m hm hpx' hqx'
  have hLowBNum :
      oBo m (oTil (m + 1)) p0 q0 ↔ oNum m p0 q0 := by
    calc
      oBo m (oTil (m + 1)) p0 q0 ↔
          oBo m (oNum (m + 1)) p0 q0 := by
        unfold oBo
        exact oTil_of_no_corner hLowBShift.1 hLowBShift.2
      _ ↔ oNum m p0 q0 := oBo_num_iff_oNum m hp0 hq0
  obtain ⟨h1, h2⟩ := cp1_not_A m (by omega) hp0 hq0
  have hnum : oNum (m + 1) p0 q0 ↔ oNum m p0 q0 := by
    unfold oNum
    rw [vIdx_succ_of_mem hp0, vIdx_succ_of_mem hq0]
  have hLowTilNum : oTil (m + 1) p0 q0 ↔ oNum m p0 q0 := by
    calc
      oTil (m + 1) p0 q0 ↔ oNum (m + 1) p0 q0 :=
        oTil_of_no_corner h1 h2
      _ ↔ oNum m p0 q0 := hnum
  have hLowOrient :
      oBo m (oTil (m + 1)) p0 q0 ↔ oTil (m + 1) p0 q0 :=
    hLowBNum.trans hLowTilNum.symm
  refine ⟨(⟨p0, List.mem_toFinset.mpr hp0⟩ : Pt m),
      (⟨q0, List.mem_toFinset.mpr hq0⟩ : Pt m), hpEq, hqEq, ?_⟩
  change pHeO (m + 1) θ ax (oBo (m + 1) (oTil (m + 2))) p q i j =
    pHeO m θ ax (oBo m (oTil (m + 1))) p0 q0 i j
  calc
    pHeO (m + 1) θ ax (oBo (m + 1) (oTil (m + 2))) p q i j =
        pHeO (m + 1) θ ax (oTil (m + 2)) p q i j :=
      pHeO_rel_congr_local (m + 1) θ ax
        (oBo (m + 1) (oTil (m + 2))) (oTil (m + 2))
        p q i j hHighOrient
    _ = pHeO m θ ax (oTil (m + 1)) p0 q0 i j := hentry
    _ = pHeO m θ ax (oBo m (oTil (m + 1))) p0 q0 i j :=
      (pHeO_rel_congr_local m θ ax
        (oBo m (oTil (m + 1))) (oTil (m + 1))
        p0 q0 i j hLowOrient).symm


/-- The C-block at the O corner also transports across one refinement level.
The C shift turns its orientation into the established C-copy orientation
transfer; the small O box then lets the ordinary O-entry transport apply. -/
theorem sgK_C_O_entry_next_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 2) (hpy : p.2 ≤ 2)
    (hqx : q.1 ≤ 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.C, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.C, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.C,
          ((⟨p, List.mem_toFinset.mpr
            (corner_O_radius_two_transport m hm hp hpx hpy).1⟩ : Pt m), i))
        (GCopy.C,
          ((⟨q, List.mem_toFinset.mpr
            (corner_O_radius_two_transport m hm hq hqx hqy).1⟩ : Pt m), j)) := by
  have hp' : p ∈ vertexOrder m :=
    (corner_O_radius_two_transport m hm hp hpx hpy).1
  have hq' : q ∈ vertexOrder m :=
    (corner_O_radius_two_transport m hm hq hqx hqy).1
  have hHighOrient : ∀ a b : Point,
      oCo (m + 1) (oTil (m + 2)) a b ↔
        oCo (m + 1) (oNum (m + 2)) a b := by
    intro a b
    obtain ⟨h1, h2⟩ := cp1_shiftC (m + 1) (p := a) (q := b)
    change oTil (m + 2) (shiftPoint (2 ^ (m + 1)) 0 1 a)
        (shiftPoint (2 ^ (m + 1)) 0 1 b) ↔
      oNum (m + 2) (shiftPoint (2 ^ (m + 1)) 0 1 a)
        (shiftPoint (2 ^ (m + 1)) 0 1 b)
    exact oTil_of_no_corner h1 h2
  have hLowOrient : ∀ a b : Point,
      oCo m (oTil (m + 1)) a b ↔
        oCo m (oNum (m + 1)) a b := by
    intro a b
    obtain ⟨h1, h2⟩ := cp1_shiftC m (p := a) (q := b)
    change oTil (m + 1) (shiftPoint (2 ^ m) 0 1 a)
        (shiftPoint (2 ^ m) 0 1 b) ↔
      oNum (m + 1) (shiftPoint (2 ^ m) 0 1 a)
        (shiftPoint (2 ^ m) 0 1 b)
    exact oTil_of_no_corner h1 h2
  have hHighC :
      pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j =
        pHeO (m + 1) θ ax (oTil (m + 1)) p q i j := by
    have h := Hc_C_num_eq_parent_til (m + 1) (by omega) θ ax
      (oNum_anti (m + 2))
      ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i)
      ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)
    change pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j =
      pHeO (m + 1) θ ax (oTil (m + 1)) p q i j at h
    exact h
  have hLowC :
      pHeO m θ ax (oCo m (oNum (m + 1))) p q i j =
        pHeO m θ ax (oTil m) p q i j := by
    have h := Hc_C_num_eq_parent_til m (by omega) θ ax
      (oNum_anti (m + 1))
      ((⟨p, List.mem_toFinset.mpr hp'⟩ : Pt m), i)
      ((⟨q, List.mem_toFinset.mpr hq'⟩ : Pt m), j)
    change pHeO m θ ax (oCo m (oNum (m + 1))) p q i j =
      pHeO m θ ax (oTil m) p q i j at h
    exact h
  change pHeO (m + 1) θ ax (oCo (m + 1) (oTil (m + 2))) p q i j =
    pHeO m θ ax (oCo m (oTil (m + 1))) p q i j
  calc
    pHeO (m + 1) θ ax (oCo (m + 1) (oTil (m + 2))) p q i j =
        pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j :=
      pHeO_rel_congr_local (m + 1) θ ax
        (oCo (m + 1) (oTil (m + 2))) (oCo (m + 1) (oNum (m + 2)))
        p q i j (hHighOrient p q)
    _ = pHeO (m + 1) θ ax (oTil (m + 1)) p q i j := hHighC
    _ = pHeO (m + 1) θ ax (oNum (m + 1)) p q i j :=
      pHeO_rel_congr_local (m + 1) θ ax (oTil (m + 1)) (oNum (m + 1))
        p q i j (oTil_of_no_corner
          (cp1_not_O_radius_two (m + 1) (by omega) hpx hqx).1
          (cp1_not_O_radius_two (m + 1) (by omega) hpx hqx).2)
    _ = pHeO m θ ax (oNum m) p q i j :=
      pHeO_corner_O_box_entry m hm θ ax hp hq hpx hpy hqx hqy i j
    _ = pHeO m θ ax (oTil m) p q i j :=
      (pHeO_rel_congr_local m θ ax (oTil m) (oNum m)
        p q i j (oTil_of_no_corner
          (cp1_not_O_radius_two m hm hpx hqx).1
          (cp1_not_O_radius_two m hm hpx hqx).2)).symm
    _ = pHeO m θ ax (oCo m (oNum (m + 1))) p q i j := hLowC.symm
    _ = pHeO m θ ax (oCo m (oTil (m + 1))) p q i j :=
      (pHeO_rel_congr_local m θ ax
        (oCo m (oTil (m + 1))) (oCo m (oNum (m + 1)))
        p q i j (hLowOrient p q)).symm



/-- Spin-resolved C-copy entries in the O-radius-three box transport
to the parent level with the exact tilde orientations. The C-copy
orientation conversion and the radius-three O/A entry bridge are kept
as separate steps. -/
theorem sgK_C_O_entry_next_til_radius_three
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 3) (hpy : p.2 ≤ 3)
    (hqx : q.1 ≤ 3) (hqy : q.2 ≤ 3)
    (i j : C2) :
    sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.C, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.C, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.C,
          ((⟨p, List.mem_toFinset.mpr
            (corner_O_radius_three_transport m hm hp hpx hpy).1⟩ : Pt m), i))
        (GCopy.C,
          ((⟨q, List.mem_toFinset.mpr
            (corner_O_radius_three_transport m hm hq hqx hqy).1⟩ : Pt m), j)) := by
  have hp' : p ∈ vertexOrder m :=
    (corner_O_radius_three_transport m hm hp hpx hpy).1
  have hq' : q ∈ vertexOrder m :=
    (corner_O_radius_three_transport m hm hq hqx hqy).1
  have hHighOrient : ∀ a b : Point,
      oCo (m + 1) (oTil (m + 2)) a b ↔
        oCo (m + 1) (oNum (m + 2)) a b := by
    intro a b
    obtain ⟨h1, h2⟩ := cp1_shiftC (m + 1) (p := a) (q := b)
    change oTil (m + 2) (shiftPoint (2 ^ (m + 1)) 0 1 a)
        (shiftPoint (2 ^ (m + 1)) 0 1 b) ↔
      oNum (m + 2) (shiftPoint (2 ^ (m + 1)) 0 1 a)
        (shiftPoint (2 ^ (m + 1)) 0 1 b)
    exact oTil_of_no_corner h1 h2
  have hLowOrient : ∀ a b : Point,
      oCo m (oTil (m + 1)) a b ↔
        oCo m (oNum (m + 1)) a b := by
    intro a b
    obtain ⟨h1, h2⟩ := cp1_shiftC m (p := a) (q := b)
    change oTil (m + 1) (shiftPoint (2 ^ m) 0 1 a)
        (shiftPoint (2 ^ m) 0 1 b) ↔
      oNum (m + 1) (shiftPoint (2 ^ m) 0 1 a)
        (shiftPoint (2 ^ m) 0 1 b)
    exact oTil_of_no_corner h1 h2
  have hHighC :
      pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j =
        pHeO (m + 1) θ ax (oTil (m + 1)) p q i j := by
    have h := Hc_C_num_eq_parent_til (m + 1) (by omega) θ ax
      (oNum_anti (m + 2))
      ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i)
      ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)
    change pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j =
      pHeO (m + 1) θ ax (oTil (m + 1)) p q i j at h
    exact h
  have hLowC :
      pHeO m θ ax (oCo m (oNum (m + 1))) p q i j =
        pHeO m θ ax (oTil m) p q i j := by
    have h := Hc_C_num_eq_parent_til m (by omega) θ ax
      (oNum_anti (m + 1))
      ((⟨p, List.mem_toFinset.mpr hp'⟩ : Pt m), i)
      ((⟨q, List.mem_toFinset.mpr hq'⟩ : Pt m), j)
    change pHeO m θ ax (oCo m (oNum (m + 1))) p q i j =
      pHeO m θ ax (oTil m) p q i j at h
    exact h
  change pHeO (m + 1) θ ax (oCo (m + 1) (oTil (m + 2))) p q i j =
    pHeO m θ ax (oCo m (oTil (m + 1))) p q i j
  calc
    pHeO (m + 1) θ ax (oCo (m + 1) (oTil (m + 2))) p q i j =
        pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j :=
      pHeO_rel_congr_local (m + 1) θ ax
        (oCo (m + 1) (oTil (m + 2))) (oCo (m + 1) (oNum (m + 2)))
        p q i j (hHighOrient p q)
    _ = pHeO (m + 1) θ ax (oTil (m + 1)) p q i j := hHighC
    _ = pHeO (m + 1) θ ax (oNum (m + 1)) p q i j :=
      pHeO_rel_congr_local (m + 1) θ ax (oTil (m + 1)) (oNum (m + 1))
        p q i j (oTil_of_no_corner
          (cp1_not_O_radius_three (m + 1) (by omega) hpx hqx).1
          (cp1_not_O_radius_three (m + 1) (by omega) hpx hqx).2)
    _ = pHeO m θ ax (oNum m) p q i j :=
      pHeO_corner_O_radius_three_entry m hm θ ax hp hq hpx hpy hqx hqy i j
    _ = pHeO m θ ax (oTil m) p q i j :=
      (pHeO_rel_congr_local m θ ax (oTil m) (oNum m)
        p q i j (oTil_of_no_corner
          (cp1_not_O_radius_three m (by omega) hpx hqx).1
          (cp1_not_O_radius_three m (by omega) hpx hqx).2)).symm
    _ = pHeO m θ ax (oCo m (oNum (m + 1))) p q i j := hLowC.symm
    _ = pHeO m θ ax (oCo m (oTil (m + 1))) p q i j :=
      (pHeO_rel_congr_local m θ ax
        (oCo m (oTil (m + 1))) (oCo m (oNum (m + 1)))
        p q i j (hLowOrient p q)).symm


/-- The level-(m+1) radius-two support at O is exactly the old A-copy
part of the same coordinate box. The copy coordinate is still explicit;
spin states are retained unchanged by the state index. -/
theorem sgK_radius_two_support_O_box_iff
    (m : ℕ) (hm : 3 ≤ m) {w z : WSG (m + 1)}
    (hw : w.2.1.1 = ((0, 0) : Point)) :
    z ∈ sgK_radius_two_support (m + 1) w ↔
      z.1 = w.1 ∧
        z.2.1.1 ∈ vertexOrder m ∧
        z.2.1.1.1 ≤ 2 ∧ z.2.1.1.2 ≤ 2 := by
  simp only [sgK_radius_two_support, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcopy, _, hx, _, hy⟩
    have hzX : z.2.1.1.1 ≤ 2 := by simpa [hw] using hx
    have hzY : z.2.1.1.2 ≤ 2 := by simpa [hw] using hy
    have hmem := (corner_O_radius_two_transport m hm
      (z := z.2.1.1) (List.mem_toFinset.mp z.2.1.2) hzX hzY).1
    exact ⟨hcopy, hmem, hzX, hzY⟩
  · rintro ⟨hcopy, _, hx, hy⟩
    exact ⟨hcopy, by simp [hw], by simpa [hw] using hx,
      by simp [hw], by simpa [hw] using hy⟩



/-- The parent-level O-corner states with the same outer copy and coordinate
box [0,2]². Spin is deliberately unrestricted, just as in the glued radius-two
support. -/
def sgK_radius_two_O_parent_support (m : ℕ) (c : GCopy) : Finset (WSG m) :=
  Finset.univ.filter fun z =>
    z.1 = c ∧ z.2.1.1.1 ≤ 2 ∧ z.2.1.1.2 ≤ 2

/-- Pulling the radius-two support at an O corner back one level is a genuine
bijection of finite state sets. It preserves the outer copy, coordinate, and
spin; this is a geometric reindexing lemma and makes no claim about matrix
weights yet. -/
noncomputable def sgK_radius_two_support_O_equiv
    (m : ℕ) (hm : 3 ≤ m) {w : WSG (m + 1)}
    (hw : w.2.1.1 = ((0, 0) : Point)) :
    {z : WSG (m + 1) // z ∈ sgK_radius_two_support (m + 1) w} ≃
      {z : WSG m // z ∈ sgK_radius_two_O_parent_support m w.1} := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    have hz := (sgK_radius_two_support_O_box_iff m hm hw).mp z.2
    refine ⟨(z.1.1, (⟨z.1.2.1.1, List.mem_toFinset.mpr hz.2.1⟩, z.1.2.2)), ?_⟩
    change _ ∈ sgK_radius_two_O_parent_support m w.1
    simp only [sgK_radius_two_O_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨hz.1, hz.2.2.1, hz.2.2.2⟩
  · intro z
    have hp : z.1.2.1.1 ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inl (List.mem_toFinset.mp z.1.2.1.2)
    refine ⟨(z.1.1, (⟨z.1.2.1.1, List.mem_toFinset.mpr hp⟩, z.1.2.2)), ?_⟩
    apply (sgK_radius_two_support_O_box_iff m hm hw).mpr
    have hparent : z.1 ∈ sgK_radius_two_O_parent_support m w.1 := z.2
    simp only [sgK_radius_two_O_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hparent
    exact ⟨hparent.1, List.mem_toFinset.mp z.1.2.1.2,
      hparent.2.1, hparent.2.2⟩
  · intro z
    apply Subtype.ext
    rfl
  · intro z
    apply Subtype.ext
    rfl

/-- The level-(m+1) radius-three support around O is exactly the old
A-copy coordinate box. The copy coordinate and spin are retained. -/
theorem sgK_radius_three_support_O_box_iff
    (m : ℕ) (hm : 4 ≤ m) {w z : WSG (m + 1)}
    (hw : w.2.1.1 = ((0, 0) : Point)) :
    z ∈ sgK_radius_three_support (m + 1) w ↔
      z.1 = w.1 ∧
        z.2.1.1 ∈ vertexOrder m ∧
        z.2.1.1.1 ≤ 3 ∧ z.2.1.1.2 ≤ 3 := by
  simp only [sgK_radius_three_support, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcopy, _, hx, _, hy⟩
    have hzX : z.2.1.1.1 ≤ 3 := by simpa [hw] using hx
    have hzY : z.2.1.1.2 ≤ 3 := by simpa [hw] using hy
    have hmem := corner_O_radius_three_transport m hm
      (z := z.2.1.1) (List.mem_toFinset.mp z.2.1.2) hzX hzY
    exact ⟨hcopy, hmem.1, hzX, hzY⟩
  · rintro ⟨hcopy, _, hx, hy⟩
    exact ⟨hcopy, by simp [hw], by simpa [hw] using hx,
      by simp [hw], by simpa [hw] using hy⟩

/-- Parent-level finite state support for the radius-three box around O.
It keeps the block index fixed and leaves spin unrestricted. -/
def sgK_radius_three_O_parent_support (m : ℕ) (c : GCopy) :
    Finset (WSG m) :=
  Finset.univ.filter fun z =>
    z.1 = c ∧ z.2.1.1.1 ≤ 3 ∧ z.2.1.1.2 ≤ 3

/-- The level-(m+1) radius-three support at O is bijective to the
parent-level support by retaining the same point, copy, and spin. This is
a finite-state reindexing statement; it does not yet compare matrix entries. -/
noncomputable def sgK_radius_three_support_O_equiv
    (m : ℕ) (hm : 4 ≤ m) {w : WSG (m + 1)}
    (hw : w.2.1.1 = ((0, 0) : Point)) :
    {z : WSG (m + 1) // z ∈ sgK_radius_three_support (m + 1) w} ≃
      {z : WSG m // z ∈ sgK_radius_three_O_parent_support m w.1} := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    have hz := (sgK_radius_three_support_O_box_iff m hm hw).mp z.2
    refine ⟨(z.1.1, (⟨z.1.2.1.1, List.mem_toFinset.mpr hz.2.1⟩,
      z.1.2.2)), ?_⟩
    change _ ∈ sgK_radius_three_O_parent_support m w.1
    simp only [sgK_radius_three_O_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨hz.1, hz.2.2.1, hz.2.2.2⟩
  · intro z
    have hp : z.1.2.1.1 ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inl (List.mem_toFinset.mp z.1.2.1.2)
    refine ⟨(z.1.1, (⟨z.1.2.1.1, List.mem_toFinset.mpr hp⟩,
      z.1.2.2)), ?_⟩
    apply (sgK_radius_three_support_O_box_iff m hm hw).mpr
    have hparent : z.1 ∈ sgK_radius_three_O_parent_support m w.1 :=
      z.2
    simp only [sgK_radius_three_O_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hparent
    exact ⟨hparent.1, List.mem_toFinset.mp z.1.2.1.2,
      hparent.2.1, hparent.2.2⟩
  · intro z
    apply Subtype.ext
    rfl
  · intro z
    apply Subtype.ext
    rfl

/-- The level-(m+1) radius-three support at X is the image of the
parent-level box under the B-copy shift. The copy coordinate is fixed,
and the spin coordinate is retained. -/
theorem sgK_radius_three_support_X_box_iff
    (m : ℕ) (hm : 4 ≤ m) {w z : WSG (m + 1)}
    (hw : w.2.1.1 = ((2 ^ (m + 1), 0) : Point)) :
    z ∈ sgK_radius_three_support (m + 1) w ↔
      z.1 = w.1 ∧
        ∃ p : Point, p ∈ vertexOrder m ∧
          2 ^ m ≤ p.1 + 3 ∧ p.2 ≤ 3 ∧
          z.2.1.1 = shiftPoint (2 ^ m) 1 0 p := by
  simp only [sgK_radius_three_support, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcopy, hx, _, _, hy⟩
    have hboxX : 2 ^ (m + 1) ≤ z.2.1.1.1 + 3 := by
      simpa [hw] using hx
    have hboxY : z.2.1.1.2 ≤ 3 := by
      simpa [hw] using hy
    rcases (corner_X_radius_three_box_iff m hm
      (List.mem_toFinset.mp z.2.1.2)).mp ⟨hboxX, hboxY⟩
      with ⟨p, hp, hpx, hpy, hz⟩
    exact ⟨hcopy, ⟨p, hp, hpx, hpy, hz⟩⟩
  · rintro ⟨hcopy, ⟨p, hp, hpx, hpy, hz⟩⟩
    have hbox := (corner_X_radius_three_box_iff m hm
      (List.mem_toFinset.mp z.2.1.2)).mpr
      ⟨p, hp, hpx, hpy, hz⟩
    have hsum := vertexOrder_sum_le (m + 1) z.2.1.1
      (List.mem_toFinset.mp z.2.1.2)
    refine ⟨hcopy, ?_, ?_, ?_, ?_⟩
    · simpa [hw] using hbox.1
    · simp [hw]
      omega
    · simp [hw]
    · simpa [hw] using hbox.2

/-- Parent-level finite-state support for the radius-three box around X.
It fixes the copy label and leaves spin unrestricted. -/
def sgK_radius_three_X_parent_support (m : ℕ) (c : GCopy) :
    Finset (WSG m) :=
  Finset.univ.filter fun z =>
    z.1 = c ∧ 2 ^ m ≤ z.2.1.1.1 + 3 ∧ z.2.1.1.2 ≤ 3

/-- The X radius-three support is bijective to its parent-level box by
the inverse B shift. This is only a finite-state reindexing statement;
it does not yet compare matrix entries. -/
noncomputable def sgK_radius_three_support_X_equiv
    (m : ℕ) (hm : 4 ≤ m) {w : WSG (m + 1)}
    (hw : w.2.1.1 = ((2 ^ (m + 1), 0) : Point)) :
    {z : WSG (m + 1) // z ∈ sgK_radius_three_support (m + 1) w} ≃
      {z : WSG m // z ∈ sgK_radius_three_X_parent_support m w.1} := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    let p : Point := (z.1.2.1.1.1 - 2 ^ m, z.1.2.1.1.2)
    have hz := (sgK_radius_three_support_X_box_iff m hm hw).mp z.2
    have hp : p ∈ vertexOrder m := by
      rcases hz.2 with ⟨q, hq, _, _, hpoint⟩
      have hcoordx : z.1.2.1.1.1 = q.1 + 2 ^ m := by
        have h := congrArg Prod.fst hpoint
        simpa [shiftPoint] using h
      have hcoordy : z.1.2.1.1.2 = q.2 := by
        have h := congrArg Prod.snd hpoint
        simpa [shiftPoint] using h
      have hpEq : p = q := by
        dsimp [p]
        exact Prod.ext (by omega) hcoordy
      rw [hpEq]
      exact hq
    have hbounds : 2 ^ m ≤ p.1 + 3 ∧ p.2 ≤ 3 := by
      rcases hz.2 with ⟨q, _, hqx, hqy, hpoint⟩
      have hcoordx : z.1.2.1.1.1 = q.1 + 2 ^ m := by
        have h := congrArg Prod.fst hpoint
        simpa [shiftPoint] using h
      have hcoordy : z.1.2.1.1.2 = q.2 := by
        have h := congrArg Prod.snd hpoint
        simpa [shiftPoint] using h
      constructor
      · dsimp [p]
        omega
      · dsimp [p]
        rw [hcoordy]
        exact hqy
    refine ⟨(z.1.1, (⟨p, List.mem_toFinset.mpr hp⟩, z.1.2.2)), ?_⟩
    simp only [sgK_radius_three_X_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨hz.1, hbounds.1, hbounds.2⟩
  · intro z
    have hp : shiftPoint (2 ^ m) 1 0 z.1.2.1.1 ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inr (Or.inl (List.mem_map.mpr
        ⟨z.1.2.1.1, List.mem_toFinset.mp z.1.2.1.2, rfl⟩))
    refine ⟨(z.1.1,
      (⟨shiftPoint (2 ^ m) 1 0 z.1.2.1.1, List.mem_toFinset.mpr hp⟩,
        z.1.2.2)), ?_⟩
    apply (sgK_radius_three_support_X_box_iff m hm hw).mpr
    have hparent : z.1 ∈ sgK_radius_three_X_parent_support m w.1 := z.2
    simp only [sgK_radius_three_X_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hparent
    exact ⟨hparent.1, ⟨z.1.2.1.1,
      List.mem_toFinset.mp z.1.2.1.2, hparent.2.1, hparent.2.2, rfl⟩⟩
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        have hz := (sgK_radius_three_support_X_box_iff m hm hw).mp z.2
        rcases hz.2 with ⟨q, _, _, _, hpoint⟩
        have hcoordx : z.1.2.1.1.1 = q.1 + 2 ^ m := by
          have h := congrArg Prod.fst hpoint
          simpa [shiftPoint] using h
        have hcoordy : z.1.2.1.1.2 = q.2 := by
          have h := congrArg Prod.snd hpoint
          simpa [shiftPoint] using h
        change shiftPoint (2 ^ m) 1 0
          (z.1.2.1.1.1 - 2 ^ m, z.1.2.1.1.2) = z.1.2.1.1
        simp only [shiftPoint, one_mul, zero_mul, Nat.add_zero]
        apply Prod.ext
        · omega
        · rfl
      · rfl
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        dsimp
        simp [shiftPoint, Nat.add_sub_cancel_right]
      · rfl


/-- The level-(m+1) radius-three support at Y is the image of the
parent-level box under the C-copy shift. The copy coordinate is fixed,
and the spin coordinate is retained. -/
theorem sgK_radius_three_support_Y_box_iff
    (m : ℕ) (hm : 4 ≤ m) {w z : WSG (m + 1)}
    (hw : w.2.1.1 = ((0, 2 ^ (m + 1)) : Point)) :
    z ∈ sgK_radius_three_support (m + 1) w ↔
      z.1 = w.1 ∧
        ∃ p : Point, p ∈ vertexOrder m ∧
          p.1 ≤ 3 ∧ 2 ^ m ≤ p.2 + 3 ∧
          z.2.1.1 = shiftPoint (2 ^ m) 0 1 p := by
  simp only [sgK_radius_three_support, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcopy, _, hx, hy, _⟩
    have hboxX : z.2.1.1.1 ≤ 3 := by
      simpa [hw] using hx
    have hboxY : 2 ^ (m + 1) ≤ z.2.1.1.2 + 3 := by
      simpa [hw] using hy
    rcases (corner_Y_radius_three_box_iff m hm
      (List.mem_toFinset.mp z.2.1.2)).mp ⟨hboxX, hboxY⟩
      with ⟨p, hp, hpx, hpy, hz⟩
    exact ⟨hcopy, ⟨p, hp, hpx, hpy, hz⟩⟩
  · rintro ⟨hcopy, ⟨p, hp, hpx, hpy, hz⟩⟩
    have hbox := (corner_Y_radius_three_box_iff m hm
      (List.mem_toFinset.mp z.2.1.2)).mpr
      ⟨p, hp, hpx, hpy, hz⟩
    have hsum := vertexOrder_sum_le (m + 1) z.2.1.1
      (List.mem_toFinset.mp z.2.1.2)
    refine ⟨hcopy, ?_, ?_, ?_, ?_⟩
    · simp [hw]
    · simpa [hw] using hbox.1
    · simpa [hw] using hbox.2
    · simp [hw]
      omega

/-- Parent-level finite-state support for the radius-three box around Y.
It fixes the copy label and leaves spin unrestricted. -/
def sgK_radius_three_Y_parent_support (m : ℕ) (c : GCopy) :
    Finset (WSG m) :=
  Finset.univ.filter fun z =>
    z.1 = c ∧ z.2.1.1.1 ≤ 3 ∧ 2 ^ m ≤ z.2.1.1.2 + 3

/-- The Y radius-three support is bijective to its parent-level box by
the inverse C shift. This is only a finite-state reindexing statement;
it does not yet compare matrix entries. -/
noncomputable def sgK_radius_three_support_Y_equiv
    (m : ℕ) (hm : 4 ≤ m) {w : WSG (m + 1)}
    (hw : w.2.1.1 = ((0, 2 ^ (m + 1)) : Point)) :
    {z : WSG (m + 1) // z ∈ sgK_radius_three_support (m + 1) w} ≃
      {z : WSG m // z ∈ sgK_radius_three_Y_parent_support m w.1} := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    let p : Point := (z.1.2.1.1.1, z.1.2.1.1.2 - 2 ^ m)
    have hz := (sgK_radius_three_support_Y_box_iff m hm hw).mp z.2
    have hp : p ∈ vertexOrder m := by
      rcases hz.2 with ⟨q, hq, _, _, hpoint⟩
      have hcoordx : z.1.2.1.1.1 = q.1 := by
        have h := congrArg Prod.fst hpoint
        simpa [shiftPoint] using h
      have hcoordy : z.1.2.1.1.2 = q.2 + 2 ^ m := by
        have h := congrArg Prod.snd hpoint
        simpa [shiftPoint] using h
      have hpEq : p = q := by
        dsimp [p]
        exact Prod.ext hcoordx (by omega)
      rw [hpEq]
      exact hq
    have hbounds : p.1 ≤ 3 ∧ 2 ^ m ≤ p.2 + 3 := by
      rcases hz.2 with ⟨q, _, hqx, hqy, hpoint⟩
      have hcoordx : z.1.2.1.1.1 = q.1 := by
        have h := congrArg Prod.fst hpoint
        simpa [shiftPoint] using h
      have hcoordy : z.1.2.1.1.2 = q.2 + 2 ^ m := by
        have h := congrArg Prod.snd hpoint
        simpa [shiftPoint] using h
      constructor
      · dsimp [p]
        rw [hcoordx]
        exact hqx
      · dsimp [p]
        rw [hcoordy]
        simpa [Nat.add_sub_cancel_right] using hqy
    refine ⟨(z.1.1, (⟨p, List.mem_toFinset.mpr hp⟩, z.1.2.2)), ?_⟩
    simp only [sgK_radius_three_Y_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨hz.1, hbounds.1, hbounds.2⟩
  · intro z
    have hp : shiftPoint (2 ^ m) 0 1 z.1.2.1.1 ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inr (Or.inr (List.mem_map.mpr
        ⟨z.1.2.1.1, List.mem_toFinset.mp z.1.2.1.2, rfl⟩))
    refine ⟨(z.1.1,
      (⟨shiftPoint (2 ^ m) 0 1 z.1.2.1.1, List.mem_toFinset.mpr hp⟩,
        z.1.2.2)), ?_⟩
    apply (sgK_radius_three_support_Y_box_iff m hm hw).mpr
    have hparent : z.1 ∈ sgK_radius_three_Y_parent_support m w.1 := z.2
    simp only [sgK_radius_three_Y_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hparent
    exact ⟨hparent.1, ⟨z.1.2.1.1,
      List.mem_toFinset.mp z.1.2.1.2, hparent.2.1, hparent.2.2, rfl⟩⟩
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        have hz := (sgK_radius_three_support_Y_box_iff m hm hw).mp z.2
        rcases hz.2 with ⟨q, _, _, _, hpoint⟩
        have hcoordx : z.1.2.1.1.1 = q.1 := by
          have h := congrArg Prod.fst hpoint
          simpa [shiftPoint] using h
        have hcoordy : z.1.2.1.1.2 = q.2 + 2 ^ m := by
          have h := congrArg Prod.snd hpoint
          simpa [shiftPoint] using h
        change shiftPoint (2 ^ m) 0 1
          (z.1.2.1.1.1, z.1.2.1.1.2 - 2 ^ m) = z.1.2.1.1
        simp only [shiftPoint, zero_mul, one_mul, Nat.add_zero]
        apply Prod.ext
        · rfl
        · omega
      · rfl
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        dsimp
        simp [shiftPoint, Nat.add_sub_cancel_right]
      · rfl

/-- The level-(m+1) radius-two support at X is the image of the level-m
box under the B-copy shift. This is a support-set characterization, not
yet an equality of the weighted path sums. -/
theorem sgK_radius_two_support_X_box_iff
    (m : ℕ) (hm : 3 ≤ m) {w z : WSG (m + 1)}
    (hw : w.2.1.1 = ((2 ^ (m + 1), 0) : Point)) :
    z ∈ sgK_radius_two_support (m + 1) w ↔
      z.1 = w.1 ∧
        ∃ p : Point, p ∈ vertexOrder m ∧
          2 ^ m ≤ p.1 + 2 ∧ p.2 ≤ 2 ∧
          z.2.1.1 = shiftPoint (2 ^ m) 1 0 p := by
  simp only [sgK_radius_two_support, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcopy, hx, _, _, hy⟩
    have hboxX : 2 ^ (m + 1) ≤ z.2.1.1.1 + 2 := by
      simpa [hw] using hx
    have hboxY : z.2.1.1.2 ≤ 2 := by
      simpa [hw] using hy
    rcases (corner_X_radius_two_box_iff m hm (List.mem_toFinset.mp z.2.1.2)).mp
        ⟨hboxX, hboxY⟩ with ⟨p, hp, hpx, hpy, hz⟩
    exact ⟨hcopy, ⟨p, hp, hpx, hpy, hz⟩⟩
  · rintro ⟨hcopy, ⟨p, hp, hpx, hpy, hz⟩⟩
    have hbox := (corner_X_radius_two_box_iff m hm (List.mem_toFinset.mp z.2.1.2)).mpr
      ⟨p, hp, hpx, hpy, hz⟩
    have hsum := vertexOrder_sum_le (m + 1) z.2.1.1
      (List.mem_toFinset.mp z.2.1.2)
    refine ⟨hcopy, ?_, ?_, ?_, ?_⟩
    · simpa [hw] using hbox.1
    · simp [hw]
      omega
    · simp [hw]
    · simpa [hw] using hbox.2



/-- Parent-level support for a radius-two box around the right corner X. -/
def sgK_radius_two_X_parent_support (m : ℕ) (c : GCopy) : Finset (WSG m) :=
  Finset.univ.filter fun z =>
    z.1 = c ∧ 2 ^ m ≤ z.2.1.1.1 + 2 ∧ z.2.1.1.2 ≤ 2

/-- The X-corner radius-two support is in bijection with its parent-level
box under the inverse B shift. The inverse coordinate is written explicitly;
existential witnesses are eliminated only in Prop-valued membership goals,
never while constructing data in Type. -/
noncomputable def sgK_radius_two_support_X_equiv
    (m : ℕ) (hm : 3 ≤ m) {w : WSG (m + 1)}
    (hw : w.2.1.1 = ((2 ^ (m + 1), 0) : Point)) :
    {z : WSG (m + 1) // z ∈ sgK_radius_two_support (m + 1) w} ≃
      {z : WSG m // z ∈ sgK_radius_two_X_parent_support m w.1} := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    let p : Point := (z.1.2.1.1.1 - 2 ^ m, z.1.2.1.1.2)
    have hz := (sgK_radius_two_support_X_box_iff m hm hw).mp z.2
    have hp : p ∈ vertexOrder m := by
      rcases hz.2 with ⟨q, hq, _, _, hpoint⟩
      have hcoordx : z.1.2.1.1.1 = q.1 + 2 ^ m := by
        have h := congrArg Prod.fst hpoint
        simpa [shiftPoint] using h
      have hcoordy : z.1.2.1.1.2 = q.2 := by
        have h := congrArg Prod.snd hpoint
        simpa [shiftPoint] using h
      have hpEq : p = q := by
        dsimp [p]
        exact Prod.ext (by omega) hcoordy
      rw [hpEq]
      exact hq
    have hbounds : 2 ^ m ≤ p.1 + 2 ∧ p.2 ≤ 2 := by
      rcases hz.2 with ⟨q, _, hqx, hqy, hpoint⟩
      have hcoordx : z.1.2.1.1.1 = q.1 + 2 ^ m := by
        have h := congrArg Prod.fst hpoint
        simpa [shiftPoint] using h
      have hcoordy : z.1.2.1.1.2 = q.2 := by
        have h := congrArg Prod.snd hpoint
        simpa [shiftPoint] using h
      constructor
      · dsimp [p]
        omega
      · dsimp [p]
        rw [hcoordy]
        exact hqy
    refine ⟨(z.1.1, (⟨p, List.mem_toFinset.mpr hp⟩, z.1.2.2)), ?_⟩
    simp only [sgK_radius_two_X_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨hz.1, hbounds.1, hbounds.2⟩
  · intro z
    have hp : shiftPoint (2 ^ m) 1 0 z.1.2.1.1 ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inr (Or.inl (List.mem_map.mpr
        ⟨z.1.2.1.1, List.mem_toFinset.mp z.1.2.1.2, rfl⟩))
    refine ⟨(z.1.1,
      (⟨shiftPoint (2 ^ m) 1 0 z.1.2.1.1, List.mem_toFinset.mpr hp⟩,
        z.1.2.2)), ?_⟩
    apply (sgK_radius_two_support_X_box_iff m hm hw).mpr
    have hparent : z.1 ∈ sgK_radius_two_X_parent_support m w.1 := z.2
    simp only [sgK_radius_two_X_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hparent
    exact ⟨hparent.1, ⟨z.1.2.1.1,
      List.mem_toFinset.mp z.1.2.1.2, hparent.2.1, hparent.2.2, rfl⟩⟩
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        have hz := (sgK_radius_two_support_X_box_iff m hm hw).mp z.2
        rcases hz.2 with ⟨q, _, _, _, hpoint⟩
        have hcoordx : z.1.2.1.1.1 = q.1 + 2 ^ m := by
          have h := congrArg Prod.fst hpoint
          simpa [shiftPoint] using h
        have hcoordy : z.1.2.1.1.2 = q.2 := by
          have h := congrArg Prod.snd hpoint
          simpa [shiftPoint] using h
        change shiftPoint (2 ^ m) 1 0
          (z.1.2.1.1.1 - 2 ^ m, z.1.2.1.1.2) = z.1.2.1.1
        simp only [shiftPoint, one_mul, zero_mul, Nat.add_zero]
        apply Prod.ext
        · omega
        · rfl
      · rfl
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        dsimp
        simp [shiftPoint, Nat.add_sub_cancel_right]
      · rfl



/-- X-corner entry transport for the exceptional flipped orientation.
Unlike the numbering-orientation lemma, this transports `oTil) itself: the
single reversed corner edge is carried by the B shift to the corresponding
reversed parent edge. This is the C-copy corner case needed in the power
transport, and does not replace `oTil) by `oNum). -/
theorem pHeO_corner_X_box_entry_next_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : 2 ^ (m + 1) ≤ p.1 + 2) (hpy : p.2 ≤ 2)
    (hqx : 2 ^ (m + 1) ≤ q.1 + 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    ∃ p' q' : Point,
      p' ∈ vertexOrder m ∧ q' ∈ vertexOrder m ∧
      p = shiftPoint (2 ^ m) 1 0 p' ∧
      q = shiftPoint (2 ^ m) 1 0 q' ∧
      pHeO (m + 1) θ ax (oTil (m + 1)) p q i j =
        pHeO m θ ax (oTil m) p' q' i j := by
  rcases (corner_X_radius_two_box_iff m hm hp).mp ⟨hpx, hpy⟩ with
    ⟨p', hp', hpx', hpy', rfl⟩
  rcases (corner_X_radius_two_box_iff m hm hq).mp ⟨hqx, hqy⟩ with
    ⟨q', hq', hqx', hqy', rfl⟩
  have hpow : 2 < 2 ^ m := by
    calc
      2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hp0 : p' ≠ (0, 0) := by
    intro heq
    have hcoord : p'.1 = 0 := congrArg Prod.fst heq
    omega
  have hpY : p' ≠ (0, 2 ^ m) := by
    intro heq
    have hcoord : p'.1 = 0 := congrArg Prod.fst heq
    omega
  refine ⟨p', q', hp', hq', rfl, rfl, ?_⟩
  calc
    pHeO (m + 1) θ ax (oTil (m + 1))
        (shiftPoint (2 ^ m) 1 0 p') (shiftPoint (2 ^ m) 1 0 q') i j =
      pHeO m θ ax (oBo m (oTil (m + 1))) p' q' i j :=
        pHeO_succ_B_local_entry m θ ax (oTil (m + 1)) hax
          hp' hq' hp0 hpY i j
    _ = pHeO m θ ax (oTil m) p' q' i j := by
      apply pHeO_orient_congr m θ ax (oBo m (oTil (m + 1))) (oTil m)
      intro a b hab hE hfl
      have hmEdge := EdgeB_mem m a.1 a.2 b.1 b.2 hE
      have ha : a ∈ vertexOrder m :=
        (mem_vertexOrder_iff m a).mpr hmEdge.1
      have hb : b ∈ vertexOrder m :=
        (mem_vertexOrder_iff m b).mpr hmEdge.2
      have fl : ∀ a b : Point, (a, b) ∈ fluxEdges m →
          ∃ f ∈ facesExact m, f.1 = a ∧ f.2.1 = b := by
        intro a b hab
        obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hab
        have hle := flux_edge_order m f hf
        have h' : fluxEdge f = (f.1, f.2.1) := by
          simp [fluxEdge, hle]
        rw [h'] at hfe
        exact ⟨f, hf, (Prod.mk.inj hfe).1, (Prod.mk.inj hfe).2⟩
      have hanti : OAnti m (oBo m (oTil (m + 1))) :=
        oanti_B m _ (oTil_anti (m + 1))
      by_cases hle : a ≤ b
      · rw [if_pos hle] at hfl
        obtain ⟨f, hf, h1, h2⟩ := fl a b hfl
        rw [← h1, ← h2]
        obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
        obtain ⟨k1, k2⟩ := cp1_shiftB m hs1
        show oTil (m + 1) (shiftPoint (2 ^ m) 1 0 f.1)
            (shiftPoint (2 ^ m) 1 0 f.2.1) ↔ oTil m f.1 f.2.1
        exact oTil_transport (faceB m f hf) k1 k2
      · rw [if_neg hle] at hfl
        obtain ⟨f, hf, h1, h2⟩ := fl b a hfl
        have h3 : oBo m (oTil (m + 1)) f.1 f.2.1 ↔
            oTil m f.1 f.2.1 := by
          obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
          obtain ⟨k1, k2⟩ := cp1_shiftB m hs1
          show oTil (m + 1) (shiftPoint (2 ^ m) 1 0 f.1)
              (shiftPoint (2 ^ m) 1 0 f.2.1) ↔ oTil m f.1 f.2.1
          exact oTil_transport (faceB m f hf) k1 k2
        rw [h1, h2] at h3
        have hanti' : OAnti m (oTil m) := oTil_anti m
        rw [hanti a b ha hb hab, hanti' a b ha hb hab]
        exact not_congr h3



/-- The C-block entry transport near X. First pass from the high C-copy
orientation to its parent tilde orientation using `Hc_C_num_eq_parent_til);
then use the already-established X-corner point transport. The low C-copy
orientation is converted back through the same C-shift argument. -/
theorem sgK_C_X_entry_next_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : 2 ^ (m + 1) ≤ p.1 + 2) (hpy : p.2 ≤ 2)
    (hqx : 2 ^ (m + 1) ≤ q.1 + 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    ∃ p' q' : Pt m,
      p = shiftPoint (2 ^ m) 1 0 p'.1 ∧
      q = shiftPoint (2 ^ m) 1 0 q'.1 ∧
      sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.C, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.C, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.C, (p', i))
        (GCopy.C, (q', j)) := by
  rcases pHeO_corner_X_box_entry_next_til m hm θ ax hax
      hp hq hpx hpy hqx hqy i j with
    ⟨p0, q0, hp0, hq0, hpEq, hqEq, hentry⟩
  have hHighOrient : ∀ a b : Point,
      oCo (m + 1) (oTil (m + 2)) a b ↔
        oCo (m + 1) (oNum (m + 2)) a b := by
    intro a b
    obtain ⟨h1, h2⟩ := cp1_shiftC (m + 1) (p := a) (q := b)
    change oTil (m + 2) (shiftPoint (2 ^ (m + 1)) 0 1 a)
        (shiftPoint (2 ^ (m + 1)) 0 1 b) ↔
      oNum (m + 2) (shiftPoint (2 ^ (m + 1)) 0 1 a)
        (shiftPoint (2 ^ (m + 1)) 0 1 b)
    exact oTil_of_no_corner h1 h2
  have hHighC :
      pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j =
        pHeO (m + 1) θ ax (oTil (m + 1)) p q i j := by
    have h := Hc_C_num_eq_parent_til (m + 1) (by omega) θ ax
      (oNum_anti (m + 2))
      ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i)
      ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)
    change pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j =
      pHeO (m + 1) θ ax (oTil (m + 1)) p q i j at h
    exact h
  have hLowOrient : ∀ a b : Point,
      oCo m (oTil (m + 1)) a b ↔ oCo m (oNum (m + 1)) a b := by
    intro a b
    obtain ⟨h1, h2⟩ := cp1_shiftC m (p := a) (q := b)
    change oTil (m + 1) (shiftPoint (2 ^ m) 0 1 a)
        (shiftPoint (2 ^ m) 0 1 b) ↔
      oNum (m + 1) (shiftPoint (2 ^ m) 0 1 a)
        (shiftPoint (2 ^ m) 0 1 b)
    exact oTil_of_no_corner h1 h2
  have hLowC :
      pHeO m θ ax (oCo m (oNum (m + 1))) p0 q0 i j =
        pHeO m θ ax (oTil m) p0 q0 i j := by
    have h := Hc_C_num_eq_parent_til m (by omega) θ ax
      (oNum_anti (m + 1))
      ((⟨p0, List.mem_toFinset.mpr hp0⟩ : Pt m), i)
      ((⟨q0, List.mem_toFinset.mpr hq0⟩ : Pt m), j)
    change pHeO m θ ax (oCo m (oNum (m + 1))) p0 q0 i j =
      pHeO m θ ax (oTil m) p0 q0 i j at h
    exact h
  refine ⟨(⟨p0, List.mem_toFinset.mpr hp0⟩ : Pt m),
      (⟨q0, List.mem_toFinset.mpr hq0⟩ : Pt m), hpEq, hqEq, ?_⟩
  change pHeO (m + 1) θ ax (oCo (m + 1) (oTil (m + 2))) p q i j =
    pHeO m θ ax (oCo m (oTil (m + 1))) p0 q0 i j
  calc
    pHeO (m + 1) θ ax (oCo (m + 1) (oTil (m + 2))) p q i j =
        pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j :=
      pHeO_rel_congr_local (m + 1) θ ax
        (oCo (m + 1) (oTil (m + 2))) (oCo (m + 1) (oNum (m + 2)))
        p q i j (hHighOrient p q)
    _ = pHeO (m + 1) θ ax (oTil (m + 1)) p q i j := hHighC
    _ = pHeO m θ ax (oTil m) p0 q0 i j := hentry
    _ = pHeO m θ ax (oCo m (oNum (m + 1))) p0 q0 i j := hLowC.symm
    _ = pHeO m θ ax (oCo m (oTil (m + 1))) p0 q0 i j :=
      (pHeO_rel_congr_local m θ ax
        (oCo m (oTil (m + 1))) (oCo m (oNum (m + 1)))
        p0 q0 i j (hLowOrient p0 q0)).symm


/-- The X-corner entry transport with the actual orientations used in the
adjacent-level residual: high level `m+1) uses `oTil (m+2)), while the
parent uses `oTil (m+1)). At these two restricted graphs the flip is absent
from the high local edge and the old parent edge; the B-copy pullback is
therefore reconciled with the parent tilde orientation explicitly. -/
theorem pHeO_corner_X_box_entry_next_til_num
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : 2 ^ (m + 1) ≤ p.1 + 2) (hpy : p.2 ≤ 2)
    (hqx : 2 ^ (m + 1) ≤ q.1 + 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    ∃ p' q' : Point,
      p' ∈ vertexOrder m ∧ q' ∈ vertexOrder m ∧
      p = shiftPoint (2 ^ m) 1 0 p' ∧
      q = shiftPoint (2 ^ m) 1 0 q' ∧
      pHeO (m + 1) θ ax (oTil (m + 2)) p q i j =
        pHeO m θ ax (oTil (m + 1)) p' q' i j := by
  have hhighOrient :
      ∀ a b : Point, a ≠ b →
        EdgeB (m + 1) a.1 a.2 b.1 b.2 = true →
        (if a ≤ b then (a, b) else (b, a)) ∈ fluxEdges (m + 1) →
        (oTil (m + 2) a b ↔ oNum (m + 2) a b) := by
    intro a b hab hE hfl
    have hmEdge := EdgeB_mem (m + 1) a.1 a.2 b.1 b.2 hE
    have ha : a ∈ vertexOrder (m + 1) :=
      (mem_vertexOrder_iff (m + 1) a).mpr hmEdge.1
    have hb : b ∈ vertexOrder (m + 1) :=
      (mem_vertexOrder_iff (m + 1) b).mpr hmEdge.2
    obtain ⟨h1, h2⟩ := cp1_not_A (m + 1) (by omega) ha hb
    exact oTil_of_no_corner h1 h2
  have hhigh := pHeO_orient_congr (m + 1) θ ax
    (oTil (m + 2)) (oNum (m + 2)) hhighOrient
  rcases pHeO_corner_X_box_entry_next_num m hm θ ax hax
      hp hq hpx hpy hqx hqy i j with
    ⟨p', q', hp', hq', rfl, rfl, hentry⟩
  have hparentOrient :
      ∀ a b : Point, a ≠ b →
        EdgeB m a.1 a.2 b.1 b.2 = true →
        (if a ≤ b then (a, b) else (b, a)) ∈ fluxEdges m →
        (oBo m (oNum (m + 1)) a b ↔ oTil (m + 1) a b) := by
    intro a b hab hE hfl
    have hmEdge := EdgeB_mem m a.1 a.2 b.1 b.2 hE
    have ha : a ∈ vertexOrder m :=
      (mem_vertexOrder_iff m a).mpr hmEdge.1
    have hb : b ∈ vertexOrder m :=
      (mem_vertexOrder_iff m b).mpr hmEdge.2
    have hbo : oBo m (oNum (m + 1)) a b ↔ oNum m a b :=
      oBo_num_iff_oNum m ha hb
    have hnum : oNum m a b ↔ oNum (m + 1) a b := by
      unfold oNum
      rw [vIdx_succ_of_mem ha, vIdx_succ_of_mem hb]
    obtain ⟨h1, h2⟩ := cp1_not_A m (by omega) ha hb
    calc
      oBo m (oNum (m + 1)) a b ↔ oNum m a b := hbo
      _ ↔ oNum (m + 1) a b := hnum
      _ ↔ oTil (m + 1) a b := (oTil_of_no_corner h1 h2).symm
  refine ⟨p', q', hp', hq', rfl, rfl, ?_⟩
  calc
    pHeO (m + 1) θ ax (oTil (m + 2))
        (shiftPoint (2 ^ m) 1 0 p') (shiftPoint (2 ^ m) 1 0 q') i j =
      pHeO (m + 1) θ ax (oNum (m + 2))
        (shiftPoint (2 ^ m) 1 0 p') (shiftPoint (2 ^ m) 1 0 q') i j :=
      hhigh _ _ i j
    _ = pHeO m θ ax (oBo m (oNum (m + 1))) p' q' i j := hentry
    _ = pHeO m θ ax (oTil (m + 1)) p' q' i j :=
      pHeO_orient_congr m θ ax
        (oBo m (oNum (m + 1))) (oTil (m + 1))
        hparentOrient p' q' i j


/-- State-index version of the X/B point-entry transport for the A block.
The point witnesses are bundled as `Pt m), so their vertex-membership
proofs are carried with the parent-level matrix states. -/
theorem sgK_A_X_entry_next_til
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : 2 ^ (m + 1) ≤ p.1 + 2) (hpy : p.2 ≤ 2)
    (hqx : 2 ^ (m + 1) ≤ q.1 + 2) (hqy : q.2 ≤ 2)
    (i j : C2) :
    ∃ p' q' : Pt m,
      p = shiftPoint (2 ^ m) 1 0 p'.1 ∧
      q = shiftPoint (2 ^ m) 1 0 q'.1 ∧
      sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.A, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.A, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.A, (p', i))
        (GCopy.A, (q', j)) := by
  rcases pHeO_corner_X_box_entry_next_til_num m hm θ ax hax
      hp hq hpx hpy hqx hqy i j with
    ⟨p0, q0, hp0, hq0, rfl, rfl, hentry⟩
  refine ⟨(⟨p0, List.mem_toFinset.mpr hp0⟩ : Pt m),
      (⟨q0, List.mem_toFinset.mpr hq0⟩ : Pt m), rfl, rfl, ?_⟩
  change pHeO (m + 1) θ ax (oTil (m + 2))
      (shiftPoint (2 ^ m) 1 0 p0) (shiftPoint (2 ^ m) 1 0 q0) i j =
    pHeO m θ ax (oTil (m + 1)) p0 q0 i j
  exact hentry


/-- The level-(m+1) radius-two support at Y is the image of the level-m
box under the C-copy shift. The C orientation and all matrix weights are
deliberately left to the subsequent path-transport proof. -/
theorem sgK_radius_two_support_Y_box_iff
    (m : ℕ) (hm : 3 ≤ m) {w z : WSG (m + 1)}
    (hw : w.2.1.1 = ((0, 2 ^ (m + 1)) : Point)) :
    z ∈ sgK_radius_two_support (m + 1) w ↔
      z.1 = w.1 ∧
        ∃ p : Point, p ∈ vertexOrder m ∧
          p.1 ≤ 2 ∧ 2 ^ m ≤ p.2 + 2 ∧
          z.2.1.1 = shiftPoint (2 ^ m) 0 1 p := by
  simp only [sgK_radius_two_support, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcopy, _, hx, hy, _⟩
    have hboxX : z.2.1.1.1 ≤ 2 := by
      simpa [hw] using hx
    have hboxY : 2 ^ (m + 1) ≤ z.2.1.1.2 + 2 := by
      simpa [hw] using hy
    rcases (corner_Y_radius_two_box_iff m hm (List.mem_toFinset.mp z.2.1.2)).mp
        ⟨hboxX, hboxY⟩ with ⟨p, hp, hpx, hpy, hz⟩
    exact ⟨hcopy, ⟨p, hp, hpx, hpy, hz⟩⟩
  · rintro ⟨hcopy, ⟨p, hp, hpx, hpy, hz⟩⟩
    have hbox := (corner_Y_radius_two_box_iff m hm (List.mem_toFinset.mp z.2.1.2)).mpr
      ⟨p, hp, hpx, hpy, hz⟩
    have hsum := vertexOrder_sum_le (m + 1) z.2.1.1
      (List.mem_toFinset.mp z.2.1.2)
    refine ⟨hcopy, ?_, ?_, ?_, ?_⟩
    · simp [hw]
    · simpa [hw] using hbox.1
    · simpa [hw] using hbox.2
    · simp [hw]
      omega



/-- Parent-level support for a radius-two box around the upper corner Y. -/
def sgK_radius_two_Y_parent_support (m : ℕ) (c : GCopy) : Finset (WSG m) :=
  Finset.univ.filter fun z =>
    z.1 = c ∧ z.2.1.1.1 ≤ 2 ∧ 2 ^ m ≤ z.2.1.1.2 + 2

/-- The Y-corner radius-two support is in bijection with its parent-level
box under the inverse C shift. Coordinates are pulled back explicitly;
this identifies only the finite state sets, not their matrix weights. -/
noncomputable def sgK_radius_two_support_Y_equiv
    (m : ℕ) (hm : 3 ≤ m) {w : WSG (m + 1)}
    (hw : w.2.1.1 = ((0, 2 ^ (m + 1)) : Point)) :
    {z : WSG (m + 1) // z ∈ sgK_radius_two_support (m + 1) w} ≃
      {z : WSG m // z ∈ sgK_radius_two_Y_parent_support m w.1} := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    let p : Point := (z.1.2.1.1.1, z.1.2.1.1.2 - 2 ^ m)
    have hz := (sgK_radius_two_support_Y_box_iff m hm hw).mp z.2
    have hp : p ∈ vertexOrder m := by
      rcases hz.2 with ⟨q, hq, _, _, hpoint⟩
      have hcoordx : z.1.2.1.1.1 = q.1 := by
        have h := congrArg Prod.fst hpoint
        simpa [shiftPoint] using h
      have hcoordy : z.1.2.1.1.2 = q.2 + 2 ^ m := by
        have h := congrArg Prod.snd hpoint
        simpa [shiftPoint] using h
      have hpEq : p = q := by
        dsimp [p]
        exact Prod.ext hcoordx (by omega)
      rw [hpEq]
      exact hq
    have hbounds : p.1 ≤ 2 ∧ 2 ^ m ≤ p.2 + 2 := by
      rcases hz.2 with ⟨q, _, hqx, hqy, hpoint⟩
      have hcoordx : z.1.2.1.1.1 = q.1 := by
        have h := congrArg Prod.fst hpoint
        simpa [shiftPoint] using h
      have hcoordy : z.1.2.1.1.2 = q.2 + 2 ^ m := by
        have h := congrArg Prod.snd hpoint
        simpa [shiftPoint] using h
      constructor
      · dsimp [p]
        rw [hcoordx]
        exact hqx
      · dsimp [p]
        rw [hcoordy]
        simpa [Nat.add_sub_cancel_right] using hqy
    refine ⟨(z.1.1, (⟨p, List.mem_toFinset.mpr hp⟩, z.1.2.2)), ?_⟩
    simp only [sgK_radius_two_Y_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨hz.1, hbounds.1, hbounds.2⟩
  · intro z
    have hp : shiftPoint (2 ^ m) 0 1 z.1.2.1.1 ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inr (Or.inr (List.mem_map.mpr
        ⟨z.1.2.1.1, List.mem_toFinset.mp z.1.2.1.2, rfl⟩))
    refine ⟨(z.1.1,
      (⟨shiftPoint (2 ^ m) 0 1 z.1.2.1.1, List.mem_toFinset.mpr hp⟩,
        z.1.2.2)), ?_⟩
    apply (sgK_radius_two_support_Y_box_iff m hm hw).mpr
    have hparent : z.1 ∈ sgK_radius_two_Y_parent_support m w.1 := z.2
    simp only [sgK_radius_two_Y_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hparent
    exact ⟨hparent.1, ⟨z.1.2.1.1,
      List.mem_toFinset.mp z.1.2.1.2, hparent.2.1, hparent.2.2, rfl⟩⟩
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        have hz := (sgK_radius_two_support_Y_box_iff m hm hw).mp z.2
        rcases hz.2 with ⟨q, _, _, _, hpoint⟩
        have hcoordx : z.1.2.1.1.1 = q.1 := by
          have h := congrArg Prod.fst hpoint
          simpa [shiftPoint] using h
        have hcoordy : z.1.2.1.1.2 = q.2 + 2 ^ m := by
          have h := congrArg Prod.snd hpoint
          simpa [shiftPoint] using h
        change shiftPoint (2 ^ m) 0 1
          (z.1.2.1.1.1, z.1.2.1.1.2 - 2 ^ m) = z.1.2.1.1
        simp only [shiftPoint, zero_mul, one_mul, Nat.add_zero]
        apply Prod.ext
        · rfl
        · omega
      · rfl
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        dsimp
        simp [shiftPoint, Nat.add_sub_cancel_right]
      · rfl


/-- The origin belongs to every recursively defined vertex list. -/
theorem sgK_origin_mem (m : ℕ) : ((0, 0) : Point) ∈ vertexOrder m := by
  induction m with
  | zero => simp [vertexOrder]
  | succ m ih =>
      rw [mem_vertexOrder_succ_iff]
      exact Or.inl ih

/-- Pull a glued corner point of level m+1 back to the corresponding
corner point of level m. Away from the three corners this total auxiliary
map defaults to the origin; it is used only on the glued-state subtype. -/
noncomputable def sgK_root_pullback_pt (m : ℕ) (p : Pt (m + 1)) : Pt m :=
  if p.1 = ((2 ^ (m + 1), 0) : Point) then
    ⟨(2 ^ m, 0), List.mem_toFinset.mpr (cornerX_mem m)⟩
  else if p.1 = ((0, 2 ^ (m + 1)) : Point) then
    ⟨(0, 2 ^ m), List.mem_toFinset.mpr (cornerY_mem m)⟩
  else
    ⟨(0, 0), List.mem_toFinset.mpr (sgK_origin_mem m)⟩

/-- Lift a glued corner point from level m to its corresponding corner
point at level m+1. -/
noncomputable def sgK_root_lift_pt (m : ℕ) (p : Pt m) : Pt (m + 1) :=
  if p.1 = ((2 ^ m, 0) : Point) then
    ⟨(2 ^ (m + 1), 0), List.mem_toFinset.mpr (cornerX_mem (m + 1))⟩
  else if p.1 = ((0, 2 ^ m) : Point) then
    ⟨(0, 2 ^ (m + 1)), List.mem_toFinset.mpr (cornerY_mem (m + 1))⟩
  else
    ⟨(0, 0), List.mem_toFinset.mpr (sgK_origin_mem (m + 1))⟩

@[simp] theorem sgK_root_pullback_pt_O
    (m : ℕ) {p : Pt (m + 1)} (hp : p.1 = ((0, 0) : Point)) :
    (sgK_root_pullback_pt m p).1 = (0, 0) := by
  have hpos : 0 < 2 ^ (m + 1) := by positivity
  have hne : (0 : ℕ) ≠ 2 ^ (m + 1) := (Nat.ne_of_gt hpos).symm
  simp [sgK_root_pullback_pt, hp, hne]

@[simp] theorem sgK_root_pullback_pt_X
    (m : ℕ) {p : Pt (m + 1)} (hp : p.1 = ((2 ^ (m + 1), 0) : Point)) :
    (sgK_root_pullback_pt m p).1 = (2 ^ m, 0) := by
  simp [sgK_root_pullback_pt, hp]

@[simp] theorem sgK_root_pullback_pt_Y
    (m : ℕ) {p : Pt (m + 1)} (hp : p.1 = ((0, 2 ^ (m + 1)) : Point)) :
    (sgK_root_pullback_pt m p).1 = (0, 2 ^ m) := by
  have hpos : 0 < 2 ^ (m + 1) := by positivity
  have hne : (0 : ℕ) ≠ 2 ^ (m + 1) := (Nat.ne_of_gt hpos).symm
  simp [sgK_root_pullback_pt, hp, hne]

@[simp] theorem sgK_root_lift_pt_O
    (m : ℕ) {p : Pt m} (hp : p.1 = ((0, 0) : Point)) :
    (sgK_root_lift_pt m p).1 = (0, 0) := by
  have hpos : 0 < 2 ^ m := by positivity
  have hne : (0 : ℕ) ≠ 2 ^ m := (Nat.ne_of_gt hpos).symm
  simp [sgK_root_lift_pt, hp, hne]

@[simp] theorem sgK_root_lift_pt_X
    (m : ℕ) {p : Pt m} (hp : p.1 = ((2 ^ m, 0) : Point)) :
    (sgK_root_lift_pt m p).1 = (2 ^ (m + 1), 0) := by
  simp [sgK_root_lift_pt, hp]

@[simp] theorem sgK_root_lift_pt_Y
    (m : ℕ) {p : Pt m} (hp : p.1 = ((0, 2 ^ m) : Point)) :
    (sgK_root_lift_pt m p).1 = (0, 2 ^ (m + 1)) := by
  have hpos : 0 < 2 ^ m := by positivity
  have hne : (0 : ℕ) ≠ 2 ^ m := (Nat.ne_of_gt hpos).symm
  simp [sgK_root_lift_pt, hp, hne]

/-- The corresponding corner reindexing of all three-copy states. -/
noncomputable def sgK_root_pullback (m : ℕ) (w : WSG (m + 1)) : WSG m :=
  (w.1, (sgK_root_pullback_pt m w.2.1, w.2.2))

/-- The inverse corner reindexing on glued roots. -/
noncomputable def sgK_root_lift (m : ℕ) (w : WSG m) : WSG (m + 1) :=
  (w.1, (sgK_root_lift_pt m w.2.1, w.2.2))

/-- Pulling back a glued pair preserves the gluing relation. -/
theorem sgK_root_pullback_glW (m : ℕ) {w w' : WSG (m + 1)}
    (h : glW (m + 1) w w') :
    glW m (sgK_root_pullback m w) (sgK_root_pullback m w') := by
  rcases w with ⟨c, p, i⟩
  rcases w' with ⟨c', p', i'⟩
  change gl (m + 1) c p.1 c' p'.1 ∧ i = i' at h
  rcases h with ⟨hgl, hspin⟩
  have hpos : 0 < 2 ^ (m + 1) := by positivity
  have hne : (0 : ℕ) ≠ 2 ^ (m + 1) := (Nat.ne_of_gt hpos).symm
  rcases hgl with
    ⟨rfl, hp, rfl, hp'⟩ |
    ⟨rfl, hp, rfl, hp'⟩ |
    ⟨rfl, hp, rfl, hp'⟩ |
    ⟨rfl, hp, rfl, hp'⟩ |
    ⟨rfl, hp, rfl, hp'⟩ |
    ⟨rfl, hp, rfl, hp'⟩
  all_goals
    change gl m _ (sgK_root_pullback_pt m p).1 _ (sgK_root_pullback_pt m p').1 ∧ i = i'
    constructor
    · simp [gl, sgK_root_pullback, sgK_root_pullback_pt, hp, hp', hne]
    · exact hspin

/-- Lifting a glued pair also preserves the gluing relation. -/
theorem sgK_root_lift_glW (m : ℕ) {w w' : WSG m}
    (h : glW m w w') :
    glW (m + 1) (sgK_root_lift m w) (sgK_root_lift m w') := by
  rcases w with ⟨c, p, i⟩
  rcases w' with ⟨c', p', i'⟩
  change gl m c p.1 c' p'.1 ∧ i = i' at h
  rcases h with ⟨hgl, hspin⟩
  have hpos : 0 < 2 ^ m := by positivity
  have hne : (0 : ℕ) ≠ 2 ^ m := (Nat.ne_of_gt hpos).symm
  rcases hgl with
    ⟨rfl, hp, rfl, hp'⟩ |
    ⟨rfl, hp, rfl, hp'⟩ |
    ⟨rfl, hp, rfl, hp'⟩ |
    ⟨rfl, hp, rfl, hp'⟩ |
    ⟨rfl, hp, rfl, hp'⟩ |
    ⟨rfl, hp, rfl, hp'⟩
  all_goals
    change gl (m + 1) _ (sgK_root_lift_pt m p).1 _ (sgK_root_lift_pt m p').1 ∧ i = i'
    constructor
    · simp [gl, sgK_root_lift, sgK_root_lift_pt, hp, hp', hne]
    · exact hspin

theorem sgK_root_pullback_g (m : ℕ) {w : WSG (m + 1)}
    (hw : (sgGlue (m + 1)).g w) :
    (sgGlue m).g (sgK_root_pullback m w) := by
  obtain ⟨w', hw'⟩ := hw
  exact ⟨sgK_root_pullback m w', sgK_root_pullback_glW m hw'⟩

theorem sgK_root_lift_g (m : ℕ) {w : WSG m}
    (hw : (sgGlue m).g w) :
    (sgGlue (m + 1)).g (sgK_root_lift m w) := by
  obtain ⟨w', hw'⟩ := hw
  exact ⟨sgK_root_lift m w', sgK_root_lift_glW m hw'⟩

/-- The partner map sigma commutes with the glued-root reindexing. This is
essential for transporting the outer sum in the high-power residual. -/
theorem sgK_root_pullback_sigma (m : ℕ) {w : WSG (m + 1)}
    (hw : (sgGlue (m + 1)).g w) :
    sgK_root_pullback m ((sgGlue (m + 1)).σ w) =
      (sgGlue m).σ (sgK_root_pullback m w) := by
  have hhigh : glW (m + 1) w ((sgGlue (m + 1)).σ w) :=
    glW_sgσ hw
  have hlow : glW m (sgK_root_pullback m w)
      (sgK_root_pullback m ((sgGlue (m + 1)).σ w)) :=
    sgK_root_pullback_glW m hhigh
  have hlow' : glW m (sgK_root_pullback m w)
      ((sgGlue m).σ (sgK_root_pullback m w)) :=
    glW_sgσ (sgK_root_pullback_g m hw)
  exact glW_unique hlow hlow'

/-- On a glued root, pulling back after lifting is the identity. -/
theorem sgK_root_pullback_lift (m : ℕ) {w : WSG m}
    (hw : (sgGlue m).g w) :
    sgK_root_pullback m (sgK_root_lift m w) = w := by
  have hcorner : w.2.1.1 = ((0, 0) : Point) ∨
      w.2.1.1 = (2 ^ m, 0) ∨ w.2.1.1 = (0, 2 ^ m) := by
    obtain ⟨w', hgl⟩ := hw
    exact glued_point m w.1 w.2.1.1 ⟨w'.1, w'.2.1.1, hgl.1⟩
  have hpos : 0 < 2 ^ m := by positivity
  have hne : (0 : ℕ) ≠ 2 ^ m := (Nat.ne_of_gt hpos).symm
  have hpos' : 0 < 2 ^ (m + 1) := by positivity
  have hne' : (0 : ℕ) ≠ 2 ^ (m + 1) := (Nat.ne_of_gt hpos').symm
  rcases hcorner with hcorner | hcorner | hcorner
  all_goals
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        simp [sgK_root_pullback, sgK_root_lift,
          sgK_root_pullback_pt, sgK_root_lift_pt, hcorner, hne, hne']
      · rfl

/-- Lifting after pulling back is the identity on the glued-root subtype. -/
theorem sgK_root_lift_pullback (m : ℕ) {w : WSG (m + 1)}
    (hw : (sgGlue (m + 1)).g w) :
    sgK_root_lift m (sgK_root_pullback m w) = w := by
  have hcorner : w.2.1.1 = ((0, 0) : Point) ∨
      w.2.1.1 = (2 ^ (m + 1), 0) ∨ w.2.1.1 = (0, 2 ^ (m + 1)) := by
    obtain ⟨w', hgl⟩ := hw
    exact glued_point (m + 1) w.1 w.2.1.1 ⟨w'.1, w'.2.1.1, hgl.1⟩
  have hpos : 0 < 2 ^ (m + 1) := by positivity
  have hne : (0 : ℕ) ≠ 2 ^ (m + 1) := (Nat.ne_of_gt hpos).symm
  have hpos' : 0 < 2 ^ m := by positivity
  have hne' : (0 : ℕ) ≠ 2 ^ m := (Nat.ne_of_gt hpos').symm
  rcases hcorner with hcorner | hcorner | hcorner
  all_goals
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        simp [sgK_root_pullback, sgK_root_lift,
          sgK_root_pullback_pt, sgK_root_lift_pt, hcorner, hne, hne']
      · rfl

/-- The glued states at adjacent refinement levels are in canonical bijection.
This equivalence preserves copy labels and spin, and its partner-map
compatibility is sgK_root_pullback_sigma. -/
noncomputable def sgK_glued_root_equiv (m : ℕ) :
    {w : WSG (m + 1) // (sgGlue (m + 1)).g w} ≃
      {w : WSG m // (sgGlue m).g w} where
  toFun w := ⟨sgK_root_pullback m w.1, sgK_root_pullback_g m w.2⟩
  invFun w := ⟨sgK_root_lift m w.1, sgK_root_lift_g m w.2⟩
  left_inv w := Subtype.ext (sgK_root_lift_pullback m w.2)
  right_inv w := Subtype.ext (sgK_root_pullback_lift m w.2)



/-- The X radius-three finite-state support transports sixth and seventh
diagonal powers whenever a spin-resolved local entry bridge is supplied.
The parent support is centered at the pulled-back X corner (2^m, 0);
the proof explicitly transfers row and column vanishing through degree
three on both levels before applying the finite-matrix identity. -/
private theorem sgK_X_diag_six_seven_transport_of_entry_bridge
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    (c : GCopy) {w : WSG (m + 1)}
    (hwCopy : w.1 = c)
    (hwPoint : w.2.1.1 = ((2 ^ (m + 1), 0) : Point))
    (hBridge :
      ∀ {p q : Point},
        p ∈ vertexOrder (m + 1) →
        q ∈ vertexOrder (m + 1) →
        2 ^ (m + 1) ≤ p.1 + 3 →
        p.2 ≤ 3 →
        2 ^ (m + 1) ≤ q.1 + 3 →
        q.2 ≤ 3 →
        ∀ i j : C2,
          ∃ p' q' : Pt m,
            p = shiftPoint (2 ^ m) 1 0 p'.1 ∧
            q = shiftPoint (2 ^ m) 1 0 q'.1 ∧
            sgK (m + 1) θ ax (oTil (m + 2))
              (c, ((⟨p, List.mem_toFinset.mpr
                (show p ∈ vertexOrder (m + 1) from by assumption)⟩ :
                  Pt (m + 1)), i))
              (c, ((⟨q, List.mem_toFinset.mpr
                (show q ∈ vertexOrder (m + 1) from by assumption)⟩ :
                  Pt (m + 1)), j)) =
            sgK m θ ax (oTil (m + 1))
              (c, (p', i)) (c, (q', j))) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 6) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 6)
        (sgK_root_pullback m w) (sgK_root_pullback m w) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 7) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 7)
        (sgK_root_pullback m w) (sgK_root_pullback m w) := by
  classical
  let S : Finset (WSG (m + 1)) := sgK_radius_three_support (m + 1) w
  let T : Finset (WSG m) := sgK_radius_three_X_parent_support m c
  let e := sgK_radius_three_support_X_equiv m hm (w := w) hwPoint
  let x' : WSG m := sgK_root_pullback m w

  have hwS : w ∈ S := by
    simp [S, sgK_radius_three_support]
  have hpull : x'.2.1.1 = ((2 ^ m, 0) : Point) := by
    change (sgK_root_pullback_pt m w.2.1).1 = ((2 ^ m, 0) : Point)
    exact sgK_root_pullback_pt_X m hwPoint
  have hrootX : x'.2.1.1.1 = 2 ^ m := by
    have h := congrArg Prod.fst hpull
    simpa using h
  have hrootY : x'.2.1.1.2 = 0 := by
    have h := congrArg Prod.snd hpull
    simpa using h

  have hwT : x' ∈ T := by
    simp only [T, sgK_radius_three_X_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · change w.1 = c
      exact hwCopy
    · rw [hrootX]
      omega
    · rw [hrootY]
      norm_num

  have hroot : e ⟨w, hwS⟩ = ⟨x', hwT⟩ := by
    apply Subtype.ext
    simp [e, sgK_radius_three_support_X_equiv, x',
      sgK_root_pullback, sgK_root_pullback_pt, hwPoint,
      pow_succ, Nat.mul_two]

  have hEntry : ∀ a b : {z : WSG (m + 1) // z ∈ S},
      sgK (m + 1) θ ax (oTil (m + 2)) a.1 b.1 =
        sgK m θ ax (oTil (m + 1)) (e a).1 (e b).1 := by
    intro a b
    have haS : a.1 ∈ sgK_radius_three_support (m + 1) w := by
      simpa [S] using a.2
    have hbS : b.1 ∈ sgK_radius_three_support (m + 1) w := by
      simpa [S] using b.2
    have haBox :=
      (sgK_radius_three_support_X_box_iff m hm hwPoint).mp haS
    have hbBox :=
      (sgK_radius_three_support_X_box_iff m hm hwPoint).mp hbS
    have haCopy : a.1.1 = c := haBox.1.trans hwCopy
    have hbCopy : b.1.1 = c := hbBox.1.trans hwCopy

    have haRaw := a.2
    have hbRaw := b.2
    simp only [S, sgK_radius_three_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at haRaw hbRaw
    have haX : 2 ^ (m + 1) ≤ a.1.2.1.1.1 + 3 := by
      simpa [hwPoint] using haRaw.2.1
    have haY : a.1.2.1.1.2 ≤ 3 := by
      simpa [hwPoint] using haRaw.2.2.2.2
    have hbX : 2 ^ (m + 1) ≤ b.1.2.1.1.1 + 3 := by
      simpa [hwPoint] using hbRaw.2.1
    have hbY : b.1.2.1.1.2 ≤ 3 := by
      simpa [hwPoint] using hbRaw.2.2.2.2

    obtain ⟨pa, pb, hpa, hpb, hbridge⟩ :=
      hBridge
        (p := a.1.2.1.1) (q := b.1.2.1.1)
        (List.mem_toFinset.mp a.1.2.1.2)
        (List.mem_toFinset.mp b.1.2.1.2)
        haX haY hbX hbY a.1.2.2 b.1.2.2

    have haPt :
        (⟨a.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp a.1.2.1.2)⟩ : Pt (m + 1)) =
            a.1.2.1 := by
      apply Subtype.ext
      rfl
    have hbPt :
        (⟨b.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp b.1.2.1.2)⟩ : Pt (m + 1)) =
            b.1.2.1 := by
      apply Subtype.ext
      rfl

    have hpaPoint :
        (a.1.2.1.1.1 - 2 ^ m, a.1.2.1.1.2) = pa.1 := by
      have hx : a.1.2.1.1.1 = pa.1.1 + 2 ^ m := by
        have h := congrArg Prod.fst hpa
        simpa [shiftPoint] using h
      have hy : a.1.2.1.1.2 = pa.1.2 := by
        have h := congrArg Prod.snd hpa
        simpa [shiftPoint] using h
      exact Prod.ext (by omega) hy
    have hpbPoint :
        (b.1.2.1.1.1 - 2 ^ m, b.1.2.1.1.2) = pb.1 := by
      have hx : b.1.2.1.1.1 = pb.1.1 + 2 ^ m := by
        have h := congrArg Prod.fst hpb
        simpa [shiftPoint] using h
      have hy : b.1.2.1.1.2 = pb.1.2 := by
        have h := congrArg Prod.snd hpb
        simpa [shiftPoint] using h
      exact Prod.ext (by omega) hy

    have haState : a.1 = (c, a.1.2) := Prod.ext haCopy rfl
    have hbState : b.1 = (c, b.1.2) := Prod.ext hbCopy rfl
    have haMap : (e a).1 = (c, (pa, a.1.2.2)) := by
      apply Prod.ext
      · exact haCopy
      · apply Prod.ext
        · apply Subtype.ext
          change (a.1.2.1.1.1 - 2 ^ m, a.1.2.1.1.2) = pa.1
          exact hpaPoint
        · rfl
    have hbMap : (e b).1 = (c, (pb, b.1.2.2)) := by
      apply Prod.ext
      · exact hbCopy
      · apply Prod.ext
        · apply Subtype.ext
          change (b.1.2.1.1.1 - 2 ^ m, b.1.2.1.1.2) = pb.1
          exact hpbPoint
        · rfl

    rw [haState, hbState]
    rw [haPt, hbPt] at hbridge
    rw [haMap, hbMap]
    exact hbridge

  have hnotS : ∀ z, z ∉ T →
      z ∉ sgK_radius_three_support m x' := by
    intro z hzT hz
    apply hzT
    have hzs := hz
    simp only [sgK_radius_three_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hzs
    simp only [T, sgK_radius_three_X_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · simpa [x', sgK_root_pullback] using hzs.1
    · simpa [x', sgK_root_pullback, sgK_root_pullback_pt, hwPoint]
        using hzs.2.1
    · simpa [x', sgK_root_pullback, sgK_root_pullback_pt, hwPoint]
        using hzs.2.2.2.2

  have hRowOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) w z = 0 := by
    intro z hz
    have hzero := sgK_pow_entry_zero_outside_radius_three
      (m + 1) θ ax (oTil (m + 2)) 1 (by norm_num) w z
      (by simpa [S] using hz)
    simpa [pow_one] using hzero
  have hColOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) z w = 0 := by
    intro z hz
    have hzero := sgK_pow_entry_zero_outside_radius_three_col
      (m + 1) θ ax (oTil (m + 2)) 1 (by norm_num) z w
      (by simpa [S] using hz)
    simpa [pow_one] using hzero
  have hRowTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) w z = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three
      (m + 1) θ ax (oTil (m + 2)) 2 (by norm_num) w z
      (by simpa [S] using hz)
  have hColTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) z w = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three_col
      (m + 1) θ ax (oTil (m + 2)) 2 (by norm_num) z w
      (by simpa [S] using hz)
  have hRowThree : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 3) w z = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three
      (m + 1) θ ax (oTil (m + 2)) 3 (by norm_num) w z
      (by simpa [S] using hz)
  have hColThree : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 3) z w = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three_col
      (m + 1) θ ax (oTil (m + 2)) 3 (by norm_num) z w
      (by simpa [S] using hz)

  have hRowOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) x' z = 0 := by
    intro z hz
    have hzero := sgK_pow_entry_zero_outside_radius_three
      m θ ax (oTil (m + 1)) 1 (by norm_num) x' z (hnotS z hz)
    simpa [pow_one] using hzero
  have hColOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) z x' = 0 := by
    intro z hz
    have hzero := sgK_pow_entry_zero_outside_radius_three_col
      m θ ax (oTil (m + 1)) 1 (by norm_num) z x' (hnotS z hz)
    simpa [pow_one] using hzero
  have hRowTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) x' z = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three
      m θ ax (oTil (m + 1)) 2 (by norm_num) x' z (hnotS z hz)
  have hColTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) z x' = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three_col
      m θ ax (oTil (m + 1)) 2 (by norm_num) z x' (hnotS z hz)
  have hRowThree' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 3) x' z = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three
      m θ ax (oTil (m + 1)) 3 (by norm_num) x' z (hnotS z hz)
  have hColThree' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 3) z x' = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three_col
      m θ ax (oTil (m + 1)) 3 (by norm_num) z x' (hnotS z hz)

  exact matrix_pow_six_seven_diag_eq_of_local_equiv
    (sgK (m + 1) θ ax (oTil (m + 2)))
    (sgK m θ ax (oTil (m + 1)))
    S T e w x' hwS hwT hroot hEntry
    hRowOne hColOne hRowTwo hColTwo hRowThree hColThree
    hRowOne' hColOne' hRowTwo' hColTwo' hRowThree' hColThree'


/-- Sixth/seventh diagonal transport for the A-copy at its X corner. -/
private theorem sgK_A_X_diag_six_seven_transport
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {w : WSG (m + 1)}
    (hwCopy : w.1 = GCopy.A)
    (hwPoint : w.2.1.1 = ((2 ^ (m + 1), 0) : Point)) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 6) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 6)
        (sgK_root_pullback m w) (sgK_root_pullback m w) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 7) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 7)
        (sgK_root_pullback m w) (sgK_root_pullback m w) := by
  exact sgK_X_diag_six_seven_transport_of_entry_bridge
    m hm θ ax hax GCopy.A hwCopy hwPoint (by
      intro p q hp hq hpx hpy hqx hqy i j
      exact sgK_A_X_entry_next_til_radius_three m hm θ ax hax
        hp hq hpx hpy hqx hqy i j)


/-- Sixth/seventh diagonal transport for the C-copy at its X corner. -/
private theorem sgK_C_X_diag_six_seven_transport
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {w : WSG (m + 1)}
    (hwCopy : w.1 = GCopy.C)
    (hwPoint : w.2.1.1 = ((2 ^ (m + 1), 0) : Point)) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 6) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 6)
        (sgK_root_pullback m w) (sgK_root_pullback m w) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 7) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 7)
        (sgK_root_pullback m w) (sgK_root_pullback m w) := by
  exact sgK_X_diag_six_seven_transport_of_entry_bridge
    m hm θ ax hax GCopy.C hwCopy hwPoint (by
      intro p q hp hq hpx hpy hqx hqy i j
      exact sgK_C_X_entry_next_til_radius_three m hm θ ax hax
        hp hq hpx hpy hqx hqy i j)


end EvgenyTheorem



namespace EvgenyTheorem

/-- At theta = pi, every Pauli-axis rotation has the exact Gaussian-integer form -iσ.
This small local identity is a first stage for the finite-level p=6 base computation. -/
theorem axisRotation_pi (a : Axis) :
    axisRotation a Real.pi = -(Complex.I) • axisPauli a := by
  unfold axisRotation su2Rotation
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- Specialized flux-edge unitary at theta = pi, without unfolding the graph. -/
theorem edgeUnitaryWithAxis_pi (m : ℕ) (axisOfIndex : ℕ → Axis)
    (e : Point × Point) :
    edgeUnitaryWithAxis m Real.pi axisOfIndex e =
      if e ∈ fluxEdges m then
        -(Complex.I) • axisPauli (axisOfIndex (fluxIndex m e))
      else (1 : Matrix C2 C2 ℂ) := by
  unfold edgeUnitaryWithAxis
  split_ifs with he
  · rw [axisRotation_pi]
  · rfl




end EvgenyTheorem


namespace EvgenyTheorem

/-- Every outer corner has degree two at every refinement level. -/
theorem pdeg_corner_O_eq_two (m : ℕ) : pdeg m ((0, 0) : Point) = 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hp : ((0, 0) : Point) ∈ vertexOrder m := corner00_mem m
      have hpX : ((0, 0) : Point) ≠ ((2 ^ m, 0) : Point) := by
        intro h
        have hx := congrArg Prod.fst h
        have hpos : 0 < 2 ^ m := by positivity
        omega
      have hpY : ((0, 0) : Point) ≠ ((0, 2 ^ m) : Point) := by
        intro h
        have hy := congrArg Prod.snd h
        have hpos : 0 < 2 ^ m := by positivity
        omega
      exact (pdeg_succ_A_local m hp hpX hpY).trans ih

/-- The right outer corner also has degree two at every level. -/
theorem pdeg_corner_X_eq_two (m : ℕ) : pdeg m ((2 ^ m, 0) : Point) = 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hp : ((2 ^ m, 0) : Point) ∈ vertexOrder m := cornerX_mem m
      have hpos : 0 < 2 ^ m := by positivity
      have hp0 : ((2 ^ m, 0) : Point) ≠ (0, 0) := by
        intro h
        have hx := congrArg Prod.fst h
        omega
      have hpY : ((2 ^ m, 0) : Point) ≠ ((0, 2 ^ m) : Point) := by
        intro h
        have hx := congrArg Prod.fst h
        omega
      have hshift : ((2 ^ (m + 1), 0) : Point) =
          shiftPoint (2 ^ m) 1 0 ((2 ^ m, 0) : Point) := by
        simp [shiftPoint, pow_succ]
        omega
      calc
        pdeg (m + 1) ((2 ^ (m + 1), 0) : Point) =
            pdeg (m + 1) (shiftPoint (2 ^ m) 1 0 ((2 ^ m, 0) : Point)) := by
              rw [hshift]
        _ = pdeg m ((2 ^ m, 0) : Point) :=
          pdeg_succ_B_local m hp hp0 hpY
        _ = 2 := ih

/-- The upper outer corner also has degree two at every level. -/
theorem pdeg_corner_Y_eq_two (m : ℕ) : pdeg m ((0, 2 ^ m) : Point) = 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hp : ((0, 2 ^ m) : Point) ∈ vertexOrder m := cornerY_mem m
      have hpos : 0 < 2 ^ m := by positivity
      have hp0 : ((0, 2 ^ m) : Point) ≠ (0, 0) := by
        intro h
        have hy := congrArg Prod.snd h
        omega
      have hpX : ((0, 2 ^ m) : Point) ≠ ((2 ^ m, 0) : Point) := by
        intro h
        have hy := congrArg Prod.snd h
        omega
      have hshift : ((0, 2 ^ (m + 1)) : Point) =
          shiftPoint (2 ^ m) 0 1 ((0, 2 ^ m) : Point) := by
        simp [shiftPoint, pow_succ]
        omega
      calc
        pdeg (m + 1) ((0, 2 ^ (m + 1)) : Point) =
            pdeg (m + 1) (shiftPoint (2 ^ m) 0 1 ((0, 2 ^ m) : Point)) := by
              rw [hshift]
        _ = pdeg m ((0, 2 ^ m) : Point) :=
          pdeg_succ_C_local m hp hp0 hpX
        _ = 2 := ih

/-- A state participating in a gluing pair is located at one of the three
outer corners, so its underlying vertex degree is exactly two. -/
theorem pdeg_glued_state_eq_two
    (m : ℕ) {w : WSG m} (hw : (sgGlue m).g w) :
    pdeg m w.2.1.1 = 2 := by
  obtain ⟨w', hww'⟩ := hw
  have hcorner := glued_point m w.1 w.2.1.1
    ⟨w'.1, w'.2.1.1, hww'.1⟩
  rcases hcorner with h | h | h
  · rw [h]
    exact pdeg_corner_O_eq_two m
  · rw [h]
    exact pdeg_corner_X_eq_two m
  · rw [h]
    exact pdeg_corner_Y_eq_two m

/-- Algebraic reduction of the p=6 high-power residual. If K and K' have
diagonal values 2 and squared-diagonal values 6 on every glued state, the
residual is exactly 12 times the difference of the fifth-power corner sums
plus 36 times the difference of the fourth-power corner sums. The partner
map sigma is retained here for the later finite-sum transport. -/
theorem glueRHS6_highPowerResidual_diagonal_reduce
    (m : ℕ) (K K' : Matrix (WSG m) (WSG m) ℂ)
    (hdiag1 : ∀ x, (sgGlue m).g x → K x x = 2)
    (hdiag2 : ∀ x, (sgGlue m).g x → (K ^ 2) x x = 6)
    (hdiag1' : ∀ x, (sgGlue m).g x → K' x x = 2)
    (hdiag2' : ∀ x, (sgGlue m).g x → (K' ^ 2) x x = 6) :
    glueRHS6_highPowerResidual m K K' =
      12 *
        ((∑ x, if (sgGlue m).g x then
            (K ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) -
          (∑ x, if (sgGlue m).g x then
            (K' ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0)) +
      36 *
        ((∑ x, if (sgGlue m).g x then
            (K ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) -
          (∑ x, if (sgGlue m).g x then
            (K' ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0)) := by
  classical
  unfold glueRHS6_highPowerResidual
  have h5 : (∑ x, if (sgGlue m).g x then
      (K ^ 1) x x * (K ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) =
      2 * (∑ x, if (sgGlue m).g x then
        (K ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
    calc
      _ = ∑ x, if (sgGlue m).g x then
            (2 : ℂ) * (K ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : (sgGlue m).g x
          · simp [hx, hdiag1 x hx]
          · simp [hx]
      _ = ∑ x, (2 : ℂ) *
            (if (sgGlue m).g x then
              (K ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : (sgGlue m).g x <;> simp [hx]
      _ = 2 * (∑ x, if (sgGlue m).g x then
            (K ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
          rw [← Finset.mul_sum]
  have h5' : (∑ x, if (sgGlue m).g x then
      (K' ^ 1) x x * (K' ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) =
      2 * (∑ x, if (sgGlue m).g x then
        (K' ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
    calc
      _ = ∑ x, if (sgGlue m).g x then
            (2 : ℂ) * (K' ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : (sgGlue m).g x
          · simp [hx, hdiag1' x hx]
          · simp [hx]
      _ = ∑ x, (2 : ℂ) *
            (if (sgGlue m).g x then
              (K' ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : (sgGlue m).g x <;> simp [hx]
      _ = 2 * (∑ x, if (sgGlue m).g x then
            (K' ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
          rw [← Finset.mul_sum]
  have h4 : (∑ x, if (sgGlue m).g x then
      (K ^ 2) x x * (K ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) =
      6 * (∑ x, if (sgGlue m).g x then
        (K ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
    calc
      _ = ∑ x, if (sgGlue m).g x then
            (6 : ℂ) * (K ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : (sgGlue m).g x
          · simp [hx, hdiag2 x hx]
          · simp [hx]
      _ = ∑ x, (6 : ℂ) *
            (if (sgGlue m).g x then
              (K ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : (sgGlue m).g x <;> simp [hx]
      _ = 6 * (∑ x, if (sgGlue m).g x then
            (K ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
          rw [← Finset.mul_sum]
  have h4' : (∑ x, if (sgGlue m).g x then
      (K' ^ 2) x x * (K' ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) =
      6 * (∑ x, if (sgGlue m).g x then
        (K' ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
    calc
      _ = ∑ x, if (sgGlue m).g x then
            (6 : ℂ) * (K' ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : (sgGlue m).g x
          · simp [hx, hdiag2' x hx]
          · simp [hx]
      _ = ∑ x, (6 : ℂ) *
            (if (sgGlue m).g x then
              (K' ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : (sgGlue m).g x <;> simp [hx]
      _ = 6 * (∑ x, if (sgGlue m).g x then
            (K' ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
          rw [← Finset.mul_sum]
  rw [h5, h5', h4, h4']
  ring

/-- Specialization to the concrete Sierpinski-gasket operator. This is an
exact reduction to weighted corner sums; it does not assert level stability. -/
theorem glueRHS6_highPowerResidual_sgK_corner_reduce
    (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    glueRHS6_highPowerResidual m (sgK m θ ax o) (sgK m θ ax' o) =
      12 *
        ((∑ x, if (sgGlue m).g x then
            (sgK m θ ax o ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) -
          (∑ x, if (sgGlue m).g x then
            (sgK m θ ax' o ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0)) +
      36 *
        ((∑ x, if (sgGlue m).g x then
            (sgK m θ ax o ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) -
          (∑ x, if (sgGlue m).g x then
            (sgK m θ ax' o ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0)) := by
  apply glueRHS6_highPowerResidual_diagonal_reduce
  · intro x hx
    rw [sgK_diag m θ ax o x, pdeg_glued_state_eq_two m hx]
    norm_num
  · intro x hx
    rw [pow_two, sgK_sq_diag m θ ax o hanti x,
      pdeg_glued_state_eq_two m hx]
    norm_num
  · intro x hx
    rw [sgK_diag m θ ax' o x, pdeg_glued_state_eq_two m hx]
    norm_num
  · intro x hx
    rw [pow_two, sgK_sq_diag m θ ax' o hanti x,
      pdeg_glued_state_eq_two m hx]
    norm_num

end EvgenyTheorem


namespace EvgenyTheorem

/-- A conditional finite sum with zero terms off a predicate is exactly
the sum over the predicate subtype. Keeping the summand opaque avoids
unfolding matrix powers during this purely finite-index conversion. -/
private theorem glueRHS6_sum_ite_eq_subtype
    {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (f : α → ℂ) :
    (∑ x, if p x then f x else 0) =
      ∑ x : {x // p x}, f x.1 := by
  classical
  calc
    (∑ x, if p x then f x else 0) =
      (∑ x : {x // p x}, if p x.1 then f x.1 else 0) +
        ∑ x : {x // ¬ p x}, if p x.1 then f x.1 else 0 := by
          exact (Fintype.sum_subtype_add_sum_subtype p
            (fun x => if p x then f x else 0)).symm
    _ = _ := by
      have hpos :
          (∑ x : {x // p x}, if p x.1 then f x.1 else 0) =
            ∑ x : {x // p x}, f x.1 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact if_pos x.2
      have hneg :
          (∑ x : {x // ¬ p x}, if p x.1 then f x.1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        exact if_neg x.2
      rw [hpos, hneg]
      exact add_zero _




/-- Reindex a glued-partner diagonal-power sum across adjacent levels, assuming
the pointwise power entry is preserved by the explicit root pullback. The
partner-map compatibility is used here, so this theorem handles the outer
finite sum and leaves only local power-entry transport as a hypothesis. -/
private theorem glueRHS6_glued_partner_power_sum_transport
    (m n : ℕ)
    (Ahi : Matrix (WSG (m + 1)) (WSG (m + 1)) ℂ)
    (Alo : Matrix (WSG m) (WSG m) ℂ)
    (hpow : ∀ w, (sgGlue (m + 1)).g w →
      (Ahi ^ n) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
        (Alo ^ n)
          (sgK_root_pullback m ((sgGlue (m + 1)).σ w))
          (sgK_root_pullback m ((sgGlue (m + 1)).σ w))) :
    (∑ w, if (sgGlue (m + 1)).g w then
        (Ahi ^ n) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) else 0) =
      ∑ w, if (sgGlue m).g w then
        (Alo ^ n) ((sgGlue m).σ w) ((sgGlue m).σ w) else 0 := by
  classical
  calc
    (∑ w, if (sgGlue (m + 1)).g w then
        (Ahi ^ n) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) else 0) =
      ∑ w : {w // (sgGlue (m + 1)).g w},
        (Ahi ^ n) ((sgGlue (m + 1)).σ w.1) ((sgGlue (m + 1)).σ w.1) := by
          exact glueRHS6_sum_ite_eq_subtype
            (fun w : WSG (m + 1) => (sgGlue (m + 1)).g w)
            (fun w => (Ahi ^ n) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w))
    _ = ∑ w : {w // (sgGlue (m + 1)).g w},
        (Alo ^ n)
          ((sgGlue m).σ (sgK_root_pullback m w.1))
          ((sgGlue m).σ (sgK_root_pullback m w.1)) := by
          apply Finset.sum_congr rfl
          intro w hw
          have hentry := hpow w.1 w.2
          rw [sgK_root_pullback_sigma m w.2] at hentry
          exact hentry
    _ = ∑ w : {w // (sgGlue m).g w},
        (Alo ^ n) ((sgGlue m).σ w.1) ((sgGlue m).σ w.1) := by
          exact Equiv.sum_comp (sgK_glued_root_equiv m)
            (fun w : {w // (sgGlue m).g w} =>
              (Alo ^ n) ((sgGlue m).σ w.1) ((sgGlue m).σ w.1))
    _ = ∑ w, if (sgGlue m).g w then
        (Alo ^ n) ((sgGlue m).σ w) ((sgGlue m).σ w) else 0 := by
          exact (glueRHS6_sum_ite_eq_subtype
            (fun w : WSG m => (sgGlue m).g w)
            (fun w => (Alo ^ n) ((sgGlue m).σ w) ((sgGlue m).σ w))).symm

/-- Restrict a finite sum to a subtype when its summand vanishes outside the
support set. This lets the local path sums be reindexed by a finite-state
equivalence without making assumptions about matrix entries off the box. -/
private theorem finset_sum_eq_subtype_of_zero_outside
    {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : α → ℂ)
    (hzero : ∀ x, x ∉ S → f x = 0) :
    (∑ x, f x) = ∑ x : {x // x ∈ S}, f x.1 := by
  calc
    (∑ x, f x) = ∑ x, if x ∈ S then f x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hs : x ∈ S
      · simp [hs]
      · simp [hzero x hs]
    _ = ∑ x : {x // x ∈ S}, f x.1 := by
      have hsubtype_univ :
          (@Finset.univ {x // x ∈ S}
            (Subtype.fintype (fun x : α => x ∈ S))) =
          (@Finset.univ {x // x ∈ S}
            (Finset.Subtype.fintype S)) := by
        ext x
        simp
      rw [← hsubtype_univ]
      exact glueRHS6_sum_ite_eq_subtype (fun x : α => x ∈ S) f

/-- Local matrix entries determine fourth- and fifth-power diagonals at a
point whenever both one-step and two-step rows/columns vanish outside the
matched finite neighborhoods. The hypothesis `hEntry` is only local: it
relates entries between states in `S` to entries between their images in
`T`. -/
private theorem matrix_pow_four_five_diag_eq_of_local_equiv
    {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    (K : Matrix W W ℂ) (L : Matrix V V ℂ)
    (S : Finset W) (T : Finset V)
    (e : {z : W // z ∈ S} ≃ {z : V // z ∈ T})
    (x : W) (x' : V) (hx : x ∈ S) (hx' : x' ∈ T)
    (hroot : e ⟨x, hx⟩ = ⟨x', hx'⟩)
    (hEntry : ∀ a b : {z : W // z ∈ S},
      K a.1 b.1 = L (e a).1 (e b).1)
    (hRowOne : ∀ z, z ∉ S → K x z = 0)
    (hColOne : ∀ z, z ∉ S → K z x = 0)
    (hRowTwo : ∀ z, z ∉ S → (K ^ 2) x z = 0)
    (hColTwo : ∀ z, z ∉ S → (K ^ 2) z x = 0)
    (hRowOne' : ∀ z, z ∉ T → L x' z = 0)
    (hColOne' : ∀ z, z ∉ T → L z x' = 0)
    (hRowTwo' : ∀ z, z ∉ T → (L ^ 2) x' z = 0)
    (hColTwo' : ∀ z, z ∉ T → (L ^ 2) z x' = 0) :
    (K ^ 4) x x = (L ^ 4) x' x' ∧
      (K ^ 5) x x = (L ^ 5) x' x' := by
  classical
  let xr : {z : W // z ∈ S} := ⟨x, hx⟩
  have hrootVal : (e xr).1 = x' := congrArg Subtype.val hroot

  have hpow2Row : ∀ y : {z : W // z ∈ S},
      (K ^ 2) x y.1 = (L ^ 2) x' (e y).1 := by
    intro y
    calc
      (K ^ 2) x y.1 = ∑ z, K x z * K z y.1 := by
        simp [pow_two, Matrix.mul_apply]
      _ = ∑ z : {z : W // z ∈ S}, K x z.1 * K z.1 y.1 :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun z => K x z * K z y.1)
          (by
            intro z hz
            simp [hRowOne z hz])
      _ = ∑ z : {z : V // z ∈ T}, L x' z.1 * L z.1 (e y).1 := by
        calc
          _ = ∑ z : {z : W // z ∈ S},
              L (e xr).1 (e z).1 * L (e z).1 (e y).1 := by
                apply Finset.sum_congr rfl
                intro z hz
                rw [hEntry xr z, hEntry z y]
          _ = ∑ z : {z : V // z ∈ T}, L x' z.1 * L z.1 (e y).1 := by
                rw [hrootVal]
                exact Equiv.sum_comp e
                  (fun z : {z : V // z ∈ T} => L x' z.1 * L z.1 (e y).1)
      _ = ∑ z, L x' z * L z (e y).1 := by
        symm
        exact finset_sum_eq_subtype_of_zero_outside T
          (fun z => L x' z * L z (e y).1)
          (by
            intro z hz
            simp [hRowOne' z hz])
      _ = (L ^ 2) x' (e y).1 := by
        simp [pow_two, Matrix.mul_apply]

  have hpow2Col : ∀ y : {z : W // z ∈ S},
      (K ^ 2) y.1 x = (L ^ 2) (e y).1 x' := by
    intro y
    calc
      (K ^ 2) y.1 x = ∑ z, K y.1 z * K z x := by
        simp [pow_two, Matrix.mul_apply]
      _ = ∑ z : {z : W // z ∈ S}, K y.1 z.1 * K z.1 x :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun z => K y.1 z * K z x)
          (by
            intro z hz
            simp [hColOne z hz])
      _ = ∑ z : {z : V // z ∈ T}, L (e y).1 z.1 * L z.1 x' := by
        calc
          _ = ∑ z : {z : W // z ∈ S},
              L (e y).1 (e z).1 * L (e z).1 (e xr).1 := by
                apply Finset.sum_congr rfl
                intro z hz
                rw [hEntry y z, hEntry z xr]
          _ = ∑ z : {z : V // z ∈ T}, L (e y).1 z.1 * L z.1 x' := by
                rw [hrootVal]
                exact Equiv.sum_comp e
                  (fun z : {z : V // z ∈ T} => L (e y).1 z.1 * L z.1 x')
      _ = ∑ z, L (e y).1 z * L z x' := by
        symm
        exact finset_sum_eq_subtype_of_zero_outside T
          (fun z => L (e y).1 z * L z x')
          (by
            intro z hz
            simp [hColOne' z hz])
      _ = (L ^ 2) (e y).1 x' := by
        simp [pow_two, Matrix.mul_apply]

  have hpow3Col : ∀ y : {z : W // z ∈ S},
      (K ^ 3) y.1 x = (L ^ 3) (e y).1 x' := by
    intro y
    calc
      (K ^ 3) y.1 x = ∑ z, K y.1 z * (K ^ 2) z x := by
        rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one,
          Matrix.mul_apply]
      _ = ∑ z : {z : W // z ∈ S}, K y.1 z.1 * (K ^ 2) z.1 x :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun z => K y.1 z * (K ^ 2) z x)
          (by
            intro z hz
            simp [hColTwo z hz])
      _ = ∑ z : {z : V // z ∈ T}, L (e y).1 z.1 * (L ^ 2) z.1 x' := by
        calc
          _ = ∑ z : {z : W // z ∈ S},
              L (e y).1 (e z).1 * (L ^ 2) (e z).1 x' := by
                apply Finset.sum_congr rfl
                intro z hz
                rw [hEntry y z, hpow2Col z]
          _ = ∑ z : {z : V // z ∈ T}, L (e y).1 z.1 * (L ^ 2) z.1 x' :=
                Equiv.sum_comp e
                  (fun z : {z : V // z ∈ T} =>
                    L (e y).1 z.1 * (L ^ 2) z.1 x')
      _ = ∑ z, L (e y).1 z * (L ^ 2) z x' := by
        symm
        exact finset_sum_eq_subtype_of_zero_outside T
          (fun z => L (e y).1 z * (L ^ 2) z x')
          (by
            intro z hz
            simp [hColTwo' z hz])
      _ = (L ^ 3) (e y).1 x' := by
        rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one,
          Matrix.mul_apply]

  have hfourK :
      (K ^ 4) x x =
        ∑ y : {z : W // z ∈ S}, (K ^ 2) x y.1 * (K ^ 2) y.1 x := by
    calc
      (K ^ 4) x x =
          ∑ y, (K ^ 2) x y * (K ^ 2) y x :=
        matrix_pow_four_diag_as_sum_sq K x
      _ = ∑ y : {z : W // z ∈ S},
          (K ^ 2) x y.1 * (K ^ 2) y.1 x :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun y => (K ^ 2) x y * (K ^ 2) y x)
          (by
            intro y hy
            simp [hRowTwo y hy])
  have hfourL :
      (L ^ 4) x' x' =
        ∑ y : {z : V // z ∈ T}, (L ^ 2) x' y.1 * (L ^ 2) y.1 x' := by
    calc
      (L ^ 4) x' x' =
          ∑ y, (L ^ 2) x' y * (L ^ 2) y x' :=
        matrix_pow_four_diag_as_sum_sq L x'
      _ = ∑ y : {z : V // z ∈ T},
          (L ^ 2) x' y.1 * (L ^ 2) y.1 x' :=
        finset_sum_eq_subtype_of_zero_outside T
          (fun y => (L ^ 2) x' y * (L ^ 2) y x')
          (by
            intro y hy
            simp [hRowTwo' y hy])

  have hfiveK :
      (K ^ 5) x x =
        ∑ y : {z : W // z ∈ S}, (K ^ 2) x y.1 * (K ^ 3) y.1 x := by
    calc
      (K ^ 5) x x =
          ∑ y, (K ^ 2) x y * (K ^ 3) y x :=
        matrix_pow_five_diag_as_sum_two_three K x
      _ = ∑ y : {z : W // z ∈ S},
          (K ^ 2) x y.1 * (K ^ 3) y.1 x :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun y => (K ^ 2) x y * (K ^ 3) y x)
          (by
            intro y hy
            simp [hRowTwo y hy])
  have hfiveL :
      (L ^ 5) x' x' =
        ∑ y : {z : V // z ∈ T}, (L ^ 2) x' y.1 * (L ^ 3) y.1 x' := by
    calc
      (L ^ 5) x' x' =
          ∑ y, (L ^ 2) x' y * (L ^ 3) y x' :=
        matrix_pow_five_diag_as_sum_two_three L x'
      _ = ∑ y : {z : V // z ∈ T},
          (L ^ 2) x' y.1 * (L ^ 3) y.1 x' :=
        finset_sum_eq_subtype_of_zero_outside T
          (fun y => (L ^ 2) x' y * (L ^ 3) y x')
          (by
            intro y hy
            simp [hRowTwo' y hy])

  constructor
  · calc
      (K ^ 4) x x = ∑ y : {z : W // z ∈ S},
          (K ^ 2) x y.1 * (K ^ 2) y.1 x := hfourK
      _ = ∑ y : {z : V // z ∈ T},
          (L ^ 2) x' y.1 * (L ^ 2) y.1 x' := by
        calc
          _ = ∑ y : {z : W // z ∈ S},
              (L ^ 2) x' (e y).1 * (L ^ 2) (e y).1 x' := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [hpow2Row y, hpow2Col y]
          _ = ∑ y : {z : V // z ∈ T},
              (L ^ 2) x' y.1 * (L ^ 2) y.1 x' :=
                Equiv.sum_comp e
                  (fun y : {z : V // z ∈ T} => (L ^ 2) x' y.1 * (L ^ 2) y.1 x')
      _ = (L ^ 4) x' x' := hfourL.symm
  · calc
      (K ^ 5) x x = ∑ y : {z : W // z ∈ S},
          (K ^ 2) x y.1 * (K ^ 3) y.1 x := hfiveK
      _ = ∑ y : {z : V // z ∈ T},
          (L ^ 2) x' y.1 * (L ^ 3) y.1 x' := by
        calc
          _ = ∑ y : {z : W // z ∈ S},
              (L ^ 2) x' (e y).1 * (L ^ 3) (e y).1 x' := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [hpow2Row y, hpow3Col y]
          _ = ∑ y : {z : V // z ∈ T},
              (L ^ 2) x' y.1 * (L ^ 3) y.1 x' :=
                Equiv.sum_comp e
                  (fun y : {z : V // z ∈ T} => (L ^ 2) x' y.1 * (L ^ 3) y.1 x')
      _ = (L ^ 5) x' x' := hfiveL.symm



/-- Local entries on matched radius-three neighborhoods determine the
sixth- and seventh-power diagonal entries at their roots. The factorizations
are K^6 = K^3*K^3 and K^7 = K^3*K^4; the support hypotheses restrict the
intermediate index to the matched finite neighborhood without reversing any
matrix word. -/
private theorem matrix_pow_six_seven_diag_eq_of_local_equiv
    {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    (K : Matrix W W ℂ) (L : Matrix V V ℂ)
    (S : Finset W) (T : Finset V)
    (e : {z : W // z ∈ S} ≃ {z : V // z ∈ T})
    (x : W) (x' : V) (hx : x ∈ S) (hx' : x' ∈ T)
    (hroot : e ⟨x, hx⟩ = ⟨x', hx'⟩)
    (hEntry : ∀ a b : {z : W // z ∈ S},
      K a.1 b.1 = L (e a).1 (e b).1)
    (hRowOne : ∀ z, z ∉ S → K x z = 0)
    (hColOne : ∀ z, z ∉ S → K z x = 0)
    (hRowTwo : ∀ z, z ∉ S → (K ^ 2) x z = 0)
    (hColTwo : ∀ z, z ∉ S → (K ^ 2) z x = 0)
    (hRowThree : ∀ z, z ∉ S → (K ^ 3) x z = 0)
    (hColThree : ∀ z, z ∉ S → (K ^ 3) z x = 0)
    (hRowOne' : ∀ z, z ∉ T → L x' z = 0)
    (hColOne' : ∀ z, z ∉ T → L z x' = 0)
    (hRowTwo' : ∀ z, z ∉ T → (L ^ 2) x' z = 0)
    (hColTwo' : ∀ z, z ∉ T → (L ^ 2) z x' = 0)
    (hRowThree' : ∀ z, z ∉ T → (L ^ 3) x' z = 0)
    (hColThree' : ∀ z, z ∉ T → (L ^ 3) z x' = 0) :
    (K ^ 6) x x = (L ^ 6) x' x' ∧
      (K ^ 7) x x = (L ^ 7) x' x' := by
  classical
  let xr : {z : W // z ∈ S} := ⟨x, hx⟩
  have hrootVal : (e xr).1 = x' := congrArg Subtype.val hroot
  have hpow2Row : ∀ y : {z : W // z ∈ S},
      (K ^ 2) x y.1 = (L ^ 2) x' (e y).1 := by
    intro y
    calc
      (K ^ 2) x y.1 = ∑ z, K x z * K z y.1 := by
        simp [pow_two, Matrix.mul_apply]
      _ = ∑ z : {z : W // z ∈ S}, K x z.1 * K z.1 y.1 :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun z => K x z * K z y.1)
          (by
            intro z hz
            simp [hRowOne z hz])
      _ = ∑ z : {z : W // z ∈ S},
          L (e xr).1 (e z).1 * L (e z).1 (e y).1 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hEntry xr z, hEntry z y, hrootVal]
      _ = ∑ z : {z : W // z ∈ S},
          L x' (e z).1 * L (e z).1 (e y).1 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hrootVal]
      _ = ∑ z : {z : V // z ∈ T},
          L x' z.1 * L z.1 (e y).1 :=
        Equiv.sum_comp e
          (fun z : {z : V // z ∈ T} => L x' z.1 * L z.1 (e y).1)
      _ = ∑ z, L x' z * L z (e y).1 := by
        symm
        exact finset_sum_eq_subtype_of_zero_outside T
          (fun z => L x' z * L z (e y).1)
          (by
            intro z hz
            simp [hRowOne' z hz])
      _ = (L ^ 2) x' (e y).1 := by
        simp [pow_two, Matrix.mul_apply]
  have hpow2Col : ∀ y : {z : W // z ∈ S},
      (K ^ 2) y.1 x = (L ^ 2) (e y).1 x' := by
    intro y
    calc
      (K ^ 2) y.1 x = ∑ z, K y.1 z * K z x := by
        simp [pow_two, Matrix.mul_apply]
      _ = ∑ z : {z : W // z ∈ S}, K y.1 z.1 * K z.1 x :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun z => K y.1 z * K z x)
          (by
            intro z hz
            simp [hColOne z hz])
      _ = ∑ z : {z : W // z ∈ S},
          L (e y).1 (e z).1 * L (e z).1 x' := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hEntry y z, hEntry z xr, hrootVal]
      _ = ∑ z : {z : V // z ∈ T},
          L (e y).1 z.1 * L z.1 x' :=
        Equiv.sum_comp e
          (fun z : {z : V // z ∈ T} =>
            L (e y).1 z.1 * L z.1 x')
      _ = ∑ z, L (e y).1 z * L z x' := by
        symm
        exact finset_sum_eq_subtype_of_zero_outside T
          (fun z => L (e y).1 z * L z x')
          (by
            intro z hz
            simp [hColOne' z hz])
      _ = (L ^ 2) (e y).1 x' := by
        simp [pow_two, Matrix.mul_apply]
  have hpow3Row : ∀ y : {z : W // z ∈ S},
      (K ^ 3) x y.1 = (L ^ 3) x' (e y).1 := by
    intro y
    calc
      (K ^ 3) x y.1 =
          ∑ z, (K ^ 2) x z * K z y.1 := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num,
          pow_add, pow_one, Matrix.mul_apply]
      _ = ∑ z : {z : W // z ∈ S},
          (K ^ 2) x z.1 * K z.1 y.1 :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun z => (K ^ 2) x z * K z y.1)
          (by
            intro z hz
            simp [hRowTwo z hz])
      _ = ∑ z : {z : W // z ∈ S},
          (L ^ 2) x' (e z).1 * L (e z).1 (e y).1 := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hpow2Row z, hEntry z y]
      _ = ∑ z : {z : V // z ∈ T},
          (L ^ 2) x' z.1 * L z.1 (e y).1 :=
        Equiv.sum_comp e
          (fun z : {z : V // z ∈ T} =>
            (L ^ 2) x' z.1 * L z.1 (e y).1)
      _ = ∑ z, (L ^ 2) x' z * L z (e y).1 := by
        symm
        exact finset_sum_eq_subtype_of_zero_outside T
          (fun z => (L ^ 2) x' z * L z (e y).1)
          (by
            intro z hz
            simp [hRowTwo' z hz])
      _ = (L ^ 3) x' (e y).1 := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num,
          pow_add, pow_one, Matrix.mul_apply]
  have hpow3Col : ∀ y : {z : W // z ∈ S},
      (K ^ 3) y.1 x = (L ^ 3) (e y).1 x' := by
    intro y
    calc
      (K ^ 3) y.1 x =
          ∑ z, K y.1 z * (K ^ 2) z x := by
        rw [show (3 : ℕ) = 1 + 2 by norm_num,
          pow_add, pow_one, Matrix.mul_apply]
      _ = ∑ z : {z : W // z ∈ S},
          K y.1 z.1 * (K ^ 2) z.1 x :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun z => K y.1 z * (K ^ 2) z x)
          (by
            intro z hz
            simp [hColTwo z hz])
      _ = ∑ z : {z : W // z ∈ S},
          L (e y).1 (e z).1 * (L ^ 2) (e z).1 x' := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hEntry y z, hpow2Col z]
      _ = ∑ z : {z : V // z ∈ T},
          L (e y).1 z.1 * (L ^ 2) z.1 x' :=
        Equiv.sum_comp e
          (fun z : {z : V // z ∈ T} =>
            L (e y).1 z.1 * (L ^ 2) z.1 x')
      _ = ∑ z, L (e y).1 z * (L ^ 2) z x' := by
        symm
        exact finset_sum_eq_subtype_of_zero_outside T
          (fun z => L (e y).1 z * (L ^ 2) z x')
          (by
            intro z hz
            simp [hColTwo' z hz])
      _ = (L ^ 3) (e y).1 x' := by
        rw [show (3 : ℕ) = 1 + 2 by norm_num,
          pow_add, pow_one, Matrix.mul_apply]
  have hpow4Col : ∀ y : {z : W // z ∈ S},
      (K ^ 4) y.1 x = (L ^ 4) (e y).1 x' := by
    intro y
    calc
      (K ^ 4) y.1 x =
          ∑ z, K y.1 z * (K ^ 3) z x := by
        rw [show (4 : ℕ) = 1 + 3 by norm_num,
          pow_add, pow_one, Matrix.mul_apply]
      _ = ∑ z : {z : W // z ∈ S},
          K y.1 z.1 * (K ^ 3) z.1 x :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun z => K y.1 z * (K ^ 3) z x)
          (by
            intro z hz
            simp [hColThree z hz])
      _ = ∑ z : {z : W // z ∈ S},
          L (e y).1 (e z).1 * (L ^ 3) (e z).1 x' := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hEntry y z, hpow3Col z]
      _ = ∑ z : {z : V // z ∈ T},
          L (e y).1 z.1 * (L ^ 3) z.1 x' :=
        Equiv.sum_comp e
          (fun z : {z : V // z ∈ T} =>
            L (e y).1 z.1 * (L ^ 3) z.1 x')
      _ = ∑ z, L (e y).1 z * (L ^ 3) z x' := by
        symm
        exact finset_sum_eq_subtype_of_zero_outside T
          (fun z => L (e y).1 z * (L ^ 3) z x')
          (by
            intro z hz
            simp [hColThree' z hz])
      _ = (L ^ 4) (e y).1 x' := by
        rw [show (4 : ℕ) = 1 + 3 by norm_num,
          pow_add, pow_one, Matrix.mul_apply]
  have hsixK : (K ^ 6) x x =
      ∑ y : {z : W // z ∈ S},
        (K ^ 3) x y.1 * (K ^ 3) y.1 x := by
    calc
      (K ^ 6) x x = ∑ y, (K ^ 3) x y * (K ^ 3) y x := by
        rw [show (6 : ℕ) = 3 + 3 by norm_num,
          pow_add, Matrix.mul_apply]
      _ = ∑ y : {z : W // z ∈ S},
          (K ^ 3) x y.1 * (K ^ 3) y.1 x :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun y => (K ^ 3) x y * (K ^ 3) y x)
          (by
            intro y hy
            simp [hRowThree y hy])
  have hsixL : (L ^ 6) x' x' =
      ∑ y : {z : V // z ∈ T},
        (L ^ 3) x' y.1 * (L ^ 3) y.1 x' := by
    calc
      (L ^ 6) x' x' = ∑ y, (L ^ 3) x' y * (L ^ 3) y x' := by
        rw [show (6 : ℕ) = 3 + 3 by norm_num,
          pow_add, Matrix.mul_apply]
      _ = ∑ y : {z : V // z ∈ T},
          (L ^ 3) x' y.1 * (L ^ 3) y.1 x' :=
        finset_sum_eq_subtype_of_zero_outside T
          (fun y => (L ^ 3) x' y * (L ^ 3) y x')
          (by
            intro y hy
            simp [hRowThree' y hy])
  have hsevenK : (K ^ 7) x x =
      ∑ y : {z : W // z ∈ S},
        (K ^ 3) x y.1 * (K ^ 4) y.1 x := by
    calc
      (K ^ 7) x x = ∑ y, (K ^ 3) x y * (K ^ 4) y x := by
        rw [show (7 : ℕ) = 3 + 4 by norm_num,
          pow_add, Matrix.mul_apply]
      _ = ∑ y : {z : W // z ∈ S},
          (K ^ 3) x y.1 * (K ^ 4) y.1 x :=
        finset_sum_eq_subtype_of_zero_outside S
          (fun y => (K ^ 3) x y * (K ^ 4) y x)
          (by
            intro y hy
            simp [hRowThree y hy])
  have hsevenL : (L ^ 7) x' x' =
      ∑ y : {z : V // z ∈ T},
        (L ^ 3) x' y.1 * (L ^ 4) y.1 x' := by
    calc
      (L ^ 7) x' x' = ∑ y, (L ^ 3) x' y * (L ^ 4) y x' := by
        rw [show (7 : ℕ) = 3 + 4 by norm_num,
          pow_add, Matrix.mul_apply]
      _ = ∑ y : {z : V // z ∈ T},
          (L ^ 3) x' y.1 * (L ^ 4) y.1 x' :=
        finset_sum_eq_subtype_of_zero_outside T
          (fun y => (L ^ 3) x' y * (L ^ 4) y x')
          (by
            intro y hy
            simp [hRowThree' y hy])
  constructor
  · calc
      (K ^ 6) x x =
          ∑ y : {z : W // z ∈ S},
            (K ^ 3) x y.1 * (K ^ 3) y.1 x := hsixK
      _ = ∑ y : {z : W // z ∈ S},
          (L ^ 3) x' (e y).1 * (L ^ 3) (e y).1 x' := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hpow3Row y, hpow3Col y]
      _ = ∑ y : {z : V // z ∈ T},
          (L ^ 3) x' y.1 * (L ^ 3) y.1 x' :=
        Equiv.sum_comp e
          (fun y : {z : V // z ∈ T} =>
            (L ^ 3) x' y.1 * (L ^ 3) y.1 x')
      _ = (L ^ 6) x' x' := hsixL.symm
  · calc
      (K ^ 7) x x =
          ∑ y : {z : W // z ∈ S},
            (K ^ 3) x y.1 * (K ^ 4) y.1 x := hsevenK
      _ = ∑ y : {z : W // z ∈ S},
          (L ^ 3) x' (e y).1 * (L ^ 4) (e y).1 x' := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hpow3Row y, hpow4Col y]
      _ = ∑ y : {z : V // z ∈ T},
          (L ^ 3) x' y.1 * (L ^ 4) y.1 x' :=
        Equiv.sum_comp e
          (fun y : {z : V // z ∈ T} =>
            (L ^ 3) x' y.1 * (L ^ 4) y.1 x')
      _ = (L ^ 7) x' x' := hsevenL.symm

/-- Symmetry of the finite radius-two support around its center. -/
private theorem sgK_radius_two_support_symm
    (m : ℕ) (w z : WSG m) :
    z ∈ sgK_radius_two_support m w ↔ w ∈ sgK_radius_two_support m z := by
  constructor <;> intro h
  all_goals
    simp only [sgK_radius_two_support, Finset.mem_filter, Finset.mem_univ,
      true_and] at h ⊢
    rcases h with ⟨hcopy, h1, h2, h3, h4⟩
    exact ⟨hcopy.symm, h2, h1, h4, h3⟩

/-- Symmetry of the finite radius-three support around its center. -/
private theorem sgK_radius_three_support_symm
    (m : ℕ) (w z : WSG m) :
    z ∈ sgK_radius_three_support m w ↔ w ∈ sgK_radius_three_support m z := by
  constructor <;> intro h
  all_goals
    simp only [sgK_radius_three_support, Finset.mem_filter, Finset.mem_univ,
      true_and] at h ⊢
    rcases h with ⟨hcopy, h1, h2, h3, h4⟩
    exact ⟨hcopy.symm, h2, h1, h4, h3⟩

/-- A radius-three column vanishes outside the support, by symmetry of the
support and the established row-vanishing theorem for powers up to three. -/
private theorem sgK_pow_entry_zero_outside_radius_three_col
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (n : ℕ) (hn : n ≤ 3) (w z : WSG m)
    (hz : z ∉ sgK_radius_three_support m w) :
    (sgK m θ ax o ^ n) z w = 0 := by
  have hrev : w ∉ sgK_radius_three_support m z := by
    intro hzw
    exact hz ((sgK_radius_three_support_symm m z w).mp hzw)
  exact sgK_pow_entry_zero_outside_radius_three
    m θ ax o n hn z w hrev

/-- A one-step matrix entry vanishes outside the radius-two support. The
support is symmetric, so the same statement also controls columns. -/
private theorem sgK_entry_zero_outside_radius_two
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (w z : WSG m)
    (hz : z ∉ sgK_radius_two_support m w) :
    sgK m θ ax o w z = 0 := by
  classical
  by_contra hnz
  have hcopy : z.1 = w.1 := by
    by_contra hne
    have hne' : w.1 ≠ z.1 := fun heq => hne heq.symm
    have hzero : sgK m θ ax o w z = 0 := by
      simp [sgK, blockK, hne']
    exact hnz hzero
  have hdist := sgK_entry_coord_dist m θ ax o w z hnz
  have hmem : z ∈ sgK_radius_two_support m w := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hcopy, ?_, ?_, ?_, ?_⟩ <;> omega
  exact hz hmem

/-- Concrete fourth/fifth diagonal transport for the A-copy at its X corner.
This is the first specialization of the finite-neighborhood algebra lemma:
the support equivalence and all entry/vanishing hypotheses come from the
existing corner-local results, not from additional assumptions on the matrix. -/
private theorem sgK_A_X_diag_four_five_transport
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {w : WSG (m + 1)}
    (hwCopy : w.1 = GCopy.A)
    (hwPoint : w.2.1.1 = ((2 ^ (m + 1), 0) : Point)) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 4) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 4)
        (sgK_root_pullback m w) (sgK_root_pullback m w) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 5) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 5)
        (sgK_root_pullback m w) (sgK_root_pullback m w) := by
  classical
  let S : Finset (WSG (m + 1)) := sgK_radius_two_support (m + 1) w
  let T : Finset (WSG m) := sgK_radius_two_X_parent_support m w.1
  let e := sgK_radius_two_support_X_equiv m hm (w := w) hwPoint
  have hwS : w ∈ S := by
    simp [S, sgK_radius_two_support]
  have hwT : sgK_root_pullback m w ∈ T := by
    simp [T, sgK_radius_two_X_parent_support, sgK_root_pullback,
      sgK_root_pullback_pt, hwPoint, pow_succ, Nat.mul_two]
  have hroot : e ⟨w, hwS⟩ = ⟨sgK_root_pullback m w, hwT⟩ := by
    apply Subtype.ext
    simp [e, sgK_radius_two_support_X_equiv, sgK_root_pullback,
      sgK_root_pullback_pt, hwPoint, pow_succ, Nat.mul_two]

  have hEntry : ∀ a b : {z : WSG (m + 1) // z ∈ S},
      sgK (m + 1) θ ax (oTil (m + 2)) a.1 b.1 =
        sgK m θ ax (oTil (m + 1)) (e a).1 (e b).1 := by
    intro a b
    have ha := a.2
    have hb := b.2
    simp only [S, sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha hb
    have haCopy : a.1.1 = GCopy.A := ha.1.trans hwCopy
    have hbCopy : b.1.1 = GCopy.A := hb.1.trans hwCopy
    have haX : 2 ^ (m + 1) ≤ a.1.2.1.1.1 + 2 := by
      simpa [hwPoint] using ha.2.1
    have haY : a.1.2.1.1.2 ≤ 2 := by
      simpa [hwPoint] using ha.2.2.2.2
    have hbX : 2 ^ (m + 1) ≤ b.1.2.1.1.1 + 2 := by
      simpa [hwPoint] using hb.2.1
    have hbY : b.1.2.1.1.2 ≤ 2 := by
      simpa [hwPoint] using hb.2.2.2.2
    obtain ⟨pa, pb, hpa, hpb, hbridge⟩ :=
      sgK_A_X_entry_next_til m hm θ ax hax
        (List.mem_toFinset.mp a.1.2.1.2)
        (List.mem_toFinset.mp b.1.2.1.2)
        haX haY hbX hbY a.1.2.2 b.1.2.2
    have haPt :
        (⟨a.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp a.1.2.1.2)⟩ : Pt (m + 1)) = a.1.2.1 := by
      apply Subtype.ext
      rfl
    have hbPt :
        (⟨b.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp b.1.2.1.2)⟩ : Pt (m + 1)) = b.1.2.1 := by
      apply Subtype.ext
      rfl
    have haState : a.1 = (GCopy.A, a.1.2) := Prod.ext haCopy rfl
    have hbState : b.1 = (GCopy.A, b.1.2) := Prod.ext hbCopy rfl
    have hpaPoint :
        (a.1.2.1.1.1 - 2 ^ m, a.1.2.1.1.2) = pa.1 := by
      have hx : a.1.2.1.1.1 = pa.1.1 + 2 ^ m := by
        have h := congrArg Prod.fst hpa
        simpa [shiftPoint] using h
      have hy : a.1.2.1.1.2 = pa.1.2 := by
        have h := congrArg Prod.snd hpa
        simpa [shiftPoint] using h
      exact Prod.ext (by omega) hy
    have hpbPoint :
        (b.1.2.1.1.1 - 2 ^ m, b.1.2.1.1.2) = pb.1 := by
      have hx : b.1.2.1.1.1 = pb.1.1 + 2 ^ m := by
        have h := congrArg Prod.fst hpb
        simpa [shiftPoint] using h
      have hy : b.1.2.1.1.2 = pb.1.2 := by
        have h := congrArg Prod.snd hpb
        simpa [shiftPoint] using h
      exact Prod.ext (by omega) hy
    have haMap : (e a).1 = (GCopy.A, (pa, a.1.2.2)) := by
      apply Prod.ext
      · exact haCopy
      · apply Prod.ext
        · apply Subtype.ext
          change (a.1.2.1.1.1 - 2 ^ m, a.1.2.1.1.2) = pa.1
          exact hpaPoint
        · rfl
    have hbMap : (e b).1 = (GCopy.A, (pb, b.1.2.2)) := by
      apply Prod.ext
      · exact hbCopy
      · apply Prod.ext
        · apply Subtype.ext
          change (b.1.2.1.1.1 - 2 ^ m, b.1.2.1.1.2) = pb.1
          exact hpbPoint
        · rfl
    rw [haState, hbState]
    rw [haPt, hbPt] at hbridge
    rw [haMap, hbMap]
    exact hbridge

  have hnotS : ∀ z, z ∉ T →
      z ∉ sgK_radius_two_support m (sgK_root_pullback m w) := by
    intro z hzT hzS
    apply hzT
    have hzs := hzS
    simp only [sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hzs
    simp only [T, sgK_radius_two_X_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · simpa [sgK_root_pullback] using hzs.1
    · simpa [sgK_root_pullback, sgK_root_pullback_pt, hwPoint] using hzs.2.1
    · simpa [sgK_root_pullback, sgK_root_pullback_pt, hwPoint] using hzs.2.2.2.2

  have hRowOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) w z = 0 := by
    intro z hz
    exact sgK_entry_zero_outside_radius_two (m + 1) θ ax
      (oTil (m + 2)) w z (by simpa [S] using hz)
  have hColOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) z w = 0 := by
    intro z hz
    have hrev : w ∉ sgK_radius_two_support (m + 1) z := by
      intro hzw
      exact hz ((sgK_radius_two_support_symm (m + 1) z w).mp hzw)
    exact sgK_entry_zero_outside_radius_two (m + 1) θ ax
      (oTil (m + 2)) z w hrev
  have hRowTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) w z = 0 := by
    intro z hz
    exact sgK_pow_two_entry_zero_outside_radius_two
      (m + 1) θ ax (oTil (m + 2)) w z (by simpa [S] using hz)
  have hColTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) z w = 0 := by
    intro z hz
    have hrev : w ∉ sgK_radius_two_support (m + 1) z := by
      intro hzw
      exact hz ((sgK_radius_two_support_symm (m + 1) z w).mp hzw)
    exact sgK_pow_two_entry_zero_outside_radius_two
      (m + 1) θ ax (oTil (m + 2)) z w hrev
  have hRowOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) (sgK_root_pullback m w) z = 0 := by
    intro z hz
    exact sgK_entry_zero_outside_radius_two m θ ax
      (oTil (m + 1)) (sgK_root_pullback m w) z (hnotS z hz)
  have hColOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) z (sgK_root_pullback m w) = 0 := by
    intro z hz
    have hnot := hnotS z hz
    have hrev : sgK_root_pullback m w ∉ sgK_radius_two_support m z := by
      intro hrootz
      exact hnot ((sgK_radius_two_support_symm m z
        (sgK_root_pullback m w)).mp hrootz)
    exact sgK_entry_zero_outside_radius_two m θ ax
      (oTil (m + 1)) z (sgK_root_pullback m w) hrev
  have hRowTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) (sgK_root_pullback m w) z = 0 := by
    intro z hz
    exact sgK_pow_two_entry_zero_outside_radius_two
      m θ ax (oTil (m + 1)) (sgK_root_pullback m w) z (hnotS z hz)
  have hColTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) z (sgK_root_pullback m w) = 0 := by
    intro z hz
    have hnot := hnotS z hz
    have hrev : sgK_root_pullback m w ∉ sgK_radius_two_support m z := by
      intro hrootz
      exact hnot ((sgK_radius_two_support_symm m z
        (sgK_root_pullback m w)).mp hrootz)
    exact sgK_pow_two_entry_zero_outside_radius_two
      m θ ax (oTil (m + 1)) z (sgK_root_pullback m w) hrev

  exact matrix_pow_four_five_diag_eq_of_local_equiv
    (sgK (m + 1) θ ax (oTil (m + 2)))
    (sgK m θ ax (oTil (m + 1)))
    S T e w (sgK_root_pullback m w) hwS hwT hroot hEntry
    hRowOne hColOne hRowTwo hColTwo
    hRowOne' hColOne' hRowTwo' hColTwo'


/-- The C-copy X-corner specialization of fourth/fifth diagonal transport.
It uses the X support reindexing and the existing C/X local entry bridge. -/
private theorem sgK_C_X_diag_four_five_transport
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {w : WSG (m + 1)}
    (hwCopy : w.1 = GCopy.C)
    (hwPoint : w.2.1.1 = ((2 ^ (m + 1), 0) : Point)) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 4) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 4)
        (sgK_root_pullback m w) (sgK_root_pullback m w) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 5) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 5)
        (sgK_root_pullback m w) (sgK_root_pullback m w) := by
  classical
  let S : Finset (WSG (m + 1)) := sgK_radius_two_support (m + 1) w
  let T : Finset (WSG m) := sgK_radius_two_X_parent_support m w.1
  let e := sgK_radius_two_support_X_equiv m hm (w := w) hwPoint
  have hwS : w ∈ S := by
    simp [S, sgK_radius_two_support]
  have hwT : sgK_root_pullback m w ∈ T := by
    simp [T, sgK_radius_two_X_parent_support, sgK_root_pullback,
      sgK_root_pullback_pt, hwPoint, pow_succ, Nat.mul_two]
  have hroot : e ⟨w, hwS⟩ = ⟨sgK_root_pullback m w, hwT⟩ := by
    apply Subtype.ext
    simp [e, sgK_radius_two_support_X_equiv, sgK_root_pullback,
      sgK_root_pullback_pt, hwPoint, pow_succ, Nat.mul_two]

  have hEntry : ∀ a b : {z : WSG (m + 1) // z ∈ S},
      sgK (m + 1) θ ax (oTil (m + 2)) a.1 b.1 =
        sgK m θ ax (oTil (m + 1)) (e a).1 (e b).1 := by
    intro a b
    have ha := a.2
    have hb := b.2
    simp only [S, sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha hb
    have haCopy : a.1.1 = GCopy.C := ha.1.trans hwCopy
    have hbCopy : b.1.1 = GCopy.C := hb.1.trans hwCopy
    have haX : 2 ^ (m + 1) ≤ a.1.2.1.1.1 + 2 := by
      simpa [hwPoint] using ha.2.1
    have haY : a.1.2.1.1.2 ≤ 2 := by
      simpa [hwPoint] using ha.2.2.2.2
    have hbX : 2 ^ (m + 1) ≤ b.1.2.1.1.1 + 2 := by
      simpa [hwPoint] using hb.2.1
    have hbY : b.1.2.1.1.2 ≤ 2 := by
      simpa [hwPoint] using hb.2.2.2.2
    obtain ⟨pa, pb, hpa, hpb, hbridge⟩ :=
      sgK_C_X_entry_next_til m hm θ ax hax
        (List.mem_toFinset.mp a.1.2.1.2)
        (List.mem_toFinset.mp b.1.2.1.2)
        haX haY hbX hbY a.1.2.2 b.1.2.2
    have haPt :
        (⟨a.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp a.1.2.1.2)⟩ : Pt (m + 1)) = a.1.2.1 := by
      apply Subtype.ext
      rfl
    have hbPt :
        (⟨b.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp b.1.2.1.2)⟩ : Pt (m + 1)) = b.1.2.1 := by
      apply Subtype.ext
      rfl
    have haState : a.1 = (GCopy.C, a.1.2) := Prod.ext haCopy rfl
    have hbState : b.1 = (GCopy.C, b.1.2) := Prod.ext hbCopy rfl
    have hpaPoint :
        (a.1.2.1.1.1 - 2 ^ m, a.1.2.1.1.2) = pa.1 := by
      have hx : a.1.2.1.1.1 = pa.1.1 + 2 ^ m := by
        have h := congrArg Prod.fst hpa
        simpa [shiftPoint] using h
      have hy : a.1.2.1.1.2 = pa.1.2 := by
        have h := congrArg Prod.snd hpa
        simpa [shiftPoint] using h
      exact Prod.ext (by omega) hy
    have hpbPoint :
        (b.1.2.1.1.1 - 2 ^ m, b.1.2.1.1.2) = pb.1 := by
      have hx : b.1.2.1.1.1 = pb.1.1 + 2 ^ m := by
        have h := congrArg Prod.fst hpb
        simpa [shiftPoint] using h
      have hy : b.1.2.1.1.2 = pb.1.2 := by
        have h := congrArg Prod.snd hpb
        simpa [shiftPoint] using h
      exact Prod.ext (by omega) hy
    have haMap : (e a).1 = (GCopy.C, (pa, a.1.2.2)) := by
      apply Prod.ext
      · exact haCopy
      · apply Prod.ext
        · apply Subtype.ext
          change (a.1.2.1.1.1 - 2 ^ m, a.1.2.1.1.2) = pa.1
          exact hpaPoint
        · rfl
    have hbMap : (e b).1 = (GCopy.C, (pb, b.1.2.2)) := by
      apply Prod.ext
      · exact hbCopy
      · apply Prod.ext
        · apply Subtype.ext
          change (b.1.2.1.1.1 - 2 ^ m, b.1.2.1.1.2) = pb.1
          exact hpbPoint
        · rfl
    rw [haState, hbState]
    rw [haPt, hbPt] at hbridge
    rw [haMap, hbMap]
    exact hbridge

  have hnotS : ∀ z, z ∉ T →
      z ∉ sgK_radius_two_support m (sgK_root_pullback m w) := by
    intro z hzT hzS
    apply hzT
    have hzs := hzS
    simp only [sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hzs
    simp only [T, sgK_radius_two_X_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · simpa [sgK_root_pullback] using hzs.1
    · simpa [sgK_root_pullback, sgK_root_pullback_pt, hwPoint] using hzs.2.1
    · simpa [sgK_root_pullback, sgK_root_pullback_pt, hwPoint] using hzs.2.2.2.2

  have hRowOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) w z = 0 := by
    intro z hz
    exact sgK_entry_zero_outside_radius_two (m + 1) θ ax
      (oTil (m + 2)) w z (by simpa [S] using hz)
  have hColOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) z w = 0 := by
    intro z hz
    have hrev : w ∉ sgK_radius_two_support (m + 1) z := by
      intro hzw
      exact hz ((sgK_radius_two_support_symm (m + 1) z w).mp hzw)
    exact sgK_entry_zero_outside_radius_two (m + 1) θ ax
      (oTil (m + 2)) z w hrev
  have hRowTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) w z = 0 := by
    intro z hz
    exact sgK_pow_two_entry_zero_outside_radius_two
      (m + 1) θ ax (oTil (m + 2)) w z (by simpa [S] using hz)
  have hColTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) z w = 0 := by
    intro z hz
    have hrev : w ∉ sgK_radius_two_support (m + 1) z := by
      intro hzw
      exact hz ((sgK_radius_two_support_symm (m + 1) z w).mp hzw)
    exact sgK_pow_two_entry_zero_outside_radius_two
      (m + 1) θ ax (oTil (m + 2)) z w hrev
  have hRowOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) (sgK_root_pullback m w) z = 0 := by
    intro z hz
    exact sgK_entry_zero_outside_radius_two m θ ax
      (oTil (m + 1)) (sgK_root_pullback m w) z (hnotS z hz)
  have hColOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) z (sgK_root_pullback m w) = 0 := by
    intro z hz
    have hnot := hnotS z hz
    have hrev : sgK_root_pullback m w ∉ sgK_radius_two_support m z := by
      intro hrootz
      exact hnot ((sgK_radius_two_support_symm m z
        (sgK_root_pullback m w)).mp hrootz)
    exact sgK_entry_zero_outside_radius_two m θ ax
      (oTil (m + 1)) z (sgK_root_pullback m w) hrev
  have hRowTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) (sgK_root_pullback m w) z = 0 := by
    intro z hz
    exact sgK_pow_two_entry_zero_outside_radius_two
      m θ ax (oTil (m + 1)) (sgK_root_pullback m w) z (hnotS z hz)
  have hColTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) z (sgK_root_pullback m w) = 0 := by
    intro z hz
    have hnot := hnotS z hz
    have hrev : sgK_root_pullback m w ∉ sgK_radius_two_support m z := by
      intro hrootz
      exact hnot ((sgK_radius_two_support_symm m z
        (sgK_root_pullback m w)).mp hrootz)
    exact sgK_pow_two_entry_zero_outside_radius_two
      m θ ax (oTil (m + 1)) z (sgK_root_pullback m w) hrev

  exact matrix_pow_four_five_diag_eq_of_local_equiv
    (sgK (m + 1) θ ax (oTil (m + 2)))
    (sgK m θ ax (oTil (m + 1)))
    S T e w (sgK_root_pullback m w) hwS hwT hroot hEntry
    hRowOne hColOne hRowTwo hColTwo
    hRowOne' hColOne' hRowTwo' hColTwo'

private theorem sgK_A_Y_diag_four_five_transport
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    {w : WSG (m + 1)}
    (hwCopy : w.1 = GCopy.A)
    (hwPoint : w.2.1.1 = ((0, 2 ^ (m + 1)) : Point)) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 4) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 4)
        (sgK_root_pullback m w) (sgK_root_pullback m w) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 5) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 5)
        (sgK_root_pullback m w) (sgK_root_pullback m w) := by
  classical
  let S : Finset (WSG (m + 1)) := sgK_radius_two_support (m + 1) w
  let T : Finset (WSG m) := sgK_radius_two_Y_parent_support m w.1
  let e := sgK_radius_two_support_Y_equiv m hm (w := w) hwPoint
  have hwS : w ∈ S := by
    simp [S, sgK_radius_two_support]
  have hpull :
      (sgK_root_pullback m w).2.1.1 = ((0, 2 ^ m) : Point) := by
    change (sgK_root_pullback_pt m w.2.1).1 = ((0, 2 ^ m) : Point)
    exact sgK_root_pullback_pt_Y m hwPoint
  have hrootX : (sgK_root_pullback m w).2.1.1.1 = 0 := by
    have h := congrArg Prod.fst hpull
    simpa using h
  have hrootY : (sgK_root_pullback m w).2.1.1.2 = 2 ^ m := by
    have h := congrArg Prod.snd hpull
    simpa using h
  have hwT : sgK_root_pullback m w ∈ T := by
    simp only [T, sgK_radius_two_Y_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hrootX]
      norm_num
    · rw [hrootY]
      omega
  have hroot : e ⟨w, hwS⟩ = ⟨sgK_root_pullback m w, hwT⟩ := by
    apply Subtype.ext
    simp [e, sgK_radius_two_support_Y_equiv, sgK_root_pullback,
      sgK_root_pullback_pt, hwPoint, pow_succ, Nat.mul_two]

  have hEntry : ∀ a b : {z : WSG (m + 1) // z ∈ S},
      sgK (m + 1) θ ax (oTil (m + 2)) a.1 b.1 =
        sgK m θ ax (oTil (m + 1)) (e a).1 (e b).1 := by
    intro a b
    have ha := a.2
    have hb := b.2
    simp only [S, sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha hb
    have haCopy : a.1.1 = GCopy.A := ha.1.trans hwCopy
    have hbCopy : b.1.1 = GCopy.A := hb.1.trans hwCopy
    have haX : a.1.2.1.1.1 ≤ 2 := by
      simpa [hwPoint] using ha.2.2.1
    have haY : 2 ^ (m + 1) ≤ a.1.2.1.1.2 + 2 := by
      simpa [hwPoint] using ha.2.2.2.1
    have hbX : b.1.2.1.1.1 ≤ 2 := by
      simpa [hwPoint] using hb.2.2.1
    have hbY : 2 ^ (m + 1) ≤ b.1.2.1.1.2 + 2 := by
      simpa [hwPoint] using hb.2.2.2.1
    obtain ⟨pa, pb, hpa, hpb, hbridge⟩ :=
      sgK_A_Y_entry_next_til m hm θ ax hax
        (List.mem_toFinset.mp a.1.2.1.2)
        (List.mem_toFinset.mp b.1.2.1.2)
        haX haY hbX hbY a.1.2.2 b.1.2.2
    have haPt :
        (⟨a.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp a.1.2.1.2)⟩ : Pt (m + 1)) = a.1.2.1 := by
      apply Subtype.ext
      rfl
    have hbPt :
        (⟨b.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp b.1.2.1.2)⟩ : Pt (m + 1)) = b.1.2.1 := by
      apply Subtype.ext
      rfl
    have haState : a.1 = (GCopy.A, a.1.2) := Prod.ext haCopy rfl
    have hbState : b.1 = (GCopy.A, b.1.2) := Prod.ext hbCopy rfl
    have hpaPoint :
        (a.1.2.1.1.1, a.1.2.1.1.2 - 2 ^ m) = pa.1 := by
      have hx : a.1.2.1.1.1 = pa.1.1 := by
        have h := congrArg Prod.fst hpa
        simpa [shiftPoint] using h
      have hy : a.1.2.1.1.2 = pa.1.2 + 2 ^ m := by
        have h := congrArg Prod.snd hpa
        simpa [shiftPoint] using h
      exact Prod.ext hx (by omega)
    have hpbPoint :
        (b.1.2.1.1.1, b.1.2.1.1.2 - 2 ^ m) = pb.1 := by
      have hx : b.1.2.1.1.1 = pb.1.1 := by
        have h := congrArg Prod.fst hpb
        simpa [shiftPoint] using h
      have hy : b.1.2.1.1.2 = pb.1.2 + 2 ^ m := by
        have h := congrArg Prod.snd hpb
        simpa [shiftPoint] using h
      exact Prod.ext hx (by omega)
    have haMap : (e a).1 = (GCopy.A, (pa, a.1.2.2)) := by
      apply Prod.ext
      · exact haCopy
      · apply Prod.ext
        · apply Subtype.ext
          change (a.1.2.1.1.1, a.1.2.1.1.2 - 2 ^ m) = pa.1
          exact hpaPoint
        · rfl
    have hbMap : (e b).1 = (GCopy.A, (pb, b.1.2.2)) := by
      apply Prod.ext
      · exact hbCopy
      · apply Prod.ext
        · apply Subtype.ext
          change (b.1.2.1.1.1, b.1.2.1.1.2 - 2 ^ m) = pb.1
          exact hpbPoint
        · rfl
    rw [haState, hbState]
    rw [haPt, hbPt] at hbridge
    rw [haMap, hbMap]
    exact hbridge

  have hnotS : ∀ z, z ∉ T →
      z ∉ sgK_radius_two_support m (sgK_root_pullback m w) := by
    intro z hzT hzS
    apply hzT
    have hzs := hzS
    simp only [sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hzs
    simp only [T, sgK_radius_two_Y_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · simpa [sgK_root_pullback] using hzs.1
    · have hbound := hzs.2.2.1
      simpa [hrootX] using hbound
    · have hbound := hzs.2.2.2.1
      simpa [hrootY] using hbound

  have hRowOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) w z = 0 := by
    intro z hz
    exact sgK_entry_zero_outside_radius_two (m + 1) θ ax
      (oTil (m + 2)) w z (by simpa [S] using hz)
  have hColOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) z w = 0 := by
    intro z hz
    have hrev : w ∉ sgK_radius_two_support (m + 1) z := by
      intro hzw
      exact hz ((sgK_radius_two_support_symm (m + 1) z w).mp hzw)
    exact sgK_entry_zero_outside_radius_two (m + 1) θ ax
      (oTil (m + 2)) z w hrev
  have hRowTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) w z = 0 := by
    intro z hz
    exact sgK_pow_two_entry_zero_outside_radius_two
      (m + 1) θ ax (oTil (m + 2)) w z (by simpa [S] using hz)
  have hColTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) z w = 0 := by
    intro z hz
    have hrev : w ∉ sgK_radius_two_support (m + 1) z := by
      intro hzw
      exact hz ((sgK_radius_two_support_symm (m + 1) z w).mp hzw)
    exact sgK_pow_two_entry_zero_outside_radius_two
      (m + 1) θ ax (oTil (m + 2)) z w hrev
  have hRowOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) (sgK_root_pullback m w) z = 0 := by
    intro z hz
    exact sgK_entry_zero_outside_radius_two m θ ax
      (oTil (m + 1)) (sgK_root_pullback m w) z (hnotS z hz)
  have hColOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) z (sgK_root_pullback m w) = 0 := by
    intro z hz
    have hnot := hnotS z hz
    have hrev : sgK_root_pullback m w ∉ sgK_radius_two_support m z := by
      intro hrootz
      exact hnot ((sgK_radius_two_support_symm m z
        (sgK_root_pullback m w)).mp hrootz)
    exact sgK_entry_zero_outside_radius_two m θ ax
      (oTil (m + 1)) z (sgK_root_pullback m w) hrev
  have hRowTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) (sgK_root_pullback m w) z = 0 := by
    intro z hz
    exact sgK_pow_two_entry_zero_outside_radius_two
      m θ ax (oTil (m + 1)) (sgK_root_pullback m w) z (hnotS z hz)
  have hColTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) z (sgK_root_pullback m w) = 0 := by
    intro z hz
    have hnot := hnotS z hz
    have hrev : sgK_root_pullback m w ∉ sgK_radius_two_support m z := by
      intro hrootz
      exact hnot ((sgK_radius_two_support_symm m z
        (sgK_root_pullback m w)).mp hrootz)
    exact sgK_pow_two_entry_zero_outside_radius_two
      m θ ax (oTil (m + 1)) z (sgK_root_pullback m w) hrev

  exact matrix_pow_four_five_diag_eq_of_local_equiv
    (sgK (m + 1) θ ax (oTil (m + 2)))
    (sgK m θ ax (oTil (m + 1)))
    S T e w (sgK_root_pullback m w) hwS hwT hroot hEntry
    hRowOne hColOne hRowTwo hColTwo
    hRowOne' hColOne' hRowTwo' hColTwo'




/-- Generic support-local specialization for the fourth/fifth diagonal
transport. The only geometric input beyond the finite equivalence is that
the level-m radius-two support is contained in the chosen parent support. -/
private theorem sgK_diag_four_five_transport_of_support_equiv
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    {w : WSG (m + 1)} {x' : WSG m}
    (T : Finset (WSG m))
    (e : {z : WSG (m + 1) //
        z ∈ sgK_radius_two_support (m + 1) w} ≃
      {z : WSG m // z ∈ T})
    (hwS : w ∈ sgK_radius_two_support (m + 1) w)
    (hxT : x' ∈ T)
    (hroot : e ⟨w, hwS⟩ = ⟨x', hxT⟩)
    (hEntry : ∀ a b : {z : WSG (m + 1) //
        z ∈ sgK_radius_two_support (m + 1) w},
      sgK (m + 1) θ ax (oTil (m + 2)) a.1 b.1 =
        sgK m θ ax (oTil (m + 1)) (e a).1 (e b).1)
    (hsubset : ∀ z, z ∈ sgK_radius_two_support m x' → z ∈ T) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 4) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 4) x' x' ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 5) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 5) x' x' := by
  classical
  let S : Finset (WSG (m + 1)) := sgK_radius_two_support (m + 1) w
  have hnotS : ∀ z, z ∉ T → z ∉ sgK_radius_two_support m x' := by
    intro z hzT hz
    exact hzT (hsubset z hz)

  have hRowOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) w z = 0 := by
    intro z hz
    exact sgK_entry_zero_outside_radius_two (m + 1) θ ax
      (oTil (m + 2)) w z (by simpa [S] using hz)
  have hColOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) z w = 0 := by
    intro z hz
    have hrev : w ∉ sgK_radius_two_support (m + 1) z := by
      intro hzw
      exact hz ((sgK_radius_two_support_symm (m + 1) z w).mp hzw)
    exact sgK_entry_zero_outside_radius_two (m + 1) θ ax
      (oTil (m + 2)) z w hrev
  have hRowTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) w z = 0 := by
    intro z hz
    exact sgK_pow_two_entry_zero_outside_radius_two
      (m + 1) θ ax (oTil (m + 2)) w z (by simpa [S] using hz)
  have hColTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) z w = 0 := by
    intro z hz
    have hrev : w ∉ sgK_radius_two_support (m + 1) z := by
      intro hzw
      exact hz ((sgK_radius_two_support_symm (m + 1) z w).mp hzw)
    exact sgK_pow_two_entry_zero_outside_radius_two
      (m + 1) θ ax (oTil (m + 2)) z w hrev

  have hRowOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) x' z = 0 := by
    intro z hz
    exact sgK_entry_zero_outside_radius_two m θ ax
      (oTil (m + 1)) x' z (hnotS z hz)
  have hColOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) z x' = 0 := by
    intro z hz
    have hnot := hnotS z hz
    have hrev : x' ∉ sgK_radius_two_support m z := by
      intro hzx
      exact hnot ((sgK_radius_two_support_symm m z x').mp hzx)
    exact sgK_entry_zero_outside_radius_two m θ ax
      (oTil (m + 1)) z x' hrev
  have hRowTwo' : ∀ z, z ∉ T →
      ((sgK m θ ax (oTil (m + 1)) ^ 2) x' z) = 0 := by
    intro z hz
    exact sgK_pow_two_entry_zero_outside_radius_two
      m θ ax (oTil (m + 1)) x' z (hnotS z hz)
  have hColTwo' : ∀ z, z ∉ T →
      ((sgK m θ ax (oTil (m + 1)) ^ 2) z x') = 0 := by
    intro z hz
    have hnot := hnotS z hz
    have hrev : x' ∉ sgK_radius_two_support m z := by
      intro hzx
      exact hnot ((sgK_radius_two_support_symm m z x').mp hzx)
    exact sgK_pow_two_entry_zero_outside_radius_two
      m θ ax (oTil (m + 1)) z x' hrev

  exact matrix_pow_four_five_diag_eq_of_local_equiv
    (sgK (m + 1) θ ax (oTil (m + 2)))
    (sgK m θ ax (oTil (m + 1)))
    S T e w x' (by simpa [S] using hwS) hxT hroot hEntry
    hRowOne hColOne hRowTwo hColTwo
    hRowOne' hColOne' hRowTwo' hColTwo'

/-- The B-copy O-corner specialization of the fourth/fifth diagonal
transport. This is the companion glued endpoint to the already checked A/X
case. -/
private theorem sgK_B_O_diag_four_five_transport
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {w : WSG (m + 1)}
    (hwCopy : w.1 = GCopy.B)
    (hwPoint : w.2.1.1 = ((0, 0) : Point)) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 4) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 4)
        (sgK_root_pullback m w) (sgK_root_pullback m w) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 5) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 5)
        (sgK_root_pullback m w) (sgK_root_pullback m w) := by
  classical
  let S : Finset (WSG (m + 1)) := sgK_radius_two_support (m + 1) w
  let T : Finset (WSG m) := sgK_radius_two_O_parent_support m w.1
  let e := sgK_radius_two_support_O_equiv m hm (w := w) hwPoint
  have hwS : w ∈ S := by simp [S, sgK_radius_two_support, hwPoint]
  have hpull : (sgK_root_pullback m w).2.1.1 = ((0, 0) : Point) := by
    change (sgK_root_pullback_pt m w.2.1).1 = ((0, 0) : Point)
    exact sgK_root_pullback_pt_O m hwPoint
  have hrootX : (sgK_root_pullback m w).2.1.1.1 = 0 := by
    have h := congrArg Prod.fst hpull
    simpa using h
  have hrootY : (sgK_root_pullback m w).2.1.1.2 = 0 := by
    have h := congrArg Prod.snd hpull
    simpa using h
  have hwT : sgK_root_pullback m w ∈ T := by
    simp only [T, sgK_radius_two_O_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hrootX]
      norm_num
    · rw [hrootY]
      norm_num
  have hroot : e ⟨w, hwS⟩ = ⟨sgK_root_pullback m w, hwT⟩ := by
    apply Subtype.ext
    change (sgK_radius_two_support_O_equiv m hm (w := w) hwPoint
      ⟨w, hwS⟩).1 = sgK_root_pullback m w
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        exact hwPoint.trans hpull.symm
      · rfl

  have hEntry : ∀ a b : {z : WSG (m + 1) // z ∈ S},
      sgK (m + 1) θ ax (oTil (m + 2)) a.1 b.1 =
        sgK m θ ax (oTil (m + 1)) (e a).1 (e b).1 := by
    intro a b
    have ha := a.2
    have hb := b.2
    simp only [S, sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha hb
    have haCopy : a.1.1 = GCopy.B := ha.1.trans hwCopy
    have hbCopy : b.1.1 = GCopy.B := hb.1.trans hwCopy
    have haX : a.1.2.1.1.1 ≤ 2 := by
      simpa [hwPoint] using ha.2.2.1
    have haY : a.1.2.1.1.2 ≤ 2 := by
      simpa [hwPoint] using ha.2.2.2.2
    have hbX : b.1.2.1.1.1 ≤ 2 := by
      simpa [hwPoint] using hb.2.2.1
    have hbY : b.1.2.1.1.2 ≤ 2 := by
      simpa [hwPoint] using hb.2.2.2.2
    have hpa := corner_O_radius_two_transport m hm
      (List.mem_toFinset.mp a.1.2.1.2) haX haY
    have hpb := corner_O_radius_two_transport m hm
      (List.mem_toFinset.mp b.1.2.1.2) hbX hbY
    have hbridge := sgK_B_O_entry_next_til m hm θ ax
      (List.mem_toFinset.mp a.1.2.1.2)
      (List.mem_toFinset.mp b.1.2.1.2)
      haX haY hbX hbY a.1.2.2 b.1.2.2
    have haPt :
        (⟨a.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp a.1.2.1.2)⟩ : Pt (m + 1)) = a.1.2.1 := by
      apply Subtype.ext
      rfl
    have hbPt :
        (⟨b.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp b.1.2.1.2)⟩ : Pt (m + 1)) = b.1.2.1 := by
      apply Subtype.ext
      rfl
    have haState : a.1 = (GCopy.B, a.1.2) := Prod.ext haCopy rfl
    have hbState : b.1 = (GCopy.B, b.1.2) := Prod.ext hbCopy rfl
    have haMap :
        (e a).1 =
          (GCopy.B,
            ((⟨a.1.2.1.1, List.mem_toFinset.mpr hpa.1⟩ : Pt m),
              a.1.2.2)) := by
      apply Prod.ext
      · exact haCopy
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl
    have hbMap :
        (e b).1 =
          (GCopy.B,
            ((⟨b.1.2.1.1, List.mem_toFinset.mpr hpb.1⟩ : Pt m),
              b.1.2.2)) := by
      apply Prod.ext
      · exact hbCopy
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl
    rw [haState, hbState]
    rw [haPt, hbPt] at hbridge
    rw [haMap, hbMap]
    exact hbridge

  have hsubset : ∀ z, z ∈ sgK_radius_two_support m (sgK_root_pullback m w) →
      z ∈ T := by
    intro z hz
    have hzs := hz
    simp only [sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hzs
    simp only [T, sgK_radius_two_O_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · simpa [sgK_root_pullback] using hzs.1
    · have hbound := hzs.2.2.1
      simpa [hrootX] using hbound
    · have hbound := hzs.2.2.2.2
      simpa [hrootY] using hbound

  exact sgK_diag_four_five_transport_of_support_equiv
    m θ ax T e (by simpa [S] using hwS) hwT hroot hEntry hsubset


private theorem sgK_C_O_diag_four_five_transport
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {w : WSG (m + 1)}
    (hwCopy : w.1 = GCopy.C)
    (hwPoint : w.2.1.1 = ((0, 0) : Point)) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 4) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 4)
        (sgK_root_pullback m w) (sgK_root_pullback m w) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 5) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 5)
        (sgK_root_pullback m w) (sgK_root_pullback m w) := by
  classical
  let S : Finset (WSG (m + 1)) := sgK_radius_two_support (m + 1) w
  let T : Finset (WSG m) := sgK_radius_two_O_parent_support m w.1
  let e := sgK_radius_two_support_O_equiv m hm (w := w) hwPoint
  have hwS : w ∈ S := by simp [S, sgK_radius_two_support, hwPoint]
  have hpull : (sgK_root_pullback m w).2.1.1 = ((0, 0) : Point) := by
    change (sgK_root_pullback_pt m w.2.1).1 = ((0, 0) : Point)
    exact sgK_root_pullback_pt_O m hwPoint
  have hrootX : (sgK_root_pullback m w).2.1.1.1 = 0 := by
    have h := congrArg Prod.fst hpull
    simpa using h
  have hrootY : (sgK_root_pullback m w).2.1.1.2 = 0 := by
    have h := congrArg Prod.snd hpull
    simpa using h
  have hwT : sgK_root_pullback m w ∈ T := by
    simp only [T, sgK_radius_two_O_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hrootX]
      norm_num
    · rw [hrootY]
      norm_num
  have hroot : e ⟨w, hwS⟩ = ⟨sgK_root_pullback m w, hwT⟩ := by
    apply Subtype.ext
    change (sgK_radius_two_support_O_equiv m hm (w := w) hwPoint
      ⟨w, hwS⟩).1 = sgK_root_pullback m w
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        exact hwPoint.trans hpull.symm
      · rfl

  have hEntry : ∀ a b : {z : WSG (m + 1) // z ∈ S},
      sgK (m + 1) θ ax (oTil (m + 2)) a.1 b.1 =
        sgK m θ ax (oTil (m + 1)) (e a).1 (e b).1 := by
    intro a b
    have ha := a.2
    have hb := b.2
    simp only [S, sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha hb
    have haCopy : a.1.1 = GCopy.C := ha.1.trans hwCopy
    have hbCopy : b.1.1 = GCopy.C := hb.1.trans hwCopy
    have haX : a.1.2.1.1.1 ≤ 2 := by
      simpa [hwPoint] using ha.2.2.1
    have haY : a.1.2.1.1.2 ≤ 2 := by
      simpa [hwPoint] using ha.2.2.2.2
    have hbX : b.1.2.1.1.1 ≤ 2 := by
      simpa [hwPoint] using hb.2.2.1
    have hbY : b.1.2.1.1.2 ≤ 2 := by
      simpa [hwPoint] using hb.2.2.2.2
    have hpa := corner_O_radius_two_transport m hm
      (List.mem_toFinset.mp a.1.2.1.2) haX haY
    have hpb := corner_O_radius_two_transport m hm
      (List.mem_toFinset.mp b.1.2.1.2) hbX hbY
    have hbridge := sgK_C_O_entry_next_til m hm θ ax
      (List.mem_toFinset.mp a.1.2.1.2)
      (List.mem_toFinset.mp b.1.2.1.2)
      haX haY hbX hbY a.1.2.2 b.1.2.2
    have haPt :
        (⟨a.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp a.1.2.1.2)⟩ : Pt (m + 1)) = a.1.2.1 := by
      apply Subtype.ext
      rfl
    have hbPt :
        (⟨b.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp b.1.2.1.2)⟩ : Pt (m + 1)) = b.1.2.1 := by
      apply Subtype.ext
      rfl
    have haState : a.1 = (GCopy.C, a.1.2) := Prod.ext haCopy rfl
    have hbState : b.1 = (GCopy.C, b.1.2) := Prod.ext hbCopy rfl
    have haMap :
        (e a).1 =
          (GCopy.C,
            ((⟨a.1.2.1.1, List.mem_toFinset.mpr hpa.1⟩ : Pt m),
              a.1.2.2)) := by
      apply Prod.ext
      · exact haCopy
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl
    have hbMap :
        (e b).1 =
          (GCopy.C,
            ((⟨b.1.2.1.1, List.mem_toFinset.mpr hpb.1⟩ : Pt m),
              b.1.2.2)) := by
      apply Prod.ext
      · exact hbCopy
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl
    rw [haState, hbState]
    rw [haPt, hbPt] at hbridge
    rw [haMap, hbMap]
    exact hbridge

  have hsubset : ∀ z, z ∈ sgK_radius_two_support m (sgK_root_pullback m w) →
      z ∈ T := by
    intro z hz
    have hzs := hz
    simp only [sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hzs
    simp only [T, sgK_radius_two_O_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · simpa [sgK_root_pullback] using hzs.1
    · have hbound := hzs.2.2.1
      simpa [hrootX] using hbound
    · have hbound := hzs.2.2.2.2
      simpa [hrootY] using hbound

  exact sgK_diag_four_five_transport_of_support_equiv
    m θ ax T e (by simpa [S] using hwS) hwT hroot hEntry hsubset

/-- The B-copy Y-corner specialization of fourth/fifth diagonal transport.
It uses the same Y support reindexing, with the existing B/Y local entry bridge. -/
private theorem sgK_B_Y_diag_four_five_transport
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    {w : WSG (m + 1)}
    (hwCopy : w.1 = GCopy.B)
    (hwPoint : w.2.1.1 = ((0, 2 ^ (m + 1)) : Point)) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 4) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 4)
        (sgK_root_pullback m w) (sgK_root_pullback m w) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 5) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 5)
        (sgK_root_pullback m w) (sgK_root_pullback m w) := by
  classical
  let S : Finset (WSG (m + 1)) := sgK_radius_two_support (m + 1) w
  let T : Finset (WSG m) := sgK_radius_two_Y_parent_support m w.1
  let e := sgK_radius_two_support_Y_equiv m hm (w := w) hwPoint
  have hwS : w ∈ S := by
    simp [S, sgK_radius_two_support]
  have hpull :
      (sgK_root_pullback m w).2.1.1 = ((0, 2 ^ m) : Point) := by
    change (sgK_root_pullback_pt m w.2.1).1 = ((0, 2 ^ m) : Point)
    exact sgK_root_pullback_pt_Y m hwPoint
  have hrootX : (sgK_root_pullback m w).2.1.1.1 = 0 := by
    have h := congrArg Prod.fst hpull
    simpa using h
  have hrootY : (sgK_root_pullback m w).2.1.1.2 = 2 ^ m := by
    have h := congrArg Prod.snd hpull
    simpa using h
  have hwT : sgK_root_pullback m w ∈ T := by
    simp only [T, sgK_radius_two_Y_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hrootX]
      norm_num
    · rw [hrootY]
      omega
  have hroot : e ⟨w, hwS⟩ = ⟨sgK_root_pullback m w, hwT⟩ := by
    apply Subtype.ext
    simp [e, sgK_radius_two_support_Y_equiv, sgK_root_pullback,
      sgK_root_pullback_pt, hwPoint, pow_succ, Nat.mul_two]

  have hEntry : ∀ a b : {z : WSG (m + 1) // z ∈ S},
      sgK (m + 1) θ ax (oTil (m + 2)) a.1 b.1 =
        sgK m θ ax (oTil (m + 1)) (e a).1 (e b).1 := by
    intro a b
    have ha := a.2
    have hb := b.2
    simp only [S, sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha hb
    have haCopy : a.1.1 = GCopy.B := ha.1.trans hwCopy
    have hbCopy : b.1.1 = GCopy.B := hb.1.trans hwCopy
    have haX : a.1.2.1.1.1 ≤ 2 := by
      simpa [hwPoint] using ha.2.2.1
    have haY : 2 ^ (m + 1) ≤ a.1.2.1.1.2 + 2 := by
      simpa [hwPoint] using ha.2.2.2.1
    have hbX : b.1.2.1.1.1 ≤ 2 := by
      simpa [hwPoint] using hb.2.2.1
    have hbY : 2 ^ (m + 1) ≤ b.1.2.1.1.2 + 2 := by
      simpa [hwPoint] using hb.2.2.2.1
    obtain ⟨pa, pb, hpa, hpb, hbridge⟩ :=
      sgK_B_Y_entry_next_til m hm θ ax hax
        (List.mem_toFinset.mp a.1.2.1.2)
        (List.mem_toFinset.mp b.1.2.1.2)
        haX haY hbX hbY a.1.2.2 b.1.2.2
    have haPt :
        (⟨a.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp a.1.2.1.2)⟩ : Pt (m + 1)) = a.1.2.1 := by
      apply Subtype.ext
      rfl
    have hbPt :
        (⟨b.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp b.1.2.1.2)⟩ : Pt (m + 1)) = b.1.2.1 := by
      apply Subtype.ext
      rfl
    have haState : a.1 = (GCopy.B, a.1.2) := Prod.ext haCopy rfl
    have hbState : b.1 = (GCopy.B, b.1.2) := Prod.ext hbCopy rfl
    have hpaPoint :
        (a.1.2.1.1.1, a.1.2.1.1.2 - 2 ^ m) = pa.1 := by
      have hx : a.1.2.1.1.1 = pa.1.1 := by
        have h := congrArg Prod.fst hpa
        simpa [shiftPoint] using h
      have hy : a.1.2.1.1.2 = pa.1.2 + 2 ^ m := by
        have h := congrArg Prod.snd hpa
        simpa [shiftPoint] using h
      exact Prod.ext hx (by omega)
    have hpbPoint :
        (b.1.2.1.1.1, b.1.2.1.1.2 - 2 ^ m) = pb.1 := by
      have hx : b.1.2.1.1.1 = pb.1.1 := by
        have h := congrArg Prod.fst hpb
        simpa [shiftPoint] using h
      have hy : b.1.2.1.1.2 = pb.1.2 + 2 ^ m := by
        have h := congrArg Prod.snd hpb
        simpa [shiftPoint] using h
      exact Prod.ext hx (by omega)
    have haMap : (e a).1 = (GCopy.B, (pa, a.1.2.2)) := by
      apply Prod.ext
      · exact haCopy
      · apply Prod.ext
        · apply Subtype.ext
          change (a.1.2.1.1.1, a.1.2.1.1.2 - 2 ^ m) = pa.1
          exact hpaPoint
        · rfl
    have hbMap : (e b).1 = (GCopy.B, (pb, b.1.2.2)) := by
      apply Prod.ext
      · exact hbCopy
      · apply Prod.ext
        · apply Subtype.ext
          change (b.1.2.1.1.1, b.1.2.1.1.2 - 2 ^ m) = pb.1
          exact hpbPoint
        · rfl
    rw [haState, hbState]
    rw [haPt, hbPt] at hbridge
    rw [haMap, hbMap]
    exact hbridge

  have hnotS : ∀ z, z ∉ T →
      z ∉ sgK_radius_two_support m (sgK_root_pullback m w) := by
    intro z hzT hzS
    apply hzT
    have hzs := hzS
    simp only [sgK_radius_two_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hzs
    simp only [T, sgK_radius_two_Y_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · simpa [sgK_root_pullback] using hzs.1
    · have hbound := hzs.2.2.1
      simpa [hrootX] using hbound
    · have hbound := hzs.2.2.2.1
      simpa [hrootY] using hbound

  have hRowOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) w z = 0 := by
    intro z hz
    exact sgK_entry_zero_outside_radius_two (m + 1) θ ax
      (oTil (m + 2)) w z (by simpa [S] using hz)
  have hColOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) z w = 0 := by
    intro z hz
    have hrev : w ∉ sgK_radius_two_support (m + 1) z := by
      intro hzw
      exact hz ((sgK_radius_two_support_symm (m + 1) z w).mp hzw)
    exact sgK_entry_zero_outside_radius_two (m + 1) θ ax
      (oTil (m + 2)) z w hrev
  have hRowTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) w z = 0 := by
    intro z hz
    exact sgK_pow_two_entry_zero_outside_radius_two
      (m + 1) θ ax (oTil (m + 2)) w z (by simpa [S] using hz)
  have hColTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) z w = 0 := by
    intro z hz
    have hrev : w ∉ sgK_radius_two_support (m + 1) z := by
      intro hzw
      exact hz ((sgK_radius_two_support_symm (m + 1) z w).mp hzw)
    exact sgK_pow_two_entry_zero_outside_radius_two
      (m + 1) θ ax (oTil (m + 2)) z w hrev
  have hRowOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) (sgK_root_pullback m w) z = 0 := by
    intro z hz
    exact sgK_entry_zero_outside_radius_two m θ ax
      (oTil (m + 1)) (sgK_root_pullback m w) z (hnotS z hz)
  have hColOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) z (sgK_root_pullback m w) = 0 := by
    intro z hz
    have hnot := hnotS z hz
    have hrev : sgK_root_pullback m w ∉ sgK_radius_two_support m z := by
      intro hrootz
      exact hnot ((sgK_radius_two_support_symm m z
        (sgK_root_pullback m w)).mp hrootz)
    exact sgK_entry_zero_outside_radius_two m θ ax
      (oTil (m + 1)) z (sgK_root_pullback m w) hrev
  have hRowTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) (sgK_root_pullback m w) z = 0 := by
    intro z hz
    exact sgK_pow_two_entry_zero_outside_radius_two
      m θ ax (oTil (m + 1)) (sgK_root_pullback m w) z (hnotS z hz)
  have hColTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) z (sgK_root_pullback m w) = 0 := by
    intro z hz
    have hnot := hnotS z hz
    have hrev : sgK_root_pullback m w ∉ sgK_radius_two_support m z := by
      intro hrootz
      exact hnot ((sgK_radius_two_support_symm m z
        (sgK_root_pullback m w)).mp hrootz)
    exact sgK_pow_two_entry_zero_outside_radius_two
      m θ ax (oTil (m + 1)) z (sgK_root_pullback m w) hrev

  exact matrix_pow_four_five_diag_eq_of_local_equiv
    (sgK (m + 1) θ ax (oTil (m + 2)))
    (sgK m θ ax (oTil (m + 1)))
    S T e w (sgK_root_pullback m w) hwS hwT hroot hEntry
    hRowOne hColOne hRowTwo hColTwo
    hRowOne' hColOne' hRowTwo' hColTwo'




/-- For any glued state, the partner `σ w` is one of the six corner/copy
endpoints. Reduce its fourth/fifth diagonal transport to the matching local
support-equivalence specialization. -/
private theorem sgK_glued_partner_diag_four_five_transport
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (haxX : ∀ k, ax (3 ^ m + k) = ax k)
    (haxY : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    {w : WSG (m + 1)} (hw : (sgGlue (m + 1)).g w) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 4)
        ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
      (sgK m θ ax (oTil (m + 1)) ^ 4)
        (sgK_root_pullback m ((sgGlue (m + 1)).σ w))
        (sgK_root_pullback m ((sgGlue (m + 1)).σ w)) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 5)
        ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
      (sgK m θ ax (oTil (m + 1)) ^ 5)
        (sgK_root_pullback m ((sgGlue (m + 1)).σ w))
        (sgK_root_pullback m ((sgGlue (m + 1)).σ w)) := by
  classical
  have hex : ∃ w', glW (m + 1) w w' := by
    change ∃ w', glW (m + 1) w w'
    exact hw
  have hpartner : glW (m + 1) w ((sgGlue (m + 1)).σ w) := by
    change glW (m + 1) w (sgσ (m + 1) w)
    exact glW_sgσ hex
  rcases hpartner with ⟨hgl, hspin⟩
  rcases hgl with
      ⟨hA, hX, hB, hO⟩
    | ⟨hB, hO, hA, hX⟩
    | ⟨hA, hY, hC, hO⟩
    | ⟨hC, hO, hA, hY⟩
    | ⟨hB, hY, hC, hX⟩
    | ⟨hC, hX, hB, hY⟩
  · exact sgK_B_O_diag_four_five_transport m hm θ ax hB hO
  · exact sgK_A_X_diag_four_five_transport m hm θ ax haxX hA hX
  · exact sgK_C_O_diag_four_five_transport m hm θ ax hC hO
  · exact sgK_A_Y_diag_four_five_transport m hm θ ax haxY hA hY
  · exact sgK_C_X_diag_four_five_transport m hm θ ax haxX hC hX
  · exact sgK_B_Y_diag_four_five_transport m hm θ ax haxY hB hY

/-- The remaining outer-sum step in the p=6 residual proof. If the local
fourth- and fifth-power diagonal entries transport at every glued partner
root, then the full high-power residual is stable across adjacent levels.
The hypotheses on powers one and two are exactly those needed to invoke the
already-proved algebraic residual reduction. -/
theorem glueRHS6_highPowerResidual_eq_of_corner_power_transport
    (m : ℕ)
    (Khi Khi' : Matrix (WSG (m + 1)) (WSG (m + 1)) ℂ)
    (Klo Klo' : Matrix (WSG m) (WSG m) ℂ)
    (hdiag1Hi : ∀ x, (sgGlue (m + 1)).g x → Khi x x = 2)
    (hdiag2Hi : ∀ x, (sgGlue (m + 1)).g x → (Khi ^ 2) x x = 6)
    (hdiag1Hi' : ∀ x, (sgGlue (m + 1)).g x → Khi' x x = 2)
    (hdiag2Hi' : ∀ x, (sgGlue (m + 1)).g x → (Khi' ^ 2) x x = 6)
    (hdiag1Lo : ∀ x, (sgGlue m).g x → Klo x x = 2)
    (hdiag2Lo : ∀ x, (sgGlue m).g x → (Klo ^ 2) x x = 6)
    (hdiag1Lo' : ∀ x, (sgGlue m).g x → Klo' x x = 2)
    (hdiag2Lo' : ∀ x, (sgGlue m).g x → (Klo' ^ 2) x x = 6)
    (h4 : ∀ w, (sgGlue (m + 1)).g w →
      (Khi ^ 4) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
        (Klo ^ 4)
          (sgK_root_pullback m ((sgGlue (m + 1)).σ w))
          (sgK_root_pullback m ((sgGlue (m + 1)).σ w)))
    (h5 : ∀ w, (sgGlue (m + 1)).g w →
      (Khi ^ 5) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
        (Klo ^ 5)
          (sgK_root_pullback m ((sgGlue (m + 1)).σ w))
          (sgK_root_pullback m ((sgGlue (m + 1)).σ w)))
    (h4' : ∀ w, (sgGlue (m + 1)).g w →
      (Khi' ^ 4) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
        (Klo' ^ 4)
          (sgK_root_pullback m ((sgGlue (m + 1)).σ w))
          (sgK_root_pullback m ((sgGlue (m + 1)).σ w)))
    (h5' : ∀ w, (sgGlue (m + 1)).g w →
      (Khi' ^ 5) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
        (Klo' ^ 5)
          (sgK_root_pullback m ((sgGlue (m + 1)).σ w))
          (sgK_root_pullback m ((sgGlue (m + 1)).σ w))) :
    glueRHS6_highPowerResidual (m + 1) Khi Khi' =
      glueRHS6_highPowerResidual m Klo Klo' := by
  classical
  have hReduceHi :=
    glueRHS6_highPowerResidual_diagonal_reduce (m + 1) Khi Khi'
      hdiag1Hi hdiag2Hi hdiag1Hi' hdiag2Hi'
  have hReduceLo :=
    glueRHS6_highPowerResidual_diagonal_reduce m Klo Klo'
      hdiag1Lo hdiag2Lo hdiag1Lo' hdiag2Lo'
  rw [hReduceHi, hReduceLo]
  have hSum4 := glueRHS6_glued_partner_power_sum_transport m 4 Khi Klo h4
  have hSum5 := glueRHS6_glued_partner_power_sum_transport m 5 Khi Klo h5
  have hSum4' := glueRHS6_glued_partner_power_sum_transport m 4 Khi' Klo' h4'
  have hSum5' := glueRHS6_glued_partner_power_sum_transport m 5 Khi' Klo' h5'
  rw [hSum5, hSum5', hSum4, hSum4']


/-- Concrete adjacent-level stability of the sixth-moment high-power
boundary residual for the tilde orientation. The six local endpoint lemmas
supply the required fourth/fifth diagonal transport. -/
theorem glueRHS6_highPowerResidual_sgK_til_succ
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    glueRHS6_highPowerResidual (m + 1)
        (sgK (m + 1) θ faceAxis (oTil (m + 2)))
        (sgK (m + 1) θ (fun _ => 2) (oTil (m + 2))) =
      glueRHS6_highPowerResidual m
        (sgK m θ faceAxis (oTil (m + 1)))
        (sgK m θ (fun _ => 2) (oTil (m + 1))) := by
  have hantiHi : OAnti (m + 2) (oTil (m + 2)) := oTil_anti (m + 2)
  have hantiLo : OAnti (m + 1) (oTil (m + 1)) := oTil_anti (m + 1)
  apply glueRHS6_highPowerResidual_eq_of_corner_power_transport m
  · intro x hx
    rw [sgK_diag (m + 1) θ faceAxis (oTil (m + 2)) x,
      pdeg_glued_state_eq_two (m + 1) hx]
    norm_num
  · intro x hx
    rw [pow_two, sgK_sq_diag (m + 1) θ faceAxis (oTil (m + 2)) hantiHi x,
      pdeg_glued_state_eq_two (m + 1) hx]
    norm_num
  · intro x hx
    rw [sgK_diag (m + 1) θ (fun _ => 2) (oTil (m + 2)) x,
      pdeg_glued_state_eq_two (m + 1) hx]
    norm_num
  · intro x hx
    rw [pow_two, sgK_sq_diag (m + 1) θ (fun _ => 2) (oTil (m + 2)) hantiHi x,
      pdeg_glued_state_eq_two (m + 1) hx]
    norm_num
  · intro x hx
    rw [sgK_diag m θ faceAxis (oTil (m + 1)) x,
      pdeg_glued_state_eq_two m hx]
    norm_num
  · intro x hx
    rw [pow_two, sgK_sq_diag m θ faceAxis (oTil (m + 1)) hantiLo x,
      pdeg_glued_state_eq_two m hx]
    norm_num
  · intro x hx
    rw [sgK_diag m θ (fun _ => 2) (oTil (m + 1)) x,
      pdeg_glued_state_eq_two m hx]
    norm_num
  · intro x hx
    rw [pow_two, sgK_sq_diag m θ (fun _ => 2) (oTil (m + 1)) hantiLo x,
      pdeg_glued_state_eq_two m hx]
    norm_num
  · intro w hw
    exact (sgK_glued_partner_diag_four_five_transport m hm θ faceAxis
      (faceAxis_pow1 m (by omega)) (faceAxis_pow2 m (by omega)) hw).1
  · intro w hw
    exact (sgK_glued_partner_diag_four_five_transport m hm θ faceAxis
      (faceAxis_pow1 m (by omega)) (faceAxis_pow2 m (by omega)) hw).2
  · intro w hw
    exact (sgK_glued_partner_diag_four_five_transport m hm θ (fun _ => 2)
      (fun _ => rfl) (fun _ => rfl) hw).1
  · intro w hw
    exact (sgK_glued_partner_diag_four_five_transport m hm θ (fun _ => 2)
      (fun _ => rfl) (fun _ => rfl) hw).2


/-- The concrete tilde-oriented sixth-moment high-power residual is equal
at every level m ≥ 3 to its level-three value. -/
theorem glueRHS6_highPowerResidual_sgK_til_eq_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    glueRHS6_highPowerResidual m
        (sgK m θ faceAxis (oTil (m + 1)))
        (sgK m θ (fun _ => 2) (oTil (m + 1))) =
      glueRHS6_highPowerResidual 3
        (sgK 3 θ faceAxis (oTil 4))
        (sgK 3 θ (fun _ => 2) (oTil 4)) := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [glueRHS6_highPowerResidual_sgK_til_succ n hn θ, ih]

/-- The same residual with numbering orientation reduces to the identical
level-three tilde residual, using the established num/til equivalence. -/
theorem glueRHS6_highPowerResidual_sgK_num_eq_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    glueRHS6_highPowerResidual m
        (sgK m θ faceAxis (oNum (m + 1)))
        (sgK m θ (fun _ => 2) (oNum (m + 1))) =
      glueRHS6_highPowerResidual 3
        (sgK 3 θ faceAxis (oTil 4))
        (sgK 3 θ (fun _ => 2) (oTil 4)) := by
  rw [glueRHS6_highPowerResidual_num_eq_til m hm θ faceAxis (fun _ => 2)]
  exact glueRHS6_highPowerResidual_sgK_til_eq_level3 m hm θ

/-- The numbering-orientation sixth-moment recurrence now has a fixed
level-three boundary term. This does not assert that the boundary term
vanishes; it proves that it is independent of m. -/
theorem defectO6_succ_num_level3_constant_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    defectO6 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      3 * defectO6 m θ faceAxis (fun _ => 2) (oNum m) -
        (defectO6 3 θ faceAxis (fun _ => 2) (oNum 3) -
          defectO6 3 θ faceAxis (fun _ => 2) (oTil 3)) +
        glueRHS6_highPowerResidual 3
          (sgK 3 θ faceAxis (oTil 4))
          (sgK 3 θ (fun _ => 2) (oTil 4)) := by
  rw [defectO6_succ_num_level3 m hm θ]
  rw [glueRHS6_sgK_axis_residual_of_diag123 m hm θ faceAxis (fun _ => 2)
    (oNum (m + 1)) (oNum_anti (m + 1))]
  rw [glueRHS6_highPowerResidual_sgK_num_eq_level3 m hm θ]


/-- Exact closed form of the numbering-orientation sixth-moment defect.
The only level-independent term is the explicit level-three boundary
residual; this theorem does not assume that residual or the base gap vanishes. -/
theorem defectO6_num_closed_form
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    defectO6 m θ faceAxis (fun _ => 2) (oNum m) =
      (3 : ℂ) ^ (m - 3) *
        (defectO6 3 θ faceAxis (fun _ => 2) (oNum 3) +
          (glueRHS6_highPowerResidual 3
              (sgK 3 θ faceAxis (oTil 4))
              (sgK 3 θ (fun _ => 2) (oTil 4)) -
            (defectO6 3 θ faceAxis (fun _ => 2) (oNum 3) -
              defectO6 3 θ faceAxis (fun _ => 2) (oTil 3))) / 2) -
        (glueRHS6_highPowerResidual 3
            (sgK 3 θ faceAxis (oTil 4))
            (sgK 3 θ (fun _ => 2) (oTil 4)) -
          (defectO6 3 θ faceAxis (fun _ => 2) (oNum 3) -
            defectO6 3 θ faceAxis (fun _ => 2) (oTil 3))) / 2 := by
  let D : ℕ → ℂ :=
    fun k => defectO6 k θ faceAxis (fun _ => 2) (oNum k)
  let R3 : ℂ :=
    glueRHS6_highPowerResidual 3
      (sgK 3 θ faceAxis (oTil 4))
      (sgK 3 θ (fun _ => 2) (oTil 4))
  let G3 : ℂ :=
    defectO6 3 θ faceAxis (fun _ => 2) (oNum 3) -
      defectO6 3 θ faceAxis (fun _ => 2) (oTil 3)
  let C3 : ℂ := R3 - G3
  have hrec : ∀ n, D (n + 4) = 3 * D (n + 3) + C3 := by
    intro n
    have hstep :=
      defectO6_succ_num_level3_constant_boundary (n + 3) (by omega) θ
    have hidx : n + 3 + 1 = n + 4 := by omega
    rw [hidx] at hstep
    calc
      D (n + 4) = 3 * D (n + 3) - G3 + R3 := by
        simpa [D, G3, R3] using hstep
      _ = 3 * D (n + 3) + C3 := by
        dsimp [C3]
        ring
  have hclosed := affine_three_recurrence D C3 hrec (m - 3)
  rw [Nat.sub_add_cancel hm] at hclosed
  simpa [D, C3, R3, G3] using hclosed


/-- The exact level-independent residual constant in the sixth-moment
recurrence. It is defined by finite level-three data, with no vanishing
assumption on either the boundary residual or the orientation gap. -/
noncomputable def defectO6_num_residual_constant (θ : ℝ) : ℂ :=
  glueRHS6_highPowerResidual 3
      (sgK 3 θ faceAxis (oTil 4))
      (sgK 3 θ (fun _ => 2) (oTil 4)) -
    (defectO6 3 θ faceAxis (fun _ => 2) (oNum 3) -
      defectO6 3 θ faceAxis (fun _ => 2) (oTil 3))

/-- Coefficient of the geometric growth term for the sixth-moment defect. -/
noncomputable def defectO6_num_growth_coefficient (θ : ℝ) : ℂ :=
  defectO6 3 θ faceAxis (fun _ => 2) (oNum 3) +
    defectO6_num_residual_constant θ / 2

/-- Constant offset in the all-level affine growth law for the sixth moment. -/
noncomputable def defectO6_num_growth_offset (θ : ℝ) : ℂ :=
  - defectO6_num_residual_constant θ / 2

/-- The sixth-moment numbering defect is exactly affine in 3^(m-3), for every
m ≥ 3 and every angle. Both coefficients are explicit finite level-three
quantities, and their definition is independent of m. -/
theorem defectO6_num_affine_growth
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    defectO6 m θ faceAxis (fun _ => 2) (oNum m) =
      (3 : ℂ) ^ (m - 3) * defectO6_num_growth_coefficient θ +
        defectO6_num_growth_offset θ := by
  rw [defectO6_num_closed_form m hm θ]
  simp [defectO6_num_growth_coefficient,
    defectO6_num_growth_offset, defectO6_num_residual_constant]
  ring

/-- Exact all-angle H6 recurrence after the proved high-power boundary
stabilization, valid for `m ≥ 3`. The constant is defined from finite
level-three data; this does not claim the `m = 2` to `m = 3` transition or
an elementary trigonometric simplification of `C₆`. -/
theorem defectO6_num_growth_recurrence
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    defectO6 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      3 * defectO6 m θ faceAxis (fun _ => 2) (oNum m) +
        defectO6_num_residual_constant θ := by
  rw [defectO6_succ_num_level3_constant_boundary m hm θ]
  simp [defectO6_num_residual_constant]
  ring


/-- A-copy entries in the O radius-three box transport by the O/A
numbering bridge; no copy shift or periodicity hypothesis is needed. -/
private theorem sgK_A_O_entry_next_til_radius_three
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 3) (hpy : p.2 ≤ 3)
    (hqx : q.1 ≤ 3) (hqy : q.2 ≤ 3) (i j : C2) :
    sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.A, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.A, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.A, ((⟨p, List.mem_toFinset.mpr
          (corner_O_radius_three_transport m hm hp hpx hpy).1⟩ : Pt m), i))
        (GCopy.A, ((⟨q, List.mem_toFinset.mpr
          (corner_O_radius_three_transport m hm hq hqx hqy).1⟩ : Pt m), j)) := by
  change pHeO (m + 1) θ ax (oTil (m + 2)) p q i j =
    pHeO m θ ax (oTil (m + 1)) p q i j
  calc
    _ = pHeO (m + 1) θ ax (oNum (m + 2)) p q i j :=
      pHeO_til_eq_num_of_level_domain (m + 1) (by omega) θ ax p q i j
    _ = pHeO m θ ax (oNum (m + 1)) p q i j :=
      pHeO_corner_O_radius_three_entry_next_num m hm θ ax
        hp hq hpx hpy hqx hqy i j
    _ = pHeO m θ ax (oTil (m + 1)) p q i j :=
      (pHeO_til_eq_num_of_level_domain m (by omega) θ ax p q i j).symm

/-- Common O radius-three entry transport for all copy labels. -/
private theorem sgK_O_entry_next_til_radius_three
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis) (c : GCopy)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : p.1 ≤ 3) (hpy : p.2 ≤ 3)
    (hqx : q.1 ≤ 3) (hqy : q.2 ≤ 3) (i j : C2) :
    sgK (m + 1) θ ax (oTil (m + 2))
        (c, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (c, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (c, ((⟨p, List.mem_toFinset.mpr
          (corner_O_radius_three_transport m hm hp hpx hpy).1⟩ : Pt m), i))
        (c, ((⟨q, List.mem_toFinset.mpr
          (corner_O_radius_three_transport m hm hq hqx hqy).1⟩ : Pt m), j)) := by
  cases c with
  | A => exact sgK_A_O_entry_next_til_radius_three m hm θ ax hp hq hpx hpy hqx hqy i j
  | B => exact sgK_B_O_entry_next_til_radius_three m hm θ ax hp hq hpx hpy hqx hqy i j
  | C => exact sgK_C_O_entry_next_til_radius_three m hm θ ax hp hq hpx hpy hqx hqy i j


/-- The O-corner radius-three neighborhood transports the diagonal entries
of powers six and seven between adjacent levels. The support equivalence
retains copy, point, and spin; the local entry bridge dispatches over all
three copy labels. -/
private theorem sgK_O_diag_six_seven_transport
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    {w : WSG (m + 1)}
    (hwPoint : w.2.1.1 = ((0, 0) : Point)) :
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 6) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 6)
        (sgK_root_pullback m w) (sgK_root_pullback m w) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ 7) w w =
      (sgK m θ ax (oTil (m + 1)) ^ 7)
        (sgK_root_pullback m w) (sgK_root_pullback m w) := by
  classical
  let S : Finset (WSG (m + 1)) := sgK_radius_three_support (m + 1) w
  let T : Finset (WSG m) := sgK_radius_three_O_parent_support m w.1
  let e := sgK_radius_three_support_O_equiv m hm (w := w) hwPoint
  let x' : WSG m := sgK_root_pullback m w

  have hwS : w ∈ S := by
    simp [S, sgK_radius_three_support, hwPoint]

  have hpull : x'.2.1.1 = ((0, 0) : Point) := by
    change (sgK_root_pullback_pt m w.2.1).1 = ((0, 0) : Point)
    exact sgK_root_pullback_pt_O m hwPoint
  have hrootX : x'.2.1.1.1 = 0 := by
    have h := congrArg Prod.fst hpull
    simpa using h
  have hrootY : x'.2.1.1.2 = 0 := by
    have h := congrArg Prod.snd hpull
    simpa using h

  have hwT : x' ∈ T := by
    simp only [T, sgK_radius_three_O_parent_support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hrootX]
      norm_num
    · rw [hrootY]
      norm_num

  have hroot : e ⟨w, hwS⟩ = ⟨x', hwT⟩ := by
    apply Subtype.ext
    change (sgK_radius_three_support_O_equiv m hm (w := w) hwPoint
      ⟨w, hwS⟩).1 = sgK_root_pullback m w
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Subtype.ext
        exact hwPoint.trans hpull.symm
      · rfl

  have hEntry : ∀ a b : {z : WSG (m + 1) // z ∈ S},
      sgK (m + 1) θ ax (oTil (m + 2)) a.1 b.1 =
        sgK m θ ax (oTil (m + 1)) (e a).1 (e b).1 := by
    intro a b
    have haS : a.1 ∈ sgK_radius_three_support (m + 1) w := by
      simpa [S] using a.2
    have hbS : b.1 ∈ sgK_radius_three_support (m + 1) w := by
      simpa [S] using b.2
    have haBox := (sgK_radius_three_support_O_box_iff m hm hwPoint).mp haS
    have hbBox := (sgK_radius_three_support_O_box_iff m hm hwPoint).mp hbS
    have haCopy : a.1.1 = w.1 := haBox.1
    have hbCopy : b.1.1 = w.1 := hbBox.1
    have haX : a.1.2.1.1.1 ≤ 3 := haBox.2.2.1
    have haY : a.1.2.1.1.2 ≤ 3 := haBox.2.2.2
    have hbX : b.1.2.1.1.1 ≤ 3 := hbBox.2.2.1
    have hbY : b.1.2.1.1.2 ≤ 3 := hbBox.2.2.2

    have hpa := corner_O_radius_three_transport m hm
      (List.mem_toFinset.mp a.1.2.1.2) haX haY
    have hpb := corner_O_radius_three_transport m hm
      (List.mem_toFinset.mp b.1.2.1.2) hbX hbY
    have hbridge := sgK_O_entry_next_til_radius_three m hm θ ax w.1
      (List.mem_toFinset.mp a.1.2.1.2)
      (List.mem_toFinset.mp b.1.2.1.2)
      haX haY hbX hbY a.1.2.2 b.1.2.2

    have haPt :
        (⟨a.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp a.1.2.1.2)⟩ : Pt (m + 1)) = a.1.2.1 := by
      apply Subtype.ext
      rfl
    have hbPt :
        (⟨b.1.2.1.1, List.mem_toFinset.mpr
          (List.mem_toFinset.mp b.1.2.1.2)⟩ : Pt (m + 1)) = b.1.2.1 := by
      apply Subtype.ext
      rfl
    have haState : a.1 = (w.1, a.1.2) := Prod.ext haCopy rfl
    have hbState : b.1 = (w.1, b.1.2) := Prod.ext hbCopy rfl
    have haMap :
        (e a).1 =
          (w.1,
            ((⟨a.1.2.1.1, List.mem_toFinset.mpr hpa.1⟩ : Pt m),
              a.1.2.2)) := by
      apply Prod.ext
      · exact haCopy
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl
    have hbMap :
        (e b).1 =
          (w.1,
            ((⟨b.1.2.1.1, List.mem_toFinset.mpr hpb.1⟩ : Pt m),
              b.1.2.2)) := by
      apply Prod.ext
      · exact hbCopy
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl
    rw [haState, hbState]
    rw [haPt, hbPt] at hbridge
    rw [haMap, hbMap]
    exact hbridge

  have hnotS : ∀ z, z ∉ T → z ∉ sgK_radius_three_support m x' := by
    intro z hzT hz
    have hzs := hz
    simp only [sgK_radius_three_support, Finset.mem_filter,
      Finset.mem_univ, true_and] at hzs
    have hzParent : z ∈ T := by
      simp only [T, sgK_radius_three_O_parent_support, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · have hxCopy : x'.1 = w.1 := by
          rfl
        exact hzs.1.trans hxCopy
      · have hbound := hzs.2.2.1
        simpa [hrootX] using hbound
      · have hbound := hzs.2.2.2.2
        simpa [hrootY] using hbound
    exact hzT hzParent

  have hRowOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) w z = 0 := by
    intro z hz
    have hzero := sgK_pow_entry_zero_outside_radius_three
      (m + 1) θ ax (oTil (m + 2)) 1 (by norm_num) w z
      (by simpa [S] using hz)
    simpa [pow_one] using hzero
  have hColOne : ∀ z, z ∉ S →
      sgK (m + 1) θ ax (oTil (m + 2)) z w = 0 := by
    intro z hz
    have hzero := sgK_pow_entry_zero_outside_radius_three_col
      (m + 1) θ ax (oTil (m + 2)) 1 (by norm_num) w z
      (by simpa [S] using hz)
    simpa [pow_one] using hzero
  have hRowTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) w z = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three
      (m + 1) θ ax (oTil (m + 2)) 2 (by norm_num) w z
      (by simpa [S] using hz)
  have hColTwo : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 2) z w = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three_col
      (m + 1) θ ax (oTil (m + 2)) 2 (by norm_num) w z
      (by simpa [S] using hz)
  have hRowThree : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 3) w z = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three
      (m + 1) θ ax (oTil (m + 2)) 3 (by norm_num) w z
      (by simpa [S] using hz)
  have hColThree : ∀ z, z ∉ S →
      (sgK (m + 1) θ ax (oTil (m + 2)) ^ 3) z w = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three_col
      (m + 1) θ ax (oTil (m + 2)) 3 (by norm_num) w z
      (by simpa [S] using hz)

  have hRowOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) x' z = 0 := by
    intro z hz
    have hzero := sgK_pow_entry_zero_outside_radius_three
      m θ ax (oTil (m + 1)) 1 (by norm_num) x' z (hnotS z hz)
    simpa [pow_one] using hzero
  have hColOne' : ∀ z, z ∉ T →
      sgK m θ ax (oTil (m + 1)) z x' = 0 := by
    intro z hz
    have hzero := sgK_pow_entry_zero_outside_radius_three_col
      m θ ax (oTil (m + 1)) 1 (by norm_num) x' z (hnotS z hz)
    simpa [pow_one] using hzero
  have hRowTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) x' z = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three
      m θ ax (oTil (m + 1)) 2 (by norm_num) x' z (hnotS z hz)
  have hColTwo' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 2) z x' = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three_col
      m θ ax (oTil (m + 1)) 2 (by norm_num) x' z (hnotS z hz)
  have hRowThree' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 3) x' z = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three
      m θ ax (oTil (m + 1)) 3 (by norm_num) x' z (hnotS z hz)
  have hColThree' : ∀ z, z ∉ T →
      (sgK m θ ax (oTil (m + 1)) ^ 3) z x' = 0 := by
    intro z hz
    exact sgK_pow_entry_zero_outside_radius_three_col
      m θ ax (oTil (m + 1)) 3 (by norm_num) x' z (hnotS z hz)

  exact matrix_pow_six_seven_diag_eq_of_local_equiv
    (sgK (m + 1) θ ax (oTil (m + 2)))
    (sgK m θ ax (oTil (m + 1)))
    S T e w x' hwS hwT hroot hEntry
    hRowOne hColOne hRowTwo hColTwo hRowThree hColThree
    hRowOne' hColOne' hRowTwo' hColTwo' hRowThree' hColThree'


/-- Spin-resolved radius-three transport at the X corner. The B-shift
pullback avoids both B-copy glued endpoints by the geometric radius-three
transport lemma. The orientation conversion is kept explicit: the high
tilde orientation is reduced to numbering, the B-local entry is transported,
and the parent B orientation is converted back to the parent tilde graph. -/
theorem pHeO_corner_X_radius_three_box_entry_next_til
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : 2 ^ (m + 1) ≤ p.1 + 3) (hpy : p.2 ≤ 3)
    (hqx : 2 ^ (m + 1) ≤ q.1 + 3) (hqy : q.2 ≤ 3)
    (i j : C2) :
    ∃ p' q' : Point,
      p' ∈ vertexOrder m ∧ q' ∈ vertexOrder m ∧
      p = shiftPoint (2 ^ m) 1 0 p' ∧
      q = shiftPoint (2 ^ m) 1 0 q' ∧
      pHeO (m + 1) θ ax (oTil (m + 2)) p q i j =
        pHeO m θ ax (oTil (m + 1)) p' q' i j := by
  rcases corner_X_radius_three_transport m hm hp hpx hpy with
    ⟨p', hp', rfl, hp0, hpY⟩
  rcases corner_X_radius_three_transport m hm hq hqx hqy with
    ⟨q', hq', rfl, _, _⟩
  have hhighOrient :
      ∀ a b : Point, a ≠ b →
        EdgeB (m + 1) a.1 a.2 b.1 b.2 = true →
        (if a ≤ b then (a, b) else (b, a)) ∈ fluxEdges (m + 1) →
        (oTil (m + 2) a b ↔ oNum (m + 2) a b) := by
    intro a b hab hE hfl
    have hmEdge := EdgeB_mem (m + 1) a.1 a.2 b.1 b.2 hE
    have ha : a ∈ vertexOrder (m + 1) :=
      (mem_vertexOrder_iff (m + 1) a).mpr hmEdge.1
    have hb : b ∈ vertexOrder (m + 1) :=
      (mem_vertexOrder_iff (m + 1) b).mpr hmEdge.2
    obtain ⟨h1, h2⟩ := cp1_not_A (m + 1) (by omega) ha hb
    exact oTil_of_no_corner h1 h2
  have hhigh := pHeO_orient_congr (m + 1) θ ax
    (oTil (m + 2)) (oNum (m + 2)) hhighOrient
  have hmiddleOrient :
      ∀ a b : Point, a ≠ b →
        EdgeB m a.1 a.2 b.1 b.2 = true →
        (if a ≤ b then (a, b) else (b, a)) ∈ fluxEdges m →
        (oBo m (oNum (m + 2)) a b ↔
          oBo m (oNum (m + 1)) a b) := by
    intro a b hab hE hfl
    have hmEdge := EdgeB_mem m a.1 a.2 b.1 b.2 hE
    have ha : a ∈ vertexOrder m :=
      (mem_vertexOrder_iff m a).mpr hmEdge.1
    have hb : b ∈ vertexOrder m :=
      (mem_vertexOrder_iff m b).mpr hmEdge.2
    have haB : shiftPoint (2 ^ m) 1 0 a ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inr (Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩))
    have hbB : shiftPoint (2 ^ m) 1 0 b ∈ vertexOrder (m + 1) := by
      rw [mem_vertexOrder_succ_iff]
      exact Or.inr (Or.inl (List.mem_map.mpr ⟨b, hb, rfl⟩))
    unfold oBo
    exact oNum_succ_restrict m haB hbB
  have hparentOrient :
      ∀ a b : Point, a ≠ b →
        EdgeB m a.1 a.2 b.1 b.2 = true →
        (if a ≤ b then (a, b) else (b, a)) ∈ fluxEdges m →
        (oBo m (oNum (m + 1)) a b ↔ oTil (m + 1) a b) := by
    intro a b hab hE hfl
    have hmEdge := EdgeB_mem m a.1 a.2 b.1 b.2 hE
    have ha : a ∈ vertexOrder m :=
      (mem_vertexOrder_iff m a).mpr hmEdge.1
    have hb : b ∈ vertexOrder m :=
      (mem_vertexOrder_iff m b).mpr hmEdge.2
    have hbo : oBo m (oNum (m + 1)) a b ↔ oNum m a b :=
      oBo_num_iff_oNum m ha hb
    have hnum : oNum m a b ↔ oNum (m + 1) a b := by
      unfold oNum
      rw [vIdx_succ_of_mem ha, vIdx_succ_of_mem hb]
    obtain ⟨h1, h2⟩ := cp1_not_A m (by omega) ha hb
    calc
      oBo m (oNum (m + 1)) a b ↔ oNum m a b := hbo
      _ ↔ oNum (m + 1) a b := hnum
      _ ↔ oTil (m + 1) a b := (oTil_of_no_corner h1 h2).symm
  have hlocal :
      pHeO (m + 1) θ ax (oNum (m + 2))
          (shiftPoint (2 ^ m) 1 0 p') (shiftPoint (2 ^ m) 1 0 q') i j =
        pHeO m θ ax (oBo m (oNum (m + 2))) p' q' i j :=
    pHeO_succ_B_local_entry m θ ax (oNum (m + 2)) hax
      hp' hq' hp0 hpY i j
  refine ⟨p', q', hp', hq', rfl, rfl, ?_⟩
  calc
    pHeO (m + 1) θ ax (oTil (m + 2))
        (shiftPoint (2 ^ m) 1 0 p') (shiftPoint (2 ^ m) 1 0 q') i j =
      pHeO (m + 1) θ ax (oNum (m + 2))
        (shiftPoint (2 ^ m) 1 0 p') (shiftPoint (2 ^ m) 1 0 q') i j :=
      hhigh _ _ i j
    _ = pHeO m θ ax (oBo m (oNum (m + 2))) p' q' i j := hlocal
    _ = pHeO m θ ax (oBo m (oNum (m + 1))) p' q' i j :=
      pHeO_orient_congr m θ ax
        (oBo m (oNum (m + 2))) (oBo m (oNum (m + 1)))
        hmiddleOrient p' q' i j
    _ = pHeO m θ ax (oTil (m + 1)) p' q' i j :=
      pHeO_orient_congr m θ ax
        (oBo m (oNum (m + 1))) (oTil (m + 1))
        hparentOrient p' q' i j


/-- The same X radius-three local entry transport, but with the parent
tilde orientations required after converting both matrix entries from
copy C to the underlying point operator. In contrast to the A-block
transport above, this is oTil (m+1) on the high level and oTil m on
the parent level. -/
theorem pHeO_corner_X_radius_three_box_entry_next_parent_til
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : 2 ^ (m + 1) ≤ p.1 + 3) (hpy : p.2 ≤ 3)
    (hqx : 2 ^ (m + 1) ≤ q.1 + 3) (hqy : q.2 ≤ 3)
    (i j : C2) :
    ∃ p' q' : Point,
      p' ∈ vertexOrder m ∧ q' ∈ vertexOrder m ∧
      p = shiftPoint (2 ^ m) 1 0 p' ∧
      q = shiftPoint (2 ^ m) 1 0 q' ∧
      pHeO (m + 1) θ ax (oTil (m + 1)) p q i j =
        pHeO m θ ax (oTil m) p' q' i j := by
  rcases (corner_X_radius_three_box_iff m hm hp).mp ⟨hpx, hpy⟩ with
    ⟨p', hp', hpx', _, rfl⟩
  rcases (corner_X_radius_three_box_iff m hm hq).mp ⟨hqx, hqy⟩ with
    ⟨q', hq', _, _, rfl⟩
  have hpow : 3 < 2 ^ m := by
    calc
      3 < 2 ^ 4 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hp0 : p' ≠ (0, 0) := by
    intro heq
    have hcoord : p'.1 = 0 := congrArg Prod.fst heq
    omega
  have hpY : p' ≠ (0, 2 ^ m) := by
    intro heq
    have hcoord : p'.1 = 0 := congrArg Prod.fst heq
    omega
  refine ⟨p', q', hp', hq', rfl, rfl, ?_⟩
  calc
    pHeO (m + 1) θ ax (oTil (m + 1))
        (shiftPoint (2 ^ m) 1 0 p') (shiftPoint (2 ^ m) 1 0 q') i j =
      pHeO m θ ax (oBo m (oTil (m + 1))) p' q' i j :=
        pHeO_succ_B_local_entry m θ ax (oTil (m + 1)) hax
          hp' hq' hp0 hpY i j
    _ = pHeO m θ ax (oTil m) p' q' i j := by
      apply pHeO_orient_congr m θ ax
        (oBo m (oTil (m + 1))) (oTil m)
      intro a b hab hE hfl
      have hmEdge := EdgeB_mem m a.1 a.2 b.1 b.2 hE
      have ha : a ∈ vertexOrder m :=
        (mem_vertexOrder_iff m a).mpr hmEdge.1
      have hb : b ∈ vertexOrder m :=
        (mem_vertexOrder_iff m b).mpr hmEdge.2
      have fl : ∀ a b : Point, (a, b) ∈ fluxEdges m →
          ∃ f ∈ facesExact m, f.1 = a ∧ f.2.1 = b := by
        intro a b hab
        obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hab
        have hle := flux_edge_order m f hf
        have h' : fluxEdge f = (f.1, f.2.1) := by
          simp [fluxEdge, hle]
        rw [h'] at hfe
        exact ⟨f, hf, (Prod.mk.inj hfe).1, (Prod.mk.inj hfe).2⟩
      have hanti : OAnti m (oBo m (oTil (m + 1))) :=
        oanti_B m _ (oTil_anti (m + 1))
      by_cases hle : a ≤ b
      · rw [if_pos hle] at hfl
        obtain ⟨f, hf, h1, h2⟩ := fl a b hfl
        rw [← h1, ← h2]
        obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
        obtain ⟨k1, k2⟩ := cp1_shiftB m hs1
        show oTil (m + 1) (shiftPoint (2 ^ m) 1 0 f.1)
            (shiftPoint (2 ^ m) 1 0 f.2.1) ↔ oTil m f.1 f.2.1
        exact oTil_transport (faceB m f hf) k1 k2
      · rw [if_neg hle] at hfl
        obtain ⟨f, hf, h1, h2⟩ := fl b a hfl
        have h3 : oBo m (oTil (m + 1)) f.1 f.2.1 ↔
            oTil m f.1 f.2.1 := by
          obtain ⟨hs1, hs2⟩ := flux_edge_shape m f hf
          obtain ⟨k1, k2⟩ := cp1_shiftB m hs1
          show oTil (m + 1) (shiftPoint (2 ^ m) 1 0 f.1)
              (shiftPoint (2 ^ m) 1 0 f.2.1) ↔ oTil m f.1 f.2.1
          exact oTil_transport (faceB m f hf) k1 k2
        rw [h1, h2] at h3
        have hanti' : OAnti m (oTil m) := oTil_anti m
        rw [hanti a b ha hb hab, hanti' a b ha hb hab]
        exact not_congr h3




/-- A-copy entries in the X radius-three box transport to their parent
B-shift representatives. This is the direct state-level bridge needed by
the X finite-support diagonal argument. -/
theorem sgK_A_X_entry_next_til_radius_three
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : 2 ^ (m + 1) ≤ p.1 + 3) (hpy : p.2 ≤ 3)
    (hqx : 2 ^ (m + 1) ≤ q.1 + 3) (hqy : q.2 ≤ 3)
    (i j : C2) :
    ∃ p' q' : Pt m,
      p = shiftPoint (2 ^ m) 1 0 p'.1 ∧
      q = shiftPoint (2 ^ m) 1 0 q'.1 ∧
      sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.A, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.A, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.A, (p', i))
        (GCopy.A, (q', j)) := by
  rcases pHeO_corner_X_radius_three_box_entry_next_til m hm θ ax hax
      hp hq hpx hpy hqx hqy i j with
    ⟨p0, q0, hp0, hq0, rfl, rfl, hentry⟩
  refine ⟨(⟨p0, List.mem_toFinset.mpr hp0⟩ : Pt m),
      (⟨q0, List.mem_toFinset.mpr hq0⟩ : Pt m), rfl, rfl, ?_⟩
  change pHeO (m + 1) θ ax (oTil (m + 2))
      (shiftPoint (2 ^ m) 1 0 p0) (shiftPoint (2 ^ m) 1 0 q0) i j =
    pHeO m θ ax (oTil (m + 1)) p0 q0 i j
  exact hentry


/-- C-copy entries in the X radius-three box transport to their parent
B-shift representatives. The C-orientation conversion remains explicit
and separate from the underlying B-shift point transport. -/
theorem sgK_C_X_entry_next_til_radius_three
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (hax : ∀ k, ax (3 ^ m + k) = ax k)
    {p q : Point}
    (hp : p ∈ vertexOrder (m + 1)) (hq : q ∈ vertexOrder (m + 1))
    (hpx : 2 ^ (m + 1) ≤ p.1 + 3) (hpy : p.2 ≤ 3)
    (hqx : 2 ^ (m + 1) ≤ q.1 + 3) (hqy : q.2 ≤ 3)
    (i j : C2) :
    ∃ p' q' : Pt m,
      p = shiftPoint (2 ^ m) 1 0 p'.1 ∧
      q = shiftPoint (2 ^ m) 1 0 q'.1 ∧
      sgK (m + 1) θ ax (oTil (m + 2))
        (GCopy.C, ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i))
        (GCopy.C, ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)) =
      sgK m θ ax (oTil (m + 1))
        (GCopy.C, (p', i))
        (GCopy.C, (q', j)) := by
  rcases pHeO_corner_X_radius_three_box_entry_next_parent_til m hm θ ax hax
      hp hq hpx hpy hqx hqy i j with
    ⟨p0, q0, hp0, hq0, hpEq, hqEq, hentry⟩
  have hHighOrient : ∀ a b : Point,
      oCo (m + 1) (oTil (m + 2)) a b ↔
        oCo (m + 1) (oNum (m + 2)) a b := by
    intro a b
    obtain ⟨h1, h2⟩ := cp1_shiftC (m + 1) (p := a) (q := b)
    change oTil (m + 2) (shiftPoint (2 ^ (m + 1)) 0 1 a)
        (shiftPoint (2 ^ (m + 1)) 0 1 b) ↔
      oNum (m + 2) (shiftPoint (2 ^ (m + 1)) 0 1 a)
        (shiftPoint (2 ^ (m + 1)) 0 1 b)
    exact oTil_of_no_corner h1 h2
  have hHighC :
      pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j =
        pHeO (m + 1) θ ax (oTil (m + 1)) p q i j := by
    have h := Hc_C_num_eq_parent_til (m + 1) (by omega) θ ax
      (oNum_anti (m + 2))
      ((⟨p, List.mem_toFinset.mpr hp⟩ : Pt (m + 1)), i)
      ((⟨q, List.mem_toFinset.mpr hq⟩ : Pt (m + 1)), j)
    change pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j =
      pHeO (m + 1) θ ax (oTil (m + 1)) p q i j at h
    exact h
  have hLowOrient : ∀ a b : Point,
      oCo m (oTil (m + 1)) a b ↔ oCo m (oNum (m + 1)) a b := by
    intro a b
    obtain ⟨h1, h2⟩ := cp1_shiftC m (p := a) (q := b)
    change oTil (m + 1) (shiftPoint (2 ^ m) 0 1 a)
        (shiftPoint (2 ^ m) 0 1 b) ↔
      oNum (m + 1) (shiftPoint (2 ^ m) 0 1 a)
        (shiftPoint (2 ^ m) 0 1 b)
    exact oTil_of_no_corner h1 h2
  have hLowC :
      pHeO m θ ax (oCo m (oNum (m + 1))) p0 q0 i j =
        pHeO m θ ax (oTil m) p0 q0 i j := by
    have h := Hc_C_num_eq_parent_til m (by omega) θ ax
      (oNum_anti (m + 1))
      ((⟨p0, List.mem_toFinset.mpr hp0⟩ : Pt m), i)
      ((⟨q0, List.mem_toFinset.mpr hq0⟩ : Pt m), j)
    change pHeO m θ ax (oCo m (oNum (m + 1))) p0 q0 i j =
      pHeO m θ ax (oTil m) p0 q0 i j at h
    exact h
  refine ⟨(⟨p0, List.mem_toFinset.mpr hp0⟩ : Pt m),
      (⟨q0, List.mem_toFinset.mpr hq0⟩ : Pt m), hpEq, hqEq, ?_⟩
  change pHeO (m + 1) θ ax (oCo (m + 1) (oTil (m + 2))) p q i j =
    pHeO m θ ax (oCo m (oTil (m + 1))) p0 q0 i j
  calc
    pHeO (m + 1) θ ax (oCo (m + 1) (oTil (m + 2))) p q i j =
        pHeO (m + 1) θ ax (oCo (m + 1) (oNum (m + 2))) p q i j :=
      pHeO_rel_congr_local (m + 1) θ ax
        (oCo (m + 1) (oTil (m + 2))) (oCo (m + 1) (oNum (m + 2)))
        p q i j (hHighOrient p q)
    _ = pHeO (m + 1) θ ax (oTil (m + 1)) p q i j := hHighC
    _ = pHeO m θ ax (oTil m) p0 q0 i j := hentry
    _ = pHeO m θ ax (oCo m (oNum (m + 1))) p0 q0 i j := hLowC.symm
    _ = pHeO m θ ax (oCo m (oTil (m + 1))) p0 q0 i j :=
      (pHeO_rel_congr_local m θ ax
        (oCo m (oTil (m + 1))) (oCo m (oNum (m + 1)))
        p0 q0 i j (hLowOrient p0 q0)).symm


end EvgenyTheorem
