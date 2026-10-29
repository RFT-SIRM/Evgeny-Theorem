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
