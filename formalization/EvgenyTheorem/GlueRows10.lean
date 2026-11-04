import EvgenyTheorem.FinalTilde

namespace EvgenyTheorem

/-- Zero rows from glued states to the flip endpoint, radius 8. -/
theorem sgK_pow_zero_from_glue_to_flip_up_to_eight
    (m n : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (w z : WSG m) (hw : (sgGlue m).g w)
    (hz : p6FlipEndpoint m z) (hn : n ≤ 8) :
    (sgK m θ ax o ^ n) w z = 0 := by
  classical
  by_cases hb : w.1 = GCopy.B
  · have hpB : w.2.1.1 = (0, 0) ∨ w.2.1.1 = (0, 2 ^ m) :=
      glued_B_point m hw hb
    have hpow : 16 ≤ 2 ^ m := by
      calc
        16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hside : 8 < 2 ^ m - 1 := by omega
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

/-- Glued rows of K^n agree under the corner flip for n ≤ 9. -/
theorem sgK_pow_row_eq_num_til_on_glue_up_to_nine
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (w : WSG m) (hw : (sgGlue m).g w) :
    ∀ n, n ≤ 9 → ∀ z,
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
      have hn8 : n ≤ 8 := by omega
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hflip : p6FlipEndpoint m y
      · have hnum := sgK_pow_zero_from_glue_to_flip_up_to_eight
          m n hm θ ax (oNum (m + 1)) w y hw hflip hn8
        have htil := sgK_pow_zero_from_glue_to_flip_up_to_eight
          m n hm θ ax (oTil (m + 1)) w y hw hflip hn8
        rw [hnum, htil]
        simp
      · have hn9 : n ≤ 9 := by omega
        rw [ih hn9 y, sgK_num_til_row_eq_away_flip m (by omega) θ ax y z hflip]

theorem glueRHS10_pair_product_transport
    (m : ℕ)
    (Khi : Matrix (WSG (m + 1)) (WSG (m + 1)) ℂ)
    (Klo : Matrix (WSG m) (WSG m) ℂ)
    (e : {w : WSG (m + 1) // (sgGlue (m + 1)).g w} ≃
      {w : WSG m // (sgGlue m).g w})
    (hpow : ∀ (w : WSG (m + 1)) (hw : (sgGlue (m + 1)).g w),
      ∀ n, n ≤ 9 →
        (Khi ^ n) w w =
          (Klo ^ n) (e ⟨w, hw⟩).1 (e ⟨w, hw⟩).1 ∧
        (Khi ^ n) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
          (Klo ^ n) ((sgGlue m).σ (e ⟨w, hw⟩).1)
            ((sgGlue m).σ (e ⟨w, hw⟩).1))
    {w : WSG (m + 1)} (hw : (sgGlue (m + 1)).g w)
    (ps : List (ℕ × ℕ))
    (hbound : ∀ p ∈ ps, p.1 ≤ 9 ∧ p.2 ≤ 9) :
    glueRHS8_pair_product (m + 1) Khi w ps =
      glueRHS8_pair_product m Klo (e ⟨w, hw⟩).1 ps := by
  classical
  revert hbound
  induction ps with
  | nil =>
      intro _
      rfl
  | cons p ps ih =>
      intro hbound
      have hp := hbound p (by simp)
      have htail : ∀ q ∈ ps, q.1 ≤ 9 ∧ q.2 ≤ 9 := by
        intro q hq
        exact hbound q (by simp [hq])
      have hvalue :
          glueRHS8_pair_value (m + 1) Khi w p =
            glueRHS8_pair_value m Klo (e ⟨w, hw⟩).1 p := by
        have hfirst := (hpow w hw p.1 hp.1).1
        have hsecond := (hpow w hw p.2 hp.2).2
        simp only [glueRHS8_pair_value, hfirst, hsecond]
      change
        glueRHS8_pair_value (m + 1) Khi w p *
            glueRHS8_pair_product (m + 1) Khi w ps =
          glueRHS8_pair_value m Klo (e ⟨w, hw⟩).1 p *
            glueRHS8_pair_product m Klo (e ⟨w, hw⟩).1 ps
      rw [hvalue, ih htail]

/-- A complete finite sum of H8 diagonal pair-products transports across
an equivalence of the glued-state subtypes. No terms outside the glued set
are introduced: the conditional sums are converted to subtype sums first. -/
theorem glueRHS10_pair_sum_transport
    (m : ℕ)
    (Khi : Matrix (WSG (m + 1)) (WSG (m + 1)) ℂ)
    (Klo : Matrix (WSG m) (WSG m) ℂ)
    (e : {w : WSG (m + 1) // (sgGlue (m + 1)).g w} ≃
      {w : WSG m // (sgGlue m).g w})
    (hpow : ∀ (w : WSG (m + 1)) (hw : (sgGlue (m + 1)).g w),
      ∀ n, n ≤ 9 →
        (Khi ^ n) w w =
          (Klo ^ n) (e ⟨w, hw⟩).1 (e ⟨w, hw⟩).1 ∧
        (Khi ^ n) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
          (Klo ^ n) ((sgGlue m).σ (e ⟨w, hw⟩).1)
            ((sgGlue m).σ (e ⟨w, hw⟩).1))
    (ps : List (ℕ × ℕ))
    (hbound : ∀ p ∈ ps, p.1 ≤ 9 ∧ p.2 ≤ 9) :
    glueRHS8_pair_sum (m + 1) Khi ps =
      glueRHS8_pair_sum m Klo ps := by
  classical
  unfold glueRHS8_pair_sum
  calc
    (∑ w, if (sgGlue (m + 1)).g w then
        glueRHS8_pair_product (m + 1) Khi w ps else 0) =
      ∑ w : {w : WSG (m + 1) // (sgGlue (m + 1)).g w},
        glueRHS8_pair_product (m + 1) Khi w.1 ps := by
          exact glueRHS8_sum_ite_eq_subtype
            (fun w : WSG (m + 1) => (sgGlue (m + 1)).g w)
            (fun w => glueRHS8_pair_product (m + 1) Khi w ps)
    _ = ∑ w : {w : WSG (m + 1) // (sgGlue (m + 1)).g w},
        glueRHS8_pair_product m Klo (e w).1 ps := by
          apply Finset.sum_congr rfl
          intro w hw
          exact glueRHS10_pair_product_transport m Khi Klo e hpow
            (w := w.1) w.2 ps hbound
    _ = ∑ w : {w : WSG m // (sgGlue m).g w},
        glueRHS8_pair_product m Klo w.1 ps := by
          exact Equiv.sum_comp e
            (fun w : {w : WSG m // (sgGlue m).g w} =>
              glueRHS8_pair_product m Klo w.1 ps)
    _ = ∑ w, if (sgGlue m).g w then
        glueRHS8_pair_product m Klo w ps else 0 := by
          exact (glueRHS8_sum_ite_eq_subtype
            (fun w : WSG m => (sgGlue m).g w)
            (fun w => glueRHS8_pair_product m Klo w ps)).symm

theorem glueRHS10_ten_eq_pair_sum
    (m : ℕ) (K : Matrix (WSG m) (WSG m) ℂ) :
    glueRHS10_ten_N_diagonal_form m K =
      glueRHS8_pair_sum m K [(1, 1), (1, 1), (1, 1), (1, 1), (1, 1)] := by
  unfold glueRHS10_ten_N_diagonal_form glueRHS8_pair_sum
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hg : (sgGlue m).g x
  · simp only [if_pos hg, glueRHS8_pair_product, glueRHS8_pair_value, pow_one]
    ring
  · simp only [if_neg hg]

/-- Adjacent-level transport of the complete H10 boundary correction. -/
theorem glueRHS10_adjacent_level_eq_of_diagonal_transport
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (oHi oLo : Point → Point → Prop)
    [DecidableRel oHi] [DecidableRel oLo]
    (e : {w : WSG (m + 1) // (sgGlue (m + 1)).g w} ≃
      {w : WSG m // (sgGlue m).g w})
    (hpow : ∀ (w : WSG (m + 1)) (hw : (sgGlue (m + 1)).g w),
      ∀ n, n ≤ 9 →
        (sgK (m + 1) θ ax oHi ^ n) w w =
          (sgK m θ ax oLo ^ n) (e ⟨w, hw⟩).1 (e ⟨w, hw⟩).1 ∧
        (sgK (m + 1) θ ax oHi ^ n) ((sgGlue (m + 1)).σ w)
            ((sgGlue (m + 1)).σ w) =
          (sgK m θ ax oLo ^ n)
            ((sgGlue m).σ (e ⟨w, hw⟩).1)
            ((sgGlue m).σ (e ⟨w, hw⟩).1)) :
    glueRHS10 (m + 1) (sgK (m + 1) θ ax oHi) =
      glueRHS10 m (sgK m θ ax oLo) := by
  unfold glueRHS10 glueRHS10_two_N_diagonal_form glueRHS10_four_N_diagonal_form
    glueRHS10_six_N_diagonal_form glueRHS10_eight_N_diagonal_form
    glueRHS10_three_pair_sum glueRHS10_four_pair_sum
  rw [glueRHS10_ten_eq_pair_sum, glueRHS10_ten_eq_pair_sum]
  have hsum (ps : List (ℕ × ℕ))
      (hbound : ∀ p ∈ ps, p.1 ≤ 9 ∧ p.2 ≤ 9) :=
    glueRHS10_pair_sum_transport m
      (sgK (m + 1) θ ax oHi) (sgK m θ ax oLo) e hpow ps hbound
  rw [
    hsum [(1,9)] (by norm_num),
    hsum [(2,8)] (by norm_num),
    hsum [(3,7)] (by norm_num),
    hsum [(4,6)] (by norm_num),
    hsum [(5,5)] (by norm_num),
    hsum [(1,1), (1,7)] (by norm_num),
    hsum [(1,1), (2,6)] (by norm_num),
    hsum [(1,1), (3,5)] (by norm_num),
    hsum [(1,1), (4,4)] (by norm_num),
    hsum [(1,1), (5,3)] (by norm_num),
    hsum [(1,1), (6,2)] (by norm_num),
    hsum [(1,2), (1,6)] (by norm_num),
    hsum [(1,2), (2,5)] (by norm_num),
    hsum [(1,2), (3,4)] (by norm_num),
    hsum [(1,2), (4,3)] (by norm_num),
    hsum [(1,2), (5,2)] (by norm_num),
    hsum [(1,3), (1,5)] (by norm_num),
    hsum [(1,3), (2,4)] (by norm_num),
    hsum [(1,3), (3,3)] (by norm_num),
    hsum [(1,3), (4,2)] (by norm_num),
    hsum [(1,4), (1,4)] (by norm_num),
    hsum [(1,4), (2,3)] (by norm_num),
    hsum [(1,4), (3,2)] (by norm_num),
    hsum [(1,5), (2,2)] (by norm_num),
    hsum [(2,2), (2,4)] (by norm_num),
    hsum [(2,2), (3,3)] (by norm_num),
    hsum [(2,3), (2,3)] (by norm_num),
    hsum [(1,1), (1,1), (1,5)] (by norm_num),
    hsum [(1,1), (1,1), (2,4)] (by norm_num),
    hsum [(1,1), (1,1), (3,3)] (by norm_num),
    hsum [(1,1), (1,1), (4,2)] (by norm_num),
    hsum [(1,1), (1,2), (1,4)] (by norm_num),
    hsum [(1,1), (1,2), (2,3)] (by norm_num),
    hsum [(1,1), (1,2), (3,2)] (by norm_num),
    hsum [(1,1), (1,3), (1,3)] (by norm_num),
    hsum [(1,1), (1,3), (2,2)] (by norm_num),
    hsum [(1,1), (1,4), (1,2)] (by norm_num),
    hsum [(1,1), (2,1), (1,4)] (by norm_num),
    hsum [(1,1), (2,1), (2,3)] (by norm_num),
    hsum [(1,1), (2,1), (3,2)] (by norm_num),
    hsum [(1,1), (2,2), (1,3)] (by norm_num),
    hsum [(1,1), (2,2), (2,2)] (by norm_num),
    hsum [(1,1), (2,3), (1,2)] (by norm_num),
    hsum [(1,1), (3,1), (1,3)] (by norm_num),
    hsum [(1,1), (3,1), (2,2)] (by norm_num),
    hsum [(1,1), (3,2), (1,2)] (by norm_num),
    hsum [(1,2), (1,2), (1,3)] (by norm_num),
    hsum [(1,2), (1,2), (2,2)] (by norm_num),
    hsum [(1,2), (2,1), (2,2)] (by norm_num),
    hsum [(1,1), (1,1), (1,1), (1,3)] (by norm_num),
    hsum [(1,1), (1,1), (1,1), (2,2)] (by norm_num),
    hsum [(1,1), (1,1), (1,2), (1,2)] (by norm_num),
    hsum [(1,1), (1,1), (2,1), (1,2)] (by norm_num),
    hsum [(1,1), (1,2), (1,1), (1,2)] (by norm_num),
    hsum [(1, 1), (1, 1), (1, 1), (1, 1), (1, 1)] (by norm_num)
  ]

end EvgenyTheorem
