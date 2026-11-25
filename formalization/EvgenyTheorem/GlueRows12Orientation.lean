import EvgenyTheorem.GlueRows12

namespace EvgenyTheorem

/-- A glued state cannot reach the exceptional orientation-flip endpoint
in at most ten steps once m >= 4. The shortest coordinate gap is
2^m - 1 >= 15. -/
theorem sgK_pow_zero_from_glue_to_flip_up_to_ten
    (m n : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (w z : WSG m) (hw : (sgGlue m).g w)
    (hz : p6FlipEndpoint m z) (hn : n ≤ 10) :
    (sgK m θ ax o ^ n) w z = 0 := by
  classical
  by_cases hb : w.1 = GCopy.B
  · have hpB : w.2.1.1 = (0, 0) ∨ w.2.1.1 = (0, 2 ^ m) :=
      glued_B_point m hw hb
    have hpow : 12 ≤ 2 ^ m := by
      calc
        12 ≤ 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hside : 10 < 2 ^ m - 1 := by omega
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

/-- Every glued row of K^n is unchanged by the exceptional corner flip
through degree eleven. The last induction step uses the radius-ten
zero-entry bound above. -/
theorem sgK_pow_row_eq_num_til_on_glue_up_to_eleven
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (w : WSG m) (hw : (sgGlue m).g w) :
    ∀ n, n ≤ 11 → ∀ z,
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
      have hn10 : n ≤ 10 := by omega
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hflip : p6FlipEndpoint m y
      · have hnum := sgK_pow_zero_from_glue_to_flip_up_to_ten
          m n hm θ ax (oNum (m + 1)) w y hw hflip hn10
        have htil := sgK_pow_zero_from_glue_to_flip_up_to_ten
          m n hm θ ax (oTil (m + 1)) w y hw hflip hn10
        rw [hnum, htil]
        simp
      · have hn11 : n ≤ 11 := by omega
        rw [ih hn11 y, sgK_num_til_row_eq_away_flip m (by omega) θ ax y z hflip]

/-- Diagonal specialization of the degree-eleven glued-row comparison. -/
theorem sgK_pow_diag_eq_num_til_on_glue_up_to_eleven
    (m n : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (w : WSG m) (hw : (sgGlue m).g w) (hn : n ≤ 11) :
    (sgK m θ ax (oNum (m + 1)) ^ n) w w =
      (sgK m θ ax (oTil (m + 1)) ^ n) w w :=
  sgK_pow_row_eq_num_til_on_glue_up_to_eleven m hm θ ax w hw n hn w

/-- A finite product of glued-state diagonal pairs is unchanged when two
operators agree on both glued-root diagonals through degree eleven. -/
theorem glueRHS12_pair_product_congr
    (m : ℕ) (K K' : Matrix (WSG m) (WSG m) ℂ)
    (h : ∀ x, (sgGlue m).g x → ∀ n, n ≤ 11 →
      (K ^ n) x x = (K' ^ n) x x ∧
      (K ^ n) ((sgGlue m).σ x) ((sgGlue m).σ x) =
        (K' ^ n) ((sgGlue m).σ x) ((sgGlue m).σ x))
    (x : WSG m) (hg : (sgGlue m).g x) :
    ∀ ps : List (ℕ × ℕ),
      (∀ p ∈ ps, p.1 ≤ 11 ∧ p.2 ≤ 11) →
        glueRHS8_pair_product m K x ps = glueRHS8_pair_product m K' x ps := by
  intro ps
  induction ps with
  | nil =>
      intro _
      rfl
  | cons p ps ih =>
      intro hb
      have hp := hb p (by simp)
      have htail : ∀ q ∈ ps, q.1 ≤ 11 ∧ q.2 ≤ 11 := by
        intro q hq
        exact hb q (by simp [hq])
      have hvalue :
          glueRHS8_pair_value m K x p =
            glueRHS8_pair_value m K' x p := by
        have hfirst := (h x hg p.1 hp.1).1
        have hsecond := (h x hg p.2 hp.2).2
        simp only [glueRHS8_pair_value, hfirst, hsecond]
      change
        glueRHS8_pair_value m K x p * glueRHS8_pair_product m K x ps =
          glueRHS8_pair_value m K' x p * glueRHS8_pair_product m K' x ps
      rw [hvalue, ih htail]

/-- The complete conditional sum of glued-state pair-products depends only
on diagonal powers through degree eleven. -/
theorem glueRHS12_pair_sum_congr
    (m : ℕ) (K K' : Matrix (WSG m) (WSG m) ℂ)
    (h : ∀ x, (sgGlue m).g x → ∀ n, n ≤ 11 →
      (K ^ n) x x = (K' ^ n) x x ∧
      (K ^ n) ((sgGlue m).σ x) ((sgGlue m).σ x) =
        (K' ^ n) ((sgGlue m).σ x) ((sgGlue m).σ x))
    (ps : List (ℕ × ℕ))
    (hb : ∀ p ∈ ps, p.1 ≤ 11 ∧ p.2 ≤ 11) :
    glueRHS8_pair_sum m K ps = glueRHS8_pair_sum m K' ps := by
  classical
  unfold glueRHS8_pair_sum
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : (sgGlue m).g x
  · simp only [if_pos hg]
    exact glueRHS12_pair_product_congr m K K' h x hg ps hb
  · simp only [if_neg hg]

/-- Sum of a list after incrementing every entry. This local copy keeps the
orientation module independent of the private helper in GlueRows12.lean. -/
private theorem h12_list_sum_map_succ_orientation (xs : List ℕ) :
    (xs.map Nat.succ).sum = xs.sum + xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      omega

/-- Compare the p=12 positive even-gap boundary trace in the numbering and
flipped-corner orientations at the same level. The bounded six-pair form
reduces the comparison to glued-state diagonal powers through degree 11. -/
theorem sg_trace_p12_even_positive_gap_trace_num_eq_til
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (r : ℕ) (hrlo : 2 ≤ r) (hrhi : r ≤ 12) (hre : r % 2 = 0)
    (gaps : binaryWordGapVectorStratum 12 r) :
    cyclicGapTrace (sgK m θ ax (oNum (m + 1))) (sgGlue m).N
        ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ) =
      cyclicGapTrace (sgK m θ ax (oTil (m + 1))) (sgGlue m).N
        ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ) := by
  classical
  let raw : List ℕ :=
    List.ofFn (fun i : Fin r => (gaps.val i).val)
  let positiveGaps : List ℕ := raw.map Nat.succ
  have hrawlen : raw.length = r := by simp [raw]
  have hrawsum : raw.sum = 12 - r := by
    simpa [raw] using gaps.property.2
  have hlen : positiveGaps.length = r := by
    simp [positiveGaps, hrawlen]
  have hsum : positiveGaps.sum = 12 := by
    calc
      positiveGaps.sum = raw.sum + raw.length := by
        dsimp [positiveGaps]
        exact h12_list_sum_map_succ_orientation raw
      _ = (12 - r) + r := by rw [hrawsum, hrawlen]
      _ = 12 := by omega
  have hpos : ∀ x ∈ positiveGaps, 0 < x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact Nat.succ_pos y
  have hboundaryNum :=
    cyclicGapTrace_p12_even_positive_gap_boundary
      m hm θ ax (oNum (m + 1)) (oNum_anti (m + 1))
      r hrlo hrhi hre positiveGaps hlen hsum hpos
  have hboundaryTil :=
    cyclicGapTrace_p12_even_positive_gap_boundary
      m hm θ ax (oTil (m + 1)) (oTil_anti (m + 1))
      r hrlo hrhi hre positiveGaps hlen hsum hpos
  let ps := h12GapPairList (h12EvenGapPad r positiveGaps)
  have hdiag :
      ∀ x, (sgGlue m).g x → ∀ n, n ≤ 11 →
        (sgK m θ ax (oNum (m + 1)) ^ n) x x =
          (sgK m θ ax (oTil (m + 1)) ^ n) x x ∧
        (sgK m θ ax (oNum (m + 1)) ^ n)
            ((sgGlue m).σ x) ((sgGlue m).σ x) =
          (sgK m θ ax (oTil (m + 1)) ^ n)
            ((sgGlue m).σ x) ((sgGlue m).σ x) := by
    intro x hx n hn
    have hσ := (sgGlue m).g_σ x hx
    exact ⟨
      sgK_pow_row_eq_num_til_on_glue_up_to_eleven
        m hm θ ax x hx n hn x,
      sgK_pow_row_eq_num_til_on_glue_up_to_eleven
        m hm θ ax ((sgGlue m).σ x) hσ n hn ((sgGlue m).σ x)⟩
  calc
    cyclicGapTrace (sgK m θ ax (oNum (m + 1))) (sgGlue m).N positiveGaps =
      glueRHS8_pair_sum m (sgK m θ ax (oNum (m + 1))) ps := by
        simpa [ps] using hboundaryNum.1
    _ = glueRHS8_pair_sum m (sgK m θ ax (oTil (m + 1))) ps :=
      glueRHS12_pair_sum_congr m
        (sgK m θ ax (oNum (m + 1)))
        (sgK m θ ax (oTil (m + 1))) hdiag ps
        (by simpa [ps] using hboundaryNum.2)
    _ = cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
        (sgGlue m).N positiveGaps := by
        simpa [ps] using hboundaryTil.1.symm

/-- Each positive even p=12 word stratum is orientation-independent.
The weighted word-to-gap identity cancels the nonzero stratum size. -/
theorem sg_trace_p12_even_N_word_stratum_num_eq_til
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (r : ℕ) (hrlo : 2 ≤ r) (hrhi : r ≤ 12) (hre : r % 2 = 0) :
    (∑ w : binaryWordFinStratum 12 r,
      Matrix.trace
        (binaryWordMatrix (sgK m θ ax (oNum (m + 1)))
          (sgK m θ ax (oNum (m + 1)) * (sgGlue m).N) (List.ofFn w.val))) =
    (∑ w : binaryWordFinStratum 12 r,
      Matrix.trace
        (binaryWordMatrix (sgK m θ ax (oTil (m + 1)))
          (sgK m θ ax (oTil (m + 1)) * (sgGlue m).N) (List.ofFn w.val))) := by
  classical
  have hgapSum :
      (∑ gaps : binaryWordGapVectorStratum 12 r,
        cyclicGapTrace (sgK m θ ax (oNum (m + 1))) (sgGlue m).N
          ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ)) =
      (∑ gaps : binaryWordGapVectorStratum 12 r,
        cyclicGapTrace (sgK m θ ax (oTil (m + 1))) (sgGlue m).N
          ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ)) := by
    apply Finset.sum_congr rfl
    intro gaps _
    exact sg_trace_p12_even_positive_gap_trace_num_eq_til
      m hm θ ax r hrlo hrhi hre gaps
  have hweightedNum :=
    binaryWordFinStratum_weighted_trace_eq_positive_gap_sum
      (sgK m θ ax (oNum (m + 1))) (sgGlue m).N 12 r
  have hweightedTil :=
    binaryWordFinStratum_weighted_trace_eq_positive_gap_sum
      (sgK m θ ax (oTil (m + 1))) (sgGlue m).N 12 r
  have hmul :
      (r : ℂ) *
        (∑ w : binaryWordFinStratum 12 r,
          Matrix.trace
            (binaryWordMatrix (sgK m θ ax (oNum (m + 1)))
              (sgK m θ ax (oNum (m + 1)) * (sgGlue m).N)
              (List.ofFn w.val))) =
      (r : ℂ) *
        (∑ w : binaryWordFinStratum 12 r,
          Matrix.trace
            (binaryWordMatrix (sgK m θ ax (oTil (m + 1)))
              (sgK m θ ax (oTil (m + 1)) * (sgGlue m).N)
              (List.ofFn w.val))) := by
    calc
      _ = (12 : ℂ) *
          (∑ gaps : binaryWordGapVectorStratum 12 r,
            cyclicGapTrace (sgK m θ ax (oNum (m + 1))) (sgGlue m).N
              ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ)) :=
        hweightedNum
      _ = (12 : ℂ) *
          (∑ gaps : binaryWordGapVectorStratum 12 r,
            cyclicGapTrace (sgK m θ ax (oTil (m + 1))) (sgGlue m).N
              ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ)) := by
        rw [hgapSum]
      _ = _ := hweightedTil.symm
  have hrpos : 0 < r := by omega
  have hrC : (r : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hrpos)
  exact mul_left_cancel₀ hrC hmul

/-- The complete positive even p=12 word contribution is independent of
numbering versus flipped-corner orientation at every level m >= 4. -/
theorem sg_trace_p12_all_positive_even_N_word_strata_num_eq_til
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis) :
    (∑ r ∈ Finset.range 13,
      if r % 2 = 0 ∧ 0 < r then
        ∑ w : binaryWordFinStratum 12 r,
          Matrix.trace
            (binaryWordMatrix (sgK m θ ax (oNum (m + 1)))
              (sgK m θ ax (oNum (m + 1)) * (sgGlue m).N)
              (List.ofFn w.val))
      else 0) =
    (∑ r ∈ Finset.range 13,
      if r % 2 = 0 ∧ 0 < r then
        ∑ w : binaryWordFinStratum 12 r,
          Matrix.trace
            (binaryWordMatrix (sgK m θ ax (oTil (m + 1)))
              (sgK m θ ax (oTil (m + 1)) * (sgGlue m).N)
              (List.ofFn w.val))
      else 0) := by
  classical
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hcond : r % 2 = 0 ∧ 0 < r
  · simp only [if_pos hcond]
    have hrlo : 2 ≤ r := by omega
    have hrhi : r ≤ 12 := by
      have hrlt : r < 13 := Finset.mem_range.mp hr
      omega
    exact sg_trace_p12_even_N_word_stratum_num_eq_til
      m hm θ ax r hrlo hrhi hcond.1
  · simp only [if_neg hcond]

/-- Complete positive-even insertion contribution for the p=12 trace expansion. -/
noncomputable def glueRHS12
    (m : ℕ) (K : Matrix (WSG m) (WSG m) ℂ) : ℂ :=
  ∑ r ∈ Finset.range 13,
    if r % 2 = 0 ∧ 0 < r then
      ∑ w : binaryWordFinStratum 12 r,
        Matrix.trace (binaryWordMatrix K (K * (sgGlue m).N) (List.ofFn w.val))
    else 0

theorem glueRHS12_num_eq_til
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis) :
    glueRHS12 m (sgK m θ ax (oNum (m + 1))) =
      glueRHS12 m (sgK m θ ax (oTil (m + 1))) := by
  simpa [glueRHS12] using
    sg_trace_p12_all_positive_even_N_word_strata_num_eq_til m hm θ ax

end EvgenyTheorem
