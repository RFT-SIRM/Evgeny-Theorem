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

/-! ### Level-three diagonal transport through degree eleven

The exceptional flipped edge is seven steps from a glued root at m = 3.
The glued-row comparison is therefore available through degree seven.  Since
`sgK` is Hermitian for both orientations, this is enough for diagonal powers
through degree eleven: split n = floor(n/2) + ceil(n/2), and reverse the
second factor by conjugate symmetry.
-/

private theorem matrix_pow_diag_eq_of_hermitian_row_eq
    {W : Type*} [Fintype W] [DecidableEq W]
    (A B : Matrix W W ℂ) (w : W)
    (hA : Matrix.conjTranspose A = A)
    (hB : Matrix.conjTranspose B = B)
    (hrow : ∀ k, k ≤ 6 → ∀ z, (A ^ k) w z = (B ^ k) w z)
    (n : ℕ) (hn : n ≤ 11) :
    (A ^ n) w w = (B ^ n) w w := by
  let p : ℕ := n / 2
  let q : ℕ := n - p
  have hpq : p + q = n := by
    dsimp [p, q]
    omega
  have hp : p ≤ 6 := by
    dsimp [p]
    omega
  have hq : q ≤ 6 := by
    dsimp [q, p]
    omega
  have hpowA : A ^ n = A ^ p * A ^ q := by
    rw [← hpq, pow_add]
  have hpowB : B ^ n = B ^ p * B ^ q := by
    rw [← hpq, pow_add]
  have hqA : Matrix.conjTranspose (A ^ q) = A ^ q := by
    rw [Matrix.conjTranspose_pow, hA]
  have hqB : Matrix.conjTranspose (B ^ q) = B ^ q := by
    rw [Matrix.conjTranspose_pow, hB]
  have hAadj (z : W) :
      (A ^ q) z w = star ((A ^ q) w z) := by
    have h := congrArg star (congrFun (congrFun hqA w) z)
    simpa [Matrix.conjTranspose_apply] using h
  have hBadj (z : W) :
      (B ^ q) z w = star ((B ^ q) w z) := by
    have h := congrArg star (congrFun (congrFun hqB w) z)
    simpa [Matrix.conjTranspose_apply] using h
  rw [hpowA, hpowB, Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro z hz
  rw [hAadj z, hBadj z, hrow p hp z, hrow q hq z]

/-- At level three the exceptional edge is too close for a degree-eleven
row identity, but the diagonal data required by the H12 boundary expression
are still orientation-independent through degree eleven. -/
theorem sgK_pow_diag_eq_num_til_on_glue_up_to_eleven_of_seven
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (w : WSG m) (hw : (sgGlue m).g w)
    (n : ℕ) (hn : n ≤ 11) :
    (sgK m θ ax (oNum (m + 1)) ^ n) w w =
      (sgK m θ ax (oTil (m + 1)) ^ n) w w := by
  exact matrix_pow_diag_eq_of_hermitian_row_eq
    (sgK m θ ax (oNum (m + 1)))
    (sgK m θ ax (oTil (m + 1))) w
    (sgK_hermitian_of_OAnti m θ ax (oNum (m + 1)) (oNum_anti (m + 1)))
    (sgK_hermitian_of_OAnti m θ ax (oTil (m + 1)) (oTil_anti (m + 1)))
    (by
      intro k hk z
      exact sgK_pow_row_eq_num_til_on_glue_up_to_seven
        m hm θ ax w hw k (by omega) z)
    n hn

/-- The same diagonal transport holds at the partner glued root. -/
theorem sgK_pow_partner_diag_eq_num_til_on_glue_up_to_eleven_of_seven
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (w : WSG m) (hw : (sgGlue m).g w)
    (n : ℕ) (hn : n ≤ 11) :
    (sgK m θ ax (oNum (m + 1)) ^ n)
        ((sgGlue m).σ w) ((sgGlue m).σ w) =
      (sgK m θ ax (oTil (m + 1)) ^ n)
        ((sgGlue m).σ w) ((sgGlue m).σ w) := by
  exact sgK_pow_diag_eq_num_til_on_glue_up_to_eleven_of_seven
    m hm θ ax ((sgGlue m).σ w) ((sgGlue m).g_σ w hw) n hn


/-- The positive-even H12 boundary trace is orientation-independent at level
three once the unique possible gap above seven is put at the cyclic head.
The other eleven exponents then lie in the radius-seven locality range;
the head factor is retained as a single arbitrary kernel and contracted from
the opposite side. -/
private theorem sg_trace_p12_even_positive_gap_trace_num_eq_til_of_head_gap_bound
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (r : ℕ) (hrlo : 2 ≤ r) (hrhi : r ≤ 12) (hre : r % 2 = 0)
    (positiveGaps : List ℕ) (hlen : positiveGaps.length = r)
    (hsum : positiveGaps.sum = 12)
    (hpos : ∀ x ∈ positiveGaps, 0 < x)
    (a : ℕ) (tail : List ℕ)
    (hgap : positiveGaps = a :: tail)
    (htailLen : tail.length = r - 1)
    (htailBound : ∀ x ∈ tail, x ≤ 7) :
    cyclicGapTrace (sgK m θ ax (oNum (m + 1))) (sgGlue m).N positiveGaps =
      cyclicGapTrace (sgK m θ ax (oTil (m + 1))) (sgGlue m).N positiveGaps := by
  classical
  have htailBound' : ∀ x ∈ positiveGaps.tail, x ≤ 7 := by
    intro x hx
    rw [hgap] at hx
    exact htailBound x (by simpa using hx)
  have hboundaryNum :=
    cyclicGapTrace_p12_even_positive_gap_boundary_head_gap_of_seven
      m hm θ ax (oNum (m + 1)) (oNum_anti (m + 1))
      r hrlo hrhi hre positiveGaps hlen hsum hpos htailBound'
  have hboundaryTil :=
    cyclicGapTrace_p12_even_positive_gap_boundary_head_gap_of_seven
      m hm θ ax (oTil (m + 1)) (oTil_anti (m + 1))
      r hrlo hrhi hre positiveGaps hlen hsum hpos htailBound'
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
    exact ⟨
      sgK_pow_diag_eq_num_til_on_glue_up_to_eleven_of_seven
        m hm θ ax x hx n hn,
      sgK_pow_partner_diag_eq_num_til_on_glue_up_to_eleven_of_seven
        m hm θ ax x hx n hn⟩
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

/-- At level three, every positive-even p=12 cyclic gap trace is
orientation-independent. A composition of twelve has at most one part
larger than seven; rotating that part to the head leaves a tail of total
weight at most four. -/
theorem sg_trace_p12_even_positive_gap_trace_num_eq_til_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
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
  let gapParts := h12SplitAtFirstLarge positiveGaps
  let preGap := gapParts.1
  let postGap := gapParts.2
  have hdecomp : positiveGaps = preGap ++ postGap := by
    simpa [gapParts, preGap, postGap] using
      h12SplitAtFirstLarge_append positiveGaps
  by_cases hlarge : ∃ x ∈ positiveGaps, 7 < x
  · obtain ⟨head, middle, hsuffix, hhead⟩ :=
      h12SplitAtFirstLarge_suffix_has_large positiveGaps hlarge
    let tail := middle ++ preGap
    let rotated := head :: tail
    have hpostGap : postGap = head :: middle := by
      simpa [gapParts, postGap] using hsuffix
    have hrotEq : rotated = postGap ++ preGap := by
      simp [rotated, tail, hpostGap, List.cons_append]
    have hparts : preGap.sum + (head + middle.sum) = 12 := by
      have hsumParts : preGap.sum + postGap.sum = 12 := by
        simpa [hdecomp, List.sum_append] using hsum
      rw [hpostGap, List.sum_cons] at hsumParts
      exact hsumParts
    have htailSum : tail.sum ≤ 4 := by
      dsimp [tail]
      simp only [List.sum_append]
      omega
    have htailBound : ∀ x ∈ tail, x ≤ 7 := by
      intro x hx
      have hxle : x ≤ tail.sum :=
        h12_nat_le_sum_of_mem (xs := tail) hx
      exact le_trans hxle (by omega)
    have hrotLen : rotated.length = r := by
      calc
        rotated.length = (postGap ++ preGap).length := by rw [hrotEq]
        _ = postGap.length + preGap.length := by simp
        _ = preGap.length + postGap.length := by omega
        _ = (preGap ++ postGap).length := by simp
        _ = positiveGaps.length := by rw [hdecomp]
        _ = r := hlen
    have hrotSum : rotated.sum = 12 := by
      calc
        rotated.sum = (postGap ++ preGap).sum := by rw [hrotEq]
        _ = postGap.sum + preGap.sum := by simp
        _ = preGap.sum + postGap.sum := by omega
        _ = (preGap ++ postGap).sum := by simp
        _ = positiveGaps.sum := by rw [hdecomp]
        _ = 12 := hsum
    have hrotPos : ∀ x ∈ rotated, 0 < x := by
      intro x hx
      have hx' : x ∈ postGap ++ preGap := by
        rw [← hrotEq]
        exact hx
      have hxsource : x ∈ positiveGaps := by
        rw [hdecomp]
        rcases List.mem_append.mp hx' with hxs | hxp
        · exact List.mem_append_right _ hxs
        · exact List.mem_append_left _ hxp
      exact hpos x hxsource
    have hrotEqTraceNum :
        cyclicGapTrace (sgK m θ ax (oNum (m + 1))) (sgGlue m).N positiveGaps =
          cyclicGapTrace (sgK m θ ax (oNum (m + 1))) (sgGlue m).N rotated := by
      calc
        _ = cyclicGapTrace (sgK m θ ax (oNum (m + 1)))
              (sgGlue m).N (preGap ++ postGap) := by rw [hdecomp]
        _ = cyclicGapTrace (sgK m θ ax (oNum (m + 1)))
              (sgGlue m).N (postGap ++ preGap) :=
              cyclicGapTrace_append_comm _ _ _ _
        _ = _ := by rw [hrotEq]
    have hrotEqTraceTil :
        cyclicGapTrace (sgK m θ ax (oTil (m + 1))) (sgGlue m).N positiveGaps =
          cyclicGapTrace (sgK m θ ax (oTil (m + 1))) (sgGlue m).N rotated := by
      calc
        _ = cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
              (sgGlue m).N (preGap ++ postGap) := by rw [hdecomp]
        _ = cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
              (sgGlue m).N (postGap ++ preGap) :=
              cyclicGapTrace_append_comm _ _ _ _
        _ = _ := by rw [hrotEq]
    have htailLen : tail.length = r - 1 := by
      have h := hrotLen
      simp [rotated] at h
      omega
    have hrotCompare :=
      sg_trace_p12_even_positive_gap_trace_num_eq_til_of_head_gap_bound
        m hm θ ax r hrlo hrhi hre rotated hrotLen hrotSum hrotPos
        head tail rfl htailLen htailBound
    calc
      cyclicGapTrace (sgK m θ ax (oNum (m + 1))) (sgGlue m).N positiveGaps =
          cyclicGapTrace (sgK m θ ax (oNum (m + 1))) (sgGlue m).N rotated :=
        hrotEqTraceNum
      _ = cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
          (sgGlue m).N rotated := hrotCompare
      _ = cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
          (sgGlue m).N positiveGaps := hrotEqTraceTil.symm
  · have hsmall : ∀ x ∈ positiveGaps, x ≤ 7 := by
      intro x hx
      by_contra hxlarge
      exact hlarge ⟨x, hx, by omega⟩
    cases hlist : positiveGaps with
    | nil => simp [hlist] at hlen; omega
    | cons head tail =>
        have htailLen : tail.length = r - 1 := by
          simp [hlist] at hlen ⊢
          omega
        have htailBound : ∀ x ∈ tail, x ≤ 7 := by
          intro x hx
          exact hsmall x (by simp [hlist, hx])
        have hcompare :=
          sg_trace_p12_even_positive_gap_trace_num_eq_til_of_head_gap_bound
            m hm θ ax r hrlo hrhi hre positiveGaps hlen hsum hpos
            head tail hlist htailLen htailBound
        exact hcompare



/-- Each positive even p=12 word stratum is orientation-independent at
level three. -/
theorem sg_trace_p12_even_N_word_stratum_num_eq_til_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
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
    exact sg_trace_p12_even_positive_gap_trace_num_eq_til_level3
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

/-- The complete positive-even H12 insertion contribution is
orientation-independent at level three. -/
theorem sg_trace_p12_all_positive_even_N_word_strata_num_eq_til_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis) :
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
    exact sg_trace_p12_even_N_word_stratum_num_eq_til_level3
      m hm θ ax r hrlo hrhi hcond.1
  · simp only [if_neg hcond]

/-- The full positive-even boundary contribution is independent of
numbering versus flipped-corner orientation at level three. -/
theorem glueRHS12_num_eq_til_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis) :
    glueRHS12 m (sgK m θ ax (oNum (m + 1))) =
      glueRHS12 m (sgK m θ ax (oTil (m + 1))) := by
  simpa [glueRHS12] using
    sg_trace_p12_all_positive_even_N_word_strata_num_eq_til_level3
      m hm θ ax



/-- Adjacent-level transport of a positive-even H12 gap trace at the base
level m=3. The lower-level boundary reducer permits one unrestricted cyclic
head gap, and the existing glued-state transport matches all six diagonal
pairs through degree eleven. -/
private theorem sg_trace_p12_even_positive_gap_trace_adjacent_of_head_gap_bound
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (haxX : ∀ k, ax (3 ^ m + k) = ax k)
    (haxY : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (r : ℕ) (hrlo : 2 ≤ r) (hrhi : r ≤ 12) (hre : r % 2 = 0)
    (positiveGaps : List ℕ) (hlen : positiveGaps.length = r)
    (hsum : positiveGaps.sum = 12)
    (hpos : ∀ x ∈ positiveGaps, 0 < x)
    (a : ℕ) (tail : List ℕ)
    (hgap : positiveGaps = a :: tail)
    (_htailLen : tail.length = r - 1)
    (htailBound : ∀ x ∈ tail, x ≤ 7) :
    cyclicGapTrace (sgK (m + 1) θ ax (oTil (m + 2)))
        (sgGlue (m + 1)).N positiveGaps =
      cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
        (sgGlue m).N positiveGaps := by
  classical
  have htailBound' : ∀ x ∈ positiveGaps.tail, x ≤ 7 := by
    intro x hx
    rw [hgap] at hx
    exact htailBound x (by simpa using hx)
  have hboundaryHi :=
    cyclicGapTrace_p12_even_positive_gap_boundary
      (m + 1) (by omega) θ ax (oTil (m + 2)) (oTil_anti (m + 2))
      r hrlo hrhi hre positiveGaps hlen hsum hpos
  have hboundaryLo :=
    cyclicGapTrace_p12_even_positive_gap_boundary_head_gap_of_seven
      m hm θ ax (oTil (m + 1)) (oTil_anti (m + 1))
      r hrlo hrhi hre positiveGaps hlen hsum hpos htailBound'
  let ps := h12GapPairList (h12EvenGapPad r positiveGaps)
  calc
    cyclicGapTrace (sgK (m + 1) θ ax (oTil (m + 2)))
        (sgGlue (m + 1)).N positiveGaps =
      glueRHS8_pair_sum (m + 1)
        (sgK (m + 1) θ ax (oTil (m + 2))) ps := by
          simpa [ps] using hboundaryHi.1
    _ = glueRHS8_pair_sum m
        (sgK m θ ax (oTil (m + 1))) ps :=
          glueRHS12_tilde_pair_sum_adjacent
            m hm θ ax haxX haxY ps (by simpa [ps] using hboundaryLo.2)
    _ = cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
        (sgGlue m).N positiveGaps := by
          simpa [ps] using hboundaryLo.1.symm

/-- Adjacent-level transport of every positive-even p=12 cyclic gap trace
starting at m=3. The cyclic head is selected so that all other exponents are
covered by the radius-seven off-diagonal lemma. -/
theorem sg_trace_p12_even_positive_gap_trace_adjacent_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (haxX : ∀ k, ax (3 ^ m + k) = ax k)
    (haxY : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (r : ℕ) (hrlo : 2 ≤ r) (hrhi : r ≤ 12) (hre : r % 2 = 0)
    (gaps : binaryWordGapVectorStratum 12 r) :
    cyclicGapTrace (sgK (m + 1) θ ax (oTil (m + 2)))
        (sgGlue (m + 1)).N
        ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ) =
      cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
        (sgGlue m).N
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
  let gapParts := h12SplitAtFirstLarge positiveGaps
  let preGap := gapParts.1
  let postGap := gapParts.2
  have hdecomp : positiveGaps = preGap ++ postGap := by
    simpa [gapParts, preGap, postGap] using
      h12SplitAtFirstLarge_append positiveGaps
  by_cases hlarge : ∃ x ∈ positiveGaps, 7 < x
  · obtain ⟨head, middle, hsuffix, hhead⟩ :=
      h12SplitAtFirstLarge_suffix_has_large positiveGaps hlarge
    let tail := middle ++ preGap
    let rotated := head :: tail
    have hpostGap : postGap = head :: middle := by
      simpa [gapParts, postGap] using hsuffix
    have hrotEq : rotated = postGap ++ preGap := by
      simp [rotated, tail, hpostGap, List.cons_append]
    have hparts : preGap.sum + (head + middle.sum) = 12 := by
      have hsumParts : preGap.sum + postGap.sum = 12 := by
        simpa [hdecomp, List.sum_append] using hsum
      rw [hpostGap, List.sum_cons] at hsumParts
      exact hsumParts
    have htailSum : tail.sum ≤ 4 := by
      dsimp [tail]
      simp only [List.sum_append]
      omega
    have htailBound : ∀ x ∈ tail, x ≤ 7 := by
      intro x hx
      have hxle : x ≤ tail.sum :=
        h12_nat_le_sum_of_mem (xs := tail) hx
      exact le_trans hxle (by omega)
    have hrotLen : rotated.length = r := by
      calc
        rotated.length = (postGap ++ preGap).length := by rw [hrotEq]
        _ = postGap.length + preGap.length := by simp
        _ = preGap.length + postGap.length := by omega
        _ = (preGap ++ postGap).length := by simp
        _ = positiveGaps.length := by rw [hdecomp]
        _ = r := hlen
    have hrotSum : rotated.sum = 12 := by
      calc
        rotated.sum = (postGap ++ preGap).sum := by rw [hrotEq]
        _ = postGap.sum + preGap.sum := by simp
        _ = preGap.sum + postGap.sum := by omega
        _ = (preGap ++ postGap).sum := by simp
        _ = positiveGaps.sum := by rw [hdecomp]
        _ = 12 := hsum
    have hrotPos : ∀ x ∈ rotated, 0 < x := by
      intro x hx
      have hx' : x ∈ postGap ++ preGap := by
        rw [← hrotEq]
        exact hx
      have hxsource : x ∈ positiveGaps := by
        rw [hdecomp]
        rcases List.mem_append.mp hx' with hxs | hxp
        · exact List.mem_append_right _ hxs
        · exact List.mem_append_left _ hxp
      exact hpos x hxsource
    have htailLen : tail.length = r - 1 := by
      have h := hrotLen
      simp [rotated] at h
      omega
    have hcompare :=
      sg_trace_p12_even_positive_gap_trace_adjacent_of_head_gap_bound
        m hm θ ax haxX haxY r hrlo hrhi hre rotated hrotLen hrotSum hrotPos
        head tail rfl htailLen htailBound
    have hrotateHi :
        cyclicGapTrace (sgK (m + 1) θ ax (oTil (m + 2)))
          (sgGlue (m + 1)).N positiveGaps =
        cyclicGapTrace (sgK (m + 1) θ ax (oTil (m + 2)))
          (sgGlue (m + 1)).N rotated := by
      calc
        _ = cyclicGapTrace (sgK (m + 1) θ ax (oTil (m + 2)))
              (sgGlue (m + 1)).N (preGap ++ postGap) := by rw [hdecomp]
        _ = cyclicGapTrace (sgK (m + 1) θ ax (oTil (m + 2)))
              (sgGlue (m + 1)).N (postGap ++ preGap) :=
              cyclicGapTrace_append_comm _ _ _ _
        _ = _ := by rw [hrotEq]
    have hrotateLo :
        cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
          (sgGlue m).N positiveGaps =
        cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
          (sgGlue m).N rotated := by
      calc
        _ = cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
              (sgGlue m).N (preGap ++ postGap) := by rw [hdecomp]
        _ = cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
              (sgGlue m).N (postGap ++ preGap) :=
              cyclicGapTrace_append_comm _ _ _ _
        _ = _ := by rw [hrotEq]
    calc
      cyclicGapTrace (sgK (m + 1) θ ax (oTil (m + 2)))
          (sgGlue (m + 1)).N positiveGaps =
        cyclicGapTrace (sgK (m + 1) θ ax (oTil (m + 2)))
          (sgGlue (m + 1)).N rotated := hrotateHi
      _ = cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
          (sgGlue m).N rotated := hcompare
      _ = cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
          (sgGlue m).N positiveGaps := hrotateLo.symm
  · have hsmall : ∀ x ∈ positiveGaps, x ≤ 7 := by
      intro x hx
      by_contra hxlarge
      exact hlarge ⟨x, hx, by omega⟩
    cases hlist : positiveGaps with
    | nil => simp [hlist] at hlen; omega
    | cons head tail =>
        have htailLen : tail.length = r - 1 := by
          simp [hlist] at hlen ⊢
          omega
        have htailBound : ∀ x ∈ tail, x ≤ 7 := by
          intro x hx
          exact hsmall x (by simp [hlist, hx])
        exact sg_trace_p12_even_positive_gap_trace_adjacent_of_head_gap_bound
          m hm θ ax haxX haxY r hrlo hrhi hre positiveGaps hlen hsum hpos
          head tail hlist htailLen htailBound


/-- Complete positive-even p=12 word-stratum transport in the first
adjacent-level step m=3. -/
theorem sg_trace_p12_even_N_word_stratum_adjacent_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (haxX : ∀ k, ax (3 ^ m + k) = ax k)
    (haxY : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (r : ℕ) (hrlo : 2 ≤ r) (hrhi : r ≤ 12)
    (hre : r % 2 = 0) :
    (∑ w : binaryWordFinStratum 12 r,
      Matrix.trace
        (binaryWordMatrix (sgK (m + 1) θ ax (oTil (m + 2)))
          (sgK (m + 1) θ ax (oTil (m + 2)) * (sgGlue (m + 1)).N)
          (List.ofFn w.val))) =
    (∑ w : binaryWordFinStratum 12 r,
      Matrix.trace
        (binaryWordMatrix (sgK m θ ax (oTil (m + 1)))
          (sgK m θ ax (oTil (m + 1)) * (sgGlue m).N)
          (List.ofFn w.val))) := by
  classical
  have hgapSum :
      (∑ gaps : binaryWordGapVectorStratum 12 r,
        cyclicGapTrace (sgK (m + 1) θ ax (oTil (m + 2)))
          (sgGlue (m + 1)).N
          ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ)) =
      (∑ gaps : binaryWordGapVectorStratum 12 r,
        cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
          (sgGlue m).N
          ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ)) := by
    apply Finset.sum_congr rfl
    intro gaps _
    exact sg_trace_p12_even_positive_gap_trace_adjacent_level3
      m hm θ ax haxX haxY r hrlo hrhi hre gaps
  have hweightedHi :=
    binaryWordFinStratum_weighted_trace_eq_positive_gap_sum
      (sgK (m + 1) θ ax (oTil (m + 2))) (sgGlue (m + 1)).N 12 r
  have hweightedLo :=
    binaryWordFinStratum_weighted_trace_eq_positive_gap_sum
      (sgK m θ ax (oTil (m + 1))) (sgGlue m).N 12 r
  have hmul :
      (r : ℂ) *
        (∑ w : binaryWordFinStratum 12 r,
          Matrix.trace
            (binaryWordMatrix (sgK (m + 1) θ ax (oTil (m + 2)))
              (sgK (m + 1) θ ax (oTil (m + 2)) * (sgGlue (m + 1)).N)
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
            cyclicGapTrace (sgK (m + 1) θ ax (oTil (m + 2)))
              (sgGlue (m + 1)).N
              ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ)) :=
        hweightedHi
      _ = (12 : ℂ) *
          (∑ gaps : binaryWordGapVectorStratum 12 r,
            cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
              (sgGlue m).N
              ((List.ofFn (fun i : Fin r => (gaps.val i).val)).map Nat.succ)) := by
        rw [hgapSum]
      _ = _ := hweightedLo.symm
  have hrpos : 0 < r := by omega
  have hrC : (r : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hrpos)
  exact mul_left_cancel₀ hrC hmul

/-- Complete positive-even p=12 boundary contribution transport in the
first adjacent-level step m=3. -/
theorem sg_trace_p12_all_positive_even_N_word_strata_adjacent_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (haxX : ∀ k, ax (3 ^ m + k) = ax k)
    (haxY : ∀ k, ax (2 * 3 ^ m + k) = ax k) :
    (∑ r ∈ Finset.range 13,
      if r % 2 = 0 ∧ 0 < r then
        ∑ w : binaryWordFinStratum 12 r,
          Matrix.trace
            (binaryWordMatrix (sgK (m + 1) θ ax (oTil (m + 2)))
              (sgK (m + 1) θ ax (oTil (m + 2)) * (sgGlue (m + 1)).N)
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
    exact sg_trace_p12_even_N_word_stratum_adjacent_level3
      m hm θ ax haxX haxY r hrlo hrhi hcond.1
  · simp only [if_neg hcond]


/-- Numbering-versus-flipped orientation invariance of the H12 boundary
term for every m >= 3, combining the base-level and stable-range proofs. -/
theorem glueRHS12_num_eq_til_from_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis) :
    glueRHS12 m (sgK m θ ax (oNum (m + 1))) =
      glueRHS12 m (sgK m θ ax (oTil (m + 1))) := by
  by_cases hm4 : 4 ≤ m
  · exact glueRHS12_num_eq_til m hm4 θ ax
  · have hmEq : m = 3 := by omega
    subst m
    exact glueRHS12_num_eq_til_level3 3 le_rfl θ ax

end EvgenyTheorem
