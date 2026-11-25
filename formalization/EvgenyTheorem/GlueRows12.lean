import EvgenyTheorem.GlueRows10

namespace EvgenyTheorem

/-- Transport a finite product of glued-state diagonal pairs through degree
11 across the canonical root equivalence. This is the degree-11 analogue of
the H10 pair-product transport; it leaves the H10 interface unchanged. -/
theorem glueRHS12_pair_product_transport
    (m : ℕ)
    (Khi : Matrix (WSG (m + 1)) (WSG (m + 1)) ℂ)
    (Klo : Matrix (WSG m) (WSG m) ℂ)
    (e : {w : WSG (m + 1) // (sgGlue (m + 1)).g w} ≃
      {w : WSG m // (sgGlue m).g w})
    (hpow : ∀ (w : WSG (m + 1)) (hw : (sgGlue (m + 1)).g w),
      ∀ n, n ≤ 11 →
        (Khi ^ n) w w =
          (Klo ^ n) (e ⟨w, hw⟩).1 (e ⟨w, hw⟩).1 ∧
        (Khi ^ n) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
          (Klo ^ n) ((sgGlue m).σ (e ⟨w, hw⟩).1)
            ((sgGlue m).σ (e ⟨w, hw⟩).1))
    {w : WSG (m + 1)} (hw : (sgGlue (m + 1)).g w)
    (ps : List (ℕ × ℕ))
    (hbound : ∀ p ∈ ps, p.1 ≤ 11 ∧ p.2 ≤ 11) :
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
      have htail : ∀ q ∈ ps, q.1 ≤ 11 ∧ q.2 ≤ 11 := by
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

/-- Transport the full conditional sum over glued states for any finite
list of diagonal pairs whose exponents are at most 11. -/
theorem glueRHS12_pair_sum_transport
    (m : ℕ)
    (Khi : Matrix (WSG (m + 1)) (WSG (m + 1)) ℂ)
    (Klo : Matrix (WSG m) (WSG m) ℂ)
    (e : {w : WSG (m + 1) // (sgGlue (m + 1)).g w} ≃
      {w : WSG m // (sgGlue m).g w})
    (hpow : ∀ (w : WSG (m + 1)) (hw : (sgGlue (m + 1)).g w),
      ∀ n, n ≤ 11 →
        (Khi ^ n) w w =
          (Klo ^ n) (e ⟨w, hw⟩).1 (e ⟨w, hw⟩).1 ∧
        (Khi ^ n) ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
          (Klo ^ n) ((sgGlue m).σ (e ⟨w, hw⟩).1)
            ((sgGlue m).σ (e ⟨w, hw⟩).1))
    (ps : List (ℕ × ℕ))
    (hbound : ∀ p ∈ ps, p.1 ≤ 11 ∧ p.2 ≤ 11) :
    glueRHS8_pair_sum (m + 1) Khi ps = glueRHS8_pair_sum m Klo ps := by
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
          exact glueRHS12_pair_product_transport m Khi Klo e hpow
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

/-- The degree-11 pair-sum transport for the H12 orientation along the
canonical glued-root equivalence. The two axis-periodicity hypotheses are
exactly those required by the already-proved diagonal transport theorem. -/
theorem glueRHS12_tilde_pair_sum_adjacent
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (haxX : ∀ k, ax (3 ^ m + k) = ax k)
    (haxY : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (ps : List (ℕ × ℕ))
    (hbound : ∀ p ∈ ps, p.1 ≤ 11 ∧ p.2 ≤ 11) :
    glueRHS8_pair_sum (m + 1)
        (sgK (m + 1) θ ax (oTil (m + 2))) ps =
      glueRHS8_pair_sum m (sgK m θ ax (oTil (m + 1))) ps := by
  refine glueRHS12_pair_sum_transport m
    (sgK (m + 1) θ ax (oTil (m + 2)))
    (sgK m θ ax (oTil (m + 1)))
    (sgK_glued_root_equiv m) ?_ ps hbound
  intro w hw n hn
  exact sgK_glued_state_diag_one_to_eleven_transport
    m hm θ ax haxX haxY hw n hn


/-- The sum of a list after incrementing every entry. -/
private theorem h12_list_sum_map_succ (xs : List ℕ) :
    (xs.map Nat.succ).sum = xs.sum + xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      omega

/-- Adjacent-level transport of an individual positive even p=12 gap trace.
The boundary reduction turns it into six degree-at-most-eleven diagonal
pairs, and the H12 pair-sum transport moves the complete glued-state sum. -/
theorem sg_trace_p12_even_positive_gap_trace_adjacent
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (haxX : ∀ k, ax (3 ^ m + k) = ax k)
    (haxY : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (r : ℕ) (hrlo : 2 ≤ r) (hrhi : r ≤ 12)
    (hre : r % 2 = 0)
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
        exact h12_list_sum_map_succ raw
      _ = (12 - r) + r := by rw [hrawsum, hrawlen]
      _ = 12 := by omega
  have hpos : ∀ x ∈ positiveGaps, 0 < x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact Nat.succ_pos y
  have hboundaryHi :=
    cyclicGapTrace_p12_even_positive_gap_boundary
      (m + 1) (by omega) θ ax (oTil (m + 2)) (oTil_anti (m + 2))
      r hrlo hrhi hre positiveGaps hlen hsum hpos
  have hboundaryLo :=
    cyclicGapTrace_p12_even_positive_gap_boundary
      m hm θ ax (oTil (m + 1)) (oTil_anti (m + 1))
      r hrlo hrhi hre positiveGaps hlen hsum hpos
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
            m (by omega) θ ax haxX haxY ps (by simpa [ps] using hboundaryHi.2)
    _ = cyclicGapTrace (sgK m θ ax (oTil (m + 1)))
        (sgGlue m).N positiveGaps := by
          simpa [ps] using hboundaryLo.1.symm

/-- The complete positive even p=12 word stratum is invariant between
adjacent levels. The weighted word-to-gap identity and the pointwise
six-pair transport are combined without enumerating cyclic orbits. -/
theorem sg_trace_p12_even_N_word_stratum_adjacent
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
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
    exact sg_trace_p12_even_positive_gap_trace_adjacent
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


/-- The complete sum of all positive even p=12 word strata is invariant
between adjacent levels. The r=0 main trace is intentionally excluded: this
is the boundary correction, not yet the full twelfth-moment recurrence. -/
theorem sg_trace_p12_all_positive_even_N_word_strata_adjacent
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
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
    exact sg_trace_p12_even_N_word_stratum_adjacent
      m hm θ ax haxX haxY r hrlo hrhi hcond.1
  · simp only [if_neg hcond]

end EvgenyTheorem
