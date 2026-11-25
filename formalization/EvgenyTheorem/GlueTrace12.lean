import EvgenyTheorem.GlueRows12Orientation

namespace EvgenyTheorem

/-- The zero-insertion p=12 word stratum contains only the all-K word,
so its exact finite-word trace is `Tr(K^12)`. -/
theorem sg_trace_p12_zero_N_word_stratum
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    (∑ w : binaryWordFinStratum 12 0,
      Matrix.trace
        (binaryWordMatrix (sgK m θ ax o)
          (sgK m θ ax o * (sgGlue m).N) (List.ofFn w.val))) =
      Matrix.trace (sgK m θ ax o ^ 12) := by
  classical
  let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
  let N : Matrix (WSG m) (WSG m) ℂ := (sgGlue m).N
  change
    (∑ w : binaryWordFinStratum 12 0,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))) =
      Matrix.trace (K ^ 12)
  let w0 : binaryWordFinStratum 12 0 :=
    ⟨fun _ => false, by
      constructor
      · omega
      · simp⟩
  have hunique : ∀ w : binaryWordFinStratum 12 0, w = w0 := by
    intro w
    apply Subtype.ext
    funext i
    cases h : w.val i with
    | false => rfl
    | true =>
        have hcard := binaryWordFin_true_positions_card 12 0 w
        have hpos :
            0 < Fintype.card {j : Fin 12 // w.val j = true} :=
          Fintype.card_pos_iff.mpr ⟨⟨i, h⟩⟩
        rw [hcard] at hpos
        omega
  letI : Unique (binaryWordFinStratum 12 0) :=
    ⟨⟨w0⟩, fun w => hunique w⟩
  have hword0 :
      List.ofFn (fun _ : Fin 12 => false) = List.replicate 12 false := by
    simp
  have hprod (n : ℕ) :
      (List.replicate n K).prod = K ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        simp [List.replicate_succ, ih, pow_succ']
  have hmatrix :
      binaryWordMatrix K (K * N) (List.ofFn w0.val) = K ^ 12 := by
    change
      binaryWordMatrix K (K * N)
        (List.ofFn (fun _ : Fin 12 => false)) = K ^ 12
    rw [hword0]
    calc
      binaryWordMatrix K (K * N) (List.replicate 12 false) =
          (List.replicate 12 K).prod := by
        unfold binaryWordMatrix
        rw [List.map_replicate]
        rw [if_neg (by decide : ¬ (false = true))]
      _ = K ^ 12 := hprod 12
  calc
    _ = ∑ w : binaryWordFinStratum 12 0,
          Matrix.trace
            (binaryWordMatrix K (K * N) (List.ofFn w0.val)) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hunique w]
    _ = Matrix.trace
          (binaryWordMatrix K (K * N) (List.ofFn w0.val)) := by
      rw [Fintype.sum_unique]
    _ = Matrix.trace (K ^ 12) := by
      rw [hmatrix]

/-- The complete ordered p=12 expansion over the glued operator splits
into the zero-insertion main trace and the positive-even boundary term.
Every odd positive-insertion stratum vanishes. -/
theorem sg_trace_p12_ordered_expansion_boundary
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    Matrix.trace
      ((sgK m θ ax o + sgK m θ ax o * (sgGlue m).N) ^ 12) =
      Matrix.trace (sgK m θ ax o ^ 12) +
        glueRHS12 m (sgK m θ ax o) := by
  let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
  let N : Matrix (WSG m) (WSG m) ℂ := (sgGlue m).N
  let stratum (r : ℕ) : ℂ :=
    ∑ w : binaryWordFinStratum 12 r,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))
  have hzero := sg_trace_p12_zero_N_word_stratum m θ ax o
  have hodd := sg_trace_p12_all_odd_N_word_strata_zero
    m hm θ ax o hanti
  have hsplit :
      (∑ r ∈ Finset.range 13, stratum r) =
        (∑ r ∈ Finset.range 13, if r = 0 then stratum r else 0) +
        (∑ r ∈ Finset.range 13,
          if r % 2 = 1 then stratum r else 0) +
        (∑ r ∈ Finset.range 13,
          if r % 2 = 0 ∧ 0 < r then stratum r else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hr0 : r = 0
    · subst r
      simp
    · by_cases hodd : r % 2 = 1
      · have hnotEven : ¬ (r % 2 = 0 ∧ 0 < r) := by omega
        simp [hr0, hodd, hnotEven]
      · have heven : r % 2 = 0 := by omega
        have hpos : 0 < r := by omega
        simp [hr0, hodd, heven, hpos]
  have hzeroSum :
      (∑ r ∈ Finset.range 13,
        if r = 0 then stratum r else 0) = stratum 0 := by
    simp
  have hoddSum :
      (∑ r ∈ Finset.range 13,
        if r % 2 = 1 then stratum r else 0) = 0 := by
    simpa [stratum, K, N] using hodd
  have hevenSum :
      (∑ r ∈ Finset.range 13,
        if r % 2 = 0 ∧ 0 < r then stratum r else 0) =
          glueRHS12 m K := by
    rfl
  have hwords :
      Matrix.trace ((K + K * N) ^ 12) =
        ∑ r ∈ Finset.range 13, stratum r := by
    simpa [stratum] using
      (trace_orderedWordExpansionByCount_sum_eq_binaryWordFinStratum
        K (K * N) 12)
  have hzeroValue : stratum 0 = Matrix.trace (K ^ 12) := by
    simpa [stratum, K, N] using hzero
  calc
    Matrix.trace ((sgK m θ ax o + sgK m θ ax o * (sgGlue m).N) ^ 12) =
        ∑ r ∈ Finset.range 13, stratum r := by
          simpa [K, N] using hwords
    _ = stratum 0 + 0 + glueRHS12 m K := by
          rw [hsplit, hzeroSum, hoddSum, hevenSum]
    _ = Matrix.trace (K ^ 12) + glueRHS12 m K := by
          simpa [hzeroValue]
    _ = Matrix.trace (sgK m θ ax o ^ 12) +
          glueRHS12 m (sgK m θ ax o) := by
          rfl

/-- The full p=12 trace of the level-(m+1) operator is the sum of the
three child traces plus the positive-even boundary contribution. -/
theorem pOpO_trace12_glue_final
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k)
    (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (hanti : OAnti (m + 1) o) :
    Matrix.trace ((pOpO (m + 1) θ ax o) ^ 12) =
      (∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 12)) +
        glueRHS12 m (sgK m θ ax o) := by
  let K := sgK m θ ax o
  let N := (sgGlue m).N
  have hwords :
      Matrix.trace ((pOpO (m + 1) θ ax o) ^ 12) =
        ((orderedWordExpansion K (K * N) 12).map Matrix.trace).sum := by
    simpa [K, N] using
      (pOpO_succ_trace_ordered_words m θ ax o hax1 hax2 12 (by omega))
  have hordered :
      ((orderedWordExpansion K (K * N) 12).map Matrix.trace).sum =
        Matrix.trace (K ^ 12) + glueRHS12 m K := by
    rw [← trace_orderedWordExpansion K (K * N) 12]
    simpa [K, N] using
      (sg_trace_p12_ordered_expansion_boundary m hm θ ax o hanti)
  have hcopy :
      Matrix.trace (K ^ 12) =
        ∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 12) := by
    simpa [K, sgK] using (trace_blockK_pow (Hc m θ ax o) 12)
  calc
    Matrix.trace ((pOpO (m + 1) θ ax o) ^ 12) =
        ((orderedWordExpansion K (K * N) 12).map Matrix.trace).sum := hwords
    _ = Matrix.trace (K ^ 12) + glueRHS12 m K := hordered
    _ = (∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 12)) +
        glueRHS12 m K := by
      rw [hcopy]

/-- Twelfth-moment defect between two axis configurations at the same
level and orientation. -/
noncomputable def defectO12
    (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] : ℂ :=
  Matrix.trace ((pOpO m θ ax o) ^ 12) -
    Matrix.trace ((pOpO m θ ax' o) ^ 12)

theorem defectO12_congr
    (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o o' : Point → Point → Prop) [DecidableRel o] [DecidableRel o']
    (h : ∀ p q : Point, p ≠ q →
      EdgeB m p.1 p.2 q.1 q.2 = true →
      (if p ≤ q then (p, q) else (q, p)) ∈ fluxEdges m →
      (o p q ↔ o' p q)) :
    defectO12 m θ ax ax' o = defectO12 m θ ax ax' o' := by
  have e : ∀ b : ℕ → Axis, pOpO m θ b o = pOpO m θ b o' := by
    intro b
    funext x y
    exact pHeO_orient_congr m θ b o o' h x.1.1 y.1.1 x.2 y.2
  unfold defectO12
  rw [e ax, e ax']

/-- Exact recursion of the twelfth-moment axis defect under the three-copy
gluing. The positive-even p=12 contribution is kept as the boundary term. -/
theorem defectO12_succ
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ)
    (ax ax' : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k)
    (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (hax1' : ∀ k, ax' (3 ^ m + k) = ax' k)
    (hax2' : ∀ k, ax' (2 * 3 ^ m + k) = ax' k) :
    defectO12 (m + 1) θ ax ax' o =
      defectO12 m θ ax ax' o +
      defectO12 m θ ax ax' (oBo m o) +
      defectO12 m θ ax ax' (oCo m o) +
      (glueRHS12 m (sgK m θ ax o) -
        glueRHS12 m (sgK m θ ax' o)) := by
  have hA : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.A = pOpO m θ b o := fun _ => rfl
  have hB : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.B = pOpO m θ b (oBo m o) := fun _ => rfl
  have hC : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.C = pOpO m θ b (oCo m o) := fun _ => rfl
  unfold defectO12
  rw [pOpO_trace12_glue_final m hm θ ax o hax1 hax2 hanti,
    pOpO_trace12_glue_final m hm θ ax' o hax1' hax2' hanti]
  rw [sum_gcopy, sum_gcopy,
    hA ax, hA ax', hB ax, hB ax', hC ax, hC ax']
  ring


/-- Complete ordered p=12 trace expansion at level three. Odd strata vanish
using the degree-seven corner separation, while the positive-even strata are
retained in `glueRHS12` exactly as at higher levels. -/
theorem sg_trace_p12_ordered_expansion_boundary_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    Matrix.trace
      ((sgK m θ ax o + sgK m θ ax o * (sgGlue m).N) ^ 12) =
      Matrix.trace (sgK m θ ax o ^ 12) +
        glueRHS12 m (sgK m θ ax o) := by
  let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
  let N : Matrix (WSG m) (WSG m) ℂ := (sgGlue m).N
  let stratum (r : ℕ) : ℂ :=
    ∑ w : binaryWordFinStratum 12 r,
      Matrix.trace (binaryWordMatrix K (K * N) (List.ofFn w.val))
  have hzero := sg_trace_p12_zero_N_word_stratum m θ ax o
  have hodd := sg_trace_p12_all_odd_N_word_strata_zero_level3
    m hm θ ax o hanti
  have hsplit :
      (∑ r ∈ Finset.range 13, stratum r) =
        (∑ r ∈ Finset.range 13, if r = 0 then stratum r else 0) +
        (∑ r ∈ Finset.range 13,
          if r % 2 = 1 then stratum r else 0) +
        (∑ r ∈ Finset.range 13,
          if r % 2 = 0 ∧ 0 < r then stratum r else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hr0 : r = 0
    · subst r
      simp
    · by_cases hodd : r % 2 = 1
      · have hnotEven : ¬ (r % 2 = 0 ∧ 0 < r) := by omega
        simp [hr0, hodd, hnotEven]
      · have heven : r % 2 = 0 := by omega
        have hpos : 0 < r := by omega
        simp [hr0, hodd, heven, hpos]
  have hzeroSum :
      (∑ r ∈ Finset.range 13,
        if r = 0 then stratum r else 0) = stratum 0 := by
    simp
  have hoddSum :
      (∑ r ∈ Finset.range 13,
        if r % 2 = 1 then stratum r else 0) = 0 := by
    simpa [stratum, K, N] using hodd
  have hevenSum :
      (∑ r ∈ Finset.range 13,
        if r % 2 = 0 ∧ 0 < r then stratum r else 0) =
          glueRHS12 m K := by
    rfl
  have hwords :
      Matrix.trace ((K + K * N) ^ 12) =
        ∑ r ∈ Finset.range 13, stratum r := by
    simpa [stratum] using
      (trace_orderedWordExpansionByCount_sum_eq_binaryWordFinStratum
        K (K * N) 12)
  have hzeroValue : stratum 0 = Matrix.trace (K ^ 12) := by
    simpa [stratum, K, N] using hzero
  calc
    Matrix.trace ((sgK m θ ax o + sgK m θ ax o * (sgGlue m).N) ^ 12) =
        ∑ r ∈ Finset.range 13, stratum r := by
          simpa [K, N] using hwords
    _ = stratum 0 + 0 + glueRHS12 m K := by
          rw [hsplit, hzeroSum, hoddSum, hevenSum]
    _ = Matrix.trace (K ^ 12) + glueRHS12 m K := by
          rw [hzeroValue]
          simp
    _ = Matrix.trace (sgK m θ ax o ^ 12) +
          glueRHS12 m (sgK m θ ax o) := by
          rfl

/-- Full p=12 gluing identity at level three, with the positive-even
boundary contribution kept explicit. -/
theorem pOpO_trace12_glue_final_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k)
    (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (hanti : OAnti (m + 1) o) :
    Matrix.trace ((pOpO (m + 1) θ ax o) ^ 12) =
      (∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 12)) +
        glueRHS12 m (sgK m θ ax o) := by
  let K := sgK m θ ax o
  let N := (sgGlue m).N
  have hwords :
      Matrix.trace ((pOpO (m + 1) θ ax o) ^ 12) =
        ((orderedWordExpansion K (K * N) 12).map Matrix.trace).sum := by
    simpa [K, N] using
      (pOpO_succ_trace_ordered_words m θ ax o hax1 hax2 12 (by omega))
  have hordered :
      ((orderedWordExpansion K (K * N) 12).map Matrix.trace).sum =
        Matrix.trace (K ^ 12) + glueRHS12 m K := by
    rw [← trace_orderedWordExpansion K (K * N) 12]
    simpa [K, N] using
      (sg_trace_p12_ordered_expansion_boundary_level3 m hm θ ax o hanti)
  have hcopy :
      Matrix.trace (K ^ 12) =
        ∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 12) := by
    simpa [K, sgK] using (trace_blockK_pow (Hc m θ ax o) 12)
  calc
    Matrix.trace ((pOpO (m + 1) θ ax o) ^ 12) =
        ((orderedWordExpansion K (K * N) 12).map Matrix.trace).sum := hwords
    _ = Matrix.trace (K ^ 12) + glueRHS12 m K := hordered
    _ = (∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 12)) +
        glueRHS12 m K := by rw [hcopy]

/-- Twelfth-moment axis-defect recurrence at the level-three base step. -/
theorem defectO12_succ_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ)
    (ax ax' : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k)
    (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (hax1' : ∀ k, ax' (3 ^ m + k) = ax' k)
    (hax2' : ∀ k, ax' (2 * 3 ^ m + k) = ax' k) :
    defectO12 (m + 1) θ ax ax' o =
      defectO12 m θ ax ax' o +
      defectO12 m θ ax ax' (oBo m o) +
      defectO12 m θ ax ax' (oCo m o) +
      (glueRHS12 m (sgK m θ ax o) -
        glueRHS12 m (sgK m θ ax' o)) := by
  have hA : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.A = pOpO m θ b o := fun _ => rfl
  have hB : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.B = pOpO m θ b (oBo m o) := fun _ => rfl
  have hC : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.C = pOpO m θ b (oCo m o) := fun _ => rfl
  unfold defectO12
  rw [pOpO_trace12_glue_final_level3 m hm θ ax o hax1 hax2 hanti,
    pOpO_trace12_glue_final_level3 m hm θ ax' o hax1' hax2' hanti]
  rw [sum_gcopy, sum_gcopy,
    hA ax, hA ax', hB ax, hB ax', hC ax, hC ax']
  ring

end EvgenyTheorem
