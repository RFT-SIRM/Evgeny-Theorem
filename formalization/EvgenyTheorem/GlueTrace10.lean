import EvgenyTheorem.GlueTrace

namespace EvgenyTheorem

/-- Assembly of the exact p=10 expansion: the zero-insertion stratum gives
`Tr K^10`, all odd strata vanish, and the positive-even strata sum to
`glueRHS10`. -/
theorem sg_trace_p10_ordered_expansion_boundary
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    Matrix.trace
      ((sgK m θ ax o + sgK m θ ax o * (sgGlue m).N) ^ 10) =
      Matrix.trace (sgK m θ ax o ^ 10) + glueRHS10 m (sgK m θ ax o) := by
  have h0 := sg_trace_p10_zero_N_word_stratum m θ ax o
  have h1 := sg_trace_p10_one_N_word_stratum_zero m θ ax o
  have h3 := sg_trace_p10_three_N_word_stratum_zero m (by omega) θ ax o hanti
  have h5 := sg_trace_p10_five_N_word_stratum_zero m (by omega) θ ax o hanti
  have h7 := sg_trace_p10_seven_N_word_stratum_zero m (by omega) θ ax o hanti
  have h9 := sg_trace_p10_nine_N_word_stratum_zero m (by omega) θ ax o hanti
  have heven := sg_trace_p10_even_N_word_strata_diagonal m hm θ ax o hanti
  rw [trace_orderedWordExpansionByCount_sum_eq_binaryWordFinStratum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linear_combination h0 + h1 + h3 + h5 + h7 + h9 + heven

theorem pOpO_trace10_glue_final
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k)
    (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (hanti : OAnti (m + 1) o) :
    Matrix.trace ((pOpO (m + 1) θ ax o) ^ 10) =
      (∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 10)) +
        glueRHS10 m (sgK m θ ax o) := by
  let K := sgK m θ ax o
  let N := (sgGlue m).N
  have hwords :
      Matrix.trace ((pOpO (m + 1) θ ax o) ^ 10) =
        ((orderedWordExpansion K (K * N) 10).map Matrix.trace).sum := by
    simpa [K, N] using
      (pOpO_succ_trace_ordered_words m θ ax o hax1 hax2 10 (by omega))
  have hordered :
      ((orderedWordExpansion K (K * N) 10).map Matrix.trace).sum =
        Matrix.trace (K ^ 10) + glueRHS10 m K := by
    rw [← trace_orderedWordExpansion K (K * N) 10]
    simpa [K, N] using
      (sg_trace_p10_ordered_expansion_boundary m hm θ ax o hanti)
  have hcopy :
      Matrix.trace (K ^ 10) =
        ∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 10) := by
    simpa [K, sgK] using (trace_blockK_pow (Hc m θ ax o) 10)
  calc
    Matrix.trace ((pOpO (m + 1) θ ax o) ^ 10) =
        ((orderedWordExpansion K (K * N) 10).map Matrix.trace).sum := hwords
    _ = Matrix.trace (K ^ 10) + glueRHS10 m K := hordered
    _ = (∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 10)) +
        glueRHS10 m K := by
      rw [hcopy]

/-- Tenth-moment defect between two axis configurations at the same
level and orientation. -/
noncomputable def defectO10
    (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] : ℂ :=
  Matrix.trace ((pOpO m θ ax o) ^ 10) -
    Matrix.trace ((pOpO m θ ax' o) ^ 10)

theorem defectO10_congr
    (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o o' : Point → Point → Prop) [DecidableRel o] [DecidableRel o']
    (h : ∀ p q : Point, p ≠ q →
      EdgeB m p.1 p.2 q.1 q.2 = true →
      (if p ≤ q then (p, q) else (q, p)) ∈ fluxEdges m →
      (o p q ↔ o' p q)) :
    defectO10 m θ ax ax' o = defectO10 m θ ax ax' o' := by
  have e : ∀ b : ℕ → Axis, pOpO m θ b o = pOpO m θ b o' := by
    intro b
    funext x y
    exact pHeO_orient_congr m θ b o o' h x.1.1 y.1.1 x.2 y.2
  unfold defectO10
  rw [e ax, e ax']

/-- Exact level recursion for the tenth-moment axis defect. -/
theorem defectO10_succ
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ)
    (ax ax' : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k)
    (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (hax1' : ∀ k, ax' (3 ^ m + k) = ax' k)
    (hax2' : ∀ k, ax' (2 * 3 ^ m + k) = ax' k) :
    defectO10 (m + 1) θ ax ax' o =
      defectO10 m θ ax ax' o +
      defectO10 m θ ax ax' (oBo m o) +
      defectO10 m θ ax ax' (oCo m o) +
      (glueRHS10 m (sgK m θ ax o) -
        glueRHS10 m (sgK m θ ax' o)) := by
  have hA : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.A = pOpO m θ b o := fun _ => rfl
  have hB : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.B = pOpO m θ b (oBo m o) := fun _ => rfl
  have hC : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.C = pOpO m θ b (oCo m o) := fun _ => rfl
  unfold defectO10
  rw [pOpO_trace10_glue_final m hm θ ax o hax1 hax2 hanti,
    pOpO_trace10_glue_final m hm θ ax' o hax1' hax2' hanti]
  rw [sum_gcopy, sum_gcopy,
    hA ax, hA ax', hB ax, hB ax', hC ax, hC ax']
  ring

end EvgenyTheorem
