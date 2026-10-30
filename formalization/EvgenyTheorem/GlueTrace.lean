import EvgenyTheorem.GlueCorner

/-!
# Trace splitting and the defect recursion over arbitrary orientations

* `trace_blockK_pow4`: `tr (blockK H)^4 = Σ_c tr (H c)^4`.
* `cornerTerm`: the three glued-corner sums of `glueRHS`.
* `trace4_split`: `tr (H_{m+1})^4 = Σ_c tr (Hc c)^4 + cornerTerm`.
* `defectO`: trace defect for an arbitrary orientation.
* `defectO_succ`: `D(m+1,o) = D(m,o) + D(m,oBo o) + D(m,oCo o)`, assuming that the corner data
  of `K` do not depend on the axis function (`hcorner`, the remaining geometric fact).
-/

namespace EvgenyTheorem

open Matrix

section Block

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]

theorem blockK_mul (H G : ι → Matrix X X ℂ) :
    blockK H * blockK G = blockK (fun c => H c * G c) := by
  classical
  ext w w'
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hc : w.1 = w'.1
  · have e : blockK (fun c => H c * G c) w w' = (H w.1 * G w.1) w.2 w'.2 := by
      simp [blockK, hc]
    rw [e, Matrix.mul_apply, Finset.sum_eq_single w.1]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      simp [blockK, hc]
    · intro c _ hne
      refine Finset.sum_eq_zero (fun y _ => ?_)
      have : w.1 ≠ c := fun h => hne h.symm
      simp [blockK, this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have e : blockK (fun c => H c * G c) w w' = 0 := by simp [blockK, hc]
    rw [e]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    refine Finset.sum_eq_zero (fun y _ => ?_)
    by_cases h1 : w.1 = c
    · have : c ≠ w'.1 := fun h => hc (h1.trans h)
      simp [blockK, this]
    · simp [blockK, h1]

theorem trace_blockK (H : ι → Matrix X X ℂ) :
    Matrix.trace (blockK H) = ∑ c, Matrix.trace (H c) := by
  classical
  rw [Matrix.trace, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp [Matrix.trace, Matrix.diag, blockK]

/-- Powers of a block-diagonal matrix are computed independently in each block. -/
theorem blockK_pow (H : ι → Matrix X X ℂ) (n : ℕ) :
    blockK H ^ n = blockK (fun c => H c ^ n) := by
  classical
  induction n with
  | zero =>
      ext ⟨i, x⟩ ⟨j, y⟩
      by_cases hij : i = j <;> by_cases hxy : x = y <;>
        simp [blockK, hij, hxy]
  | succ n ih =>
      rw [pow_succ, ih, blockK_mul]
      exact congrArg blockK (funext fun c => by rw [pow_succ])

/-- The trace of any natural power of a block-diagonal matrix is the sum of block traces. -/
theorem trace_blockK_pow (H : ι → Matrix X X ℂ) (n : ℕ) :
    Matrix.trace (blockK H ^ n) = ∑ c, Matrix.trace (H c ^ n) := by
  rw [blockK_pow, trace_blockK]

/-- Recursive noncommutative expansion of a power of a sum.
The recurrence appends either factor on the right, so it preserves matrix order. -/
def addWordSum {X : Type*} [Fintype X] [DecidableEq X]
    (D E : Matrix X X ℂ) : ℕ → Matrix X X ℂ
  | 0 => 1
  | n + 1 => addWordSum D E n * D + addWordSum D E n * E

/-- The recursive word sum equals the power of the sum, without assuming commutativity. -/
theorem add_pow_eq_addWordSum {X : Type*} [Fintype X] [DecidableEq X]
    (D E : Matrix X X ℂ) (n : ℕ) :
    (D + E) ^ n = addWordSum D E n := by
  induction n with
  | zero => simp [addWordSum]
  | succ n ih =>
      rw [pow_succ, ih, addWordSum, mul_add]

/-- Explicit degree-three expansion, retaining the order of all eight words. -/
theorem addWordSum_three {X : Type*} [Fintype X] [DecidableEq X]
    (D E : Matrix X X ℂ) :
    addWordSum D E 3 =
      D * D * D + E * D * D + D * E * D + E * E * D +
        D * D * E + E * D * E + D * E * E + E * E * E := by
  simp [addWordSum, add_mul, mul_add, add_assoc, add_comm, add_left_comm]

/-- Explicit degree-two expansion. The four ordered products are retained. -/
theorem addWordSum_two {X : Type*} [Fintype X] [DecidableEq X]
    (D E : Matrix X X ℂ) :
    addWordSum D E 2 = D * D + E * D + D * E + E * E := by
  simp [addWordSum, add_mul, mul_add, add_assoc, add_comm, add_left_comm]

set_option maxHeartbeats 800000 in
/-- Explicit degree-four expansion into all sixteen ordered words. -/
theorem addWordSum_four {X : Type*} [Fintype X] [DecidableEq X]
    (D E : Matrix X X ℂ) :
    addWordSum D E 4 =
      D * D * D * D + E * D * D * D + D * E * D * D + E * E * D * D +
      D * D * E * D + E * D * E * D + D * E * E * D + E * E * E * D +
      D * D * D * E + E * D * D * E + D * E * D * E + E * E * D * E +
      D * D * E * E + E * D * E * E + D * E * E * E + E * E * E * E := by
  simp [addWordSum, add_mul, mul_add, add_assoc, add_comm, add_left_comm]

/-- The trace recurrence exposes the two ordered extensions of each word. -/
theorem trace_addWordSum_succ {X : Type*} [Fintype X] [DecidableEq X]
    (D E : Matrix X X ℂ) (n : ℕ) :
    Matrix.trace (addWordSum D E (n + 1)) =
      Matrix.trace (addWordSum D E n * D) +
        Matrix.trace (addWordSum D E n * E) := by
  rw [addWordSum, Matrix.trace_add]

/-- Trace-level form of the recursive noncommutative expansion. -/
theorem trace_add_pow_eq_addWordSum {X : Type*} [Fintype X] [DecidableEq X]
    (D E : Matrix X X ℂ) (n : ℕ) :
    Matrix.trace ((D + E) ^ n) = Matrix.trace (addWordSum D E n) := by
  rw [add_pow_eq_addWordSum]

/-- Degree-four regression form: the recursive expansion preserves the exact
matrix power, so its trace agrees with the existing fourth-power expression. -/
theorem trace_add_pow_four_eq_addWordSum {X : Type*} [Fintype X] [DecidableEq X]
    (D E : Matrix X X ℂ) :
    Matrix.trace ((D + E) ^ 4) = Matrix.trace (addWordSum D E 4) := by
  exact trace_add_pow_eq_addWordSum D E 4

theorem trace_blockK_pow4 (H : ι → Matrix X X ℂ) :
    Matrix.trace (blockK H * blockK H * blockK H * blockK H) =
      ∑ c, Matrix.trace (H c * H c * H c * H c) := by
  classical
  rw [blockK_mul, blockK_mul, blockK_mul, trace_blockK]

end Block

/-! ### Corner term -/

/-- The three glued-corner sums of `glueRHS`. -/
noncomputable def cornerTerm (m : ℕ) (K : Matrix (WSG m) (WSG m) ℂ) : ℂ :=
  4 * ∑ a, (if (sgGlue m).g a then (K * K * K) a a * K ((sgGlue m).σ a) ((sgGlue m).σ a)
      else 0) +
    2 * ∑ a, (if (sgGlue m).g a then (K * K) a a * (K * K) ((sgGlue m).σ a) ((sgGlue m).σ a)
      else 0) +
    ∑ a, (if (sgGlue m).g a then K a a * K a a * (K ((sgGlue m).σ a) ((sgGlue m).σ a) *
      K ((sgGlue m).σ a) ((sgGlue m).σ a)) else 0)

/-- Equal corner data give equal corner terms. -/
theorem cornerTerm_congr (m : ℕ) (K K' : Matrix (WSG m) (WSG m) ℂ)
    (h : ∀ a, (sgGlue m).g a →
      (K * K * K) a a = (K' * K' * K') a a ∧ (K * K) a a = (K' * K') a a ∧
        K a a = K' a a) :
    cornerTerm m K = cornerTerm m K' := by
  have e1 : ∀ a, (if (sgGlue m).g a then
        (K * K * K) a a * K ((sgGlue m).σ a) ((sgGlue m).σ a) else 0) =
      (if (sgGlue m).g a then
        (K' * K' * K') a a * K' ((sgGlue m).σ a) ((sgGlue m).σ a) else 0) := by
    intro a
    by_cases ha : (sgGlue m).g a
    · obtain ⟨h3, _, _⟩ := h a ha
      obtain ⟨_, _, h1σ⟩ := h _ ((sgGlue m).g_σ a ha)
      rw [if_pos ha, if_pos ha, h3, h1σ]
    · rw [if_neg ha, if_neg ha]
  have e2 : ∀ a, (if (sgGlue m).g a then
        (K * K) a a * (K * K) ((sgGlue m).σ a) ((sgGlue m).σ a) else 0) =
      (if (sgGlue m).g a then
        (K' * K') a a * (K' * K') ((sgGlue m).σ a) ((sgGlue m).σ a) else 0) := by
    intro a
    by_cases ha : (sgGlue m).g a
    · obtain ⟨_, h2, _⟩ := h a ha
      obtain ⟨_, h2σ, _⟩ := h _ ((sgGlue m).g_σ a ha)
      rw [if_pos ha, if_pos ha, h2, h2σ]
    · rw [if_neg ha, if_neg ha]
  have e3 : ∀ a, (if (sgGlue m).g a then K a a * K a a * (K ((sgGlue m).σ a) ((sgGlue m).σ a) *
        K ((sgGlue m).σ a) ((sgGlue m).σ a)) else 0) =
      (if (sgGlue m).g a then K' a a * K' a a * (K' ((sgGlue m).σ a) ((sgGlue m).σ a) *
        K' ((sgGlue m).σ a) ((sgGlue m).σ a)) else 0) := by
    intro a
    by_cases ha : (sgGlue m).g a
    · obtain ⟨_, _, h1⟩ := h a ha
      obtain ⟨_, _, h1σ⟩ := h _ ((sgGlue m).g_σ a ha)
      rw [if_pos ha, if_pos ha, h1, h1σ]
    · rw [if_neg ha, if_neg ha]
  unfold cornerTerm
  rw [Finset.sum_congr rfl (fun a _ => e1 a), Finset.sum_congr rfl (fun a _ => e2 a),
    Finset.sum_congr rfl (fun a _ => e3 a)]

/-! ### Splitting the trace -/

theorem trace4_split (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (hanti : OAnti (m + 1) o)
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k) (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k) :
    Matrix.trace (pOpO (m + 1) θ ax o * pOpO (m + 1) θ ax o * pOpO (m + 1) θ ax o *
        pOpO (m + 1) θ ax o) =
      ∑ c, Matrix.trace (Hc m θ ax o c * Hc m θ ax o c * Hc m θ ax o c * Hc m θ ax o c) +
        cornerTerm m (sgK m θ ax o) := by
  rw [pOpO_trace4_glue_final m hm θ ax o hanti hax1 hax2]
  have h4 : Matrix.trace (sgK m θ ax o * sgK m θ ax o * sgK m θ ax o * sgK m θ ax o) =
      ∑ c, Matrix.trace (Hc m θ ax o c * Hc m θ ax o c * Hc m θ ax o c * Hc m θ ax o c) :=
    trace_blockK_pow4 (Hc m θ ax o)
  unfold glueRHS cornerTerm
  rw [h4]
  ring

/-! ### Defect for an arbitrary orientation -/

noncomputable def defectO (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] : ℂ :=
  Matrix.trace (pOpO m θ ax o * pOpO m θ ax o * pOpO m θ ax o * pOpO m θ ax o) -
    Matrix.trace (pOpO m θ ax' o * pOpO m θ ax' o * pOpO m θ ax' o * pOpO m θ ax' o)

/-- The usual trace defect is `defectO` for the numbering orientation. -/
theorem traceDefect_eq_defectO (m : ℕ) (θ : ℝ) :
    traceDefect m θ =
      defectO m θ faceAxis (fun _ => 2) (fun p q => vIdx m p ≤ vIdx m q) := by
  rw [traceDefect_pt]
  unfold defectO
  rw [pOp_eq_pOpO, pOp_eq_pOpO]

/-- `defectO` depends on the orientation only through its values on flux edges. -/
theorem defectO_congr (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis) (o o' : Point → Point → Prop)
    [DecidableRel o] [DecidableRel o']
    (h : ∀ p q : Point, p ≠ q → EdgeB m p.1 p.2 q.1 q.2 = true →
      (if p ≤ q then (p, q) else (q, p)) ∈ fluxEdges m → (o p q ↔ o' p q)) :
    defectO m θ ax ax' o = defectO m θ ax ax' o' := by
  have e : ∀ b : ℕ → Axis, pOpO m θ b o = pOpO m θ b o' := by
    intro b
    funext x y
    exact pHeO_orient_congr m θ b o o' h x.1.1 y.1.1 x.2 y.2
  unfold defectO
  rw [e ax, e ax']

/-- **Recursion of the defect over orientations.**  `hcorner` is the remaining geometric fact:
the diagonal entries of `K`, `K²`, `K³` at glued corners do not depend on the axis function. -/
theorem defectO_succ (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] (hanti : OAnti (m + 1) o)
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k) (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (hax1' : ∀ k, ax' (3 ^ m + k) = ax' k) (hax2' : ∀ k, ax' (2 * 3 ^ m + k) = ax' k)
    (hcorner : ∀ a, (sgGlue m).g a →
      (sgK m θ ax o * sgK m θ ax o * sgK m θ ax o) a a =
          (sgK m θ ax' o * sgK m θ ax' o * sgK m θ ax' o) a a ∧
        (sgK m θ ax o * sgK m θ ax o) a a = (sgK m θ ax' o * sgK m θ ax' o) a a ∧
        sgK m θ ax o a a = sgK m θ ax' o a a) :
    defectO (m + 1) θ ax ax' o =
      defectO m θ ax ax' o + defectO m θ ax ax' (oBo m o) + defectO m θ ax ax' (oCo m o) := by
  have hA : ∀ b : ℕ → Axis, Hc m θ b o GCopy.A = pOpO m θ b o := fun _ => rfl
  have hB : ∀ b : ℕ → Axis, Hc m θ b o GCopy.B = pOpO m θ b (oBo m o) := fun _ => rfl
  have hC : ∀ b : ℕ → Axis, Hc m θ b o GCopy.C = pOpO m θ b (oCo m o) := fun _ => rfl
  unfold defectO
  rw [trace4_split m hm θ ax o hanti hax1 hax2, trace4_split m hm θ ax' o hanti hax1' hax2',
    cornerTerm_congr m (sgK m θ ax o) (sgK m θ ax' o) hcorner, sum_gcopy, sum_gcopy,
    hA ax, hA ax', hB ax, hB ax', hC ax, hC ax']
  ring


/-- The one-N cyclic class in the p=6 ordered expansion vanishes.
The single pairing factor is moved cyclically between powers of the block-diagonal
kernel; no commutation of K with N is used. -/
theorem sg_trace_p6_one_N_class_zero
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N * sgK m θ ax o ^ 5) = 0 := by
  exact trace_pow_N_pow_zero (sgGlue m) (sgK m θ ax o)
    (blockK_BD (Hc m θ ax o)) 1 5


/-- Every p=6 ordered word with three pairing insertions vanishes.
The middle K-run has length at most five, so the geometric corner-vanishing
lemma for powers through degree five supplies the hypothesis of the generic
three-N trace reduction. This is a word-level fact; the cyclic census and its
multiplicities are handled separately. -/
theorem sg_trace_p6_three_N_word_zero
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d : ℕ) (hb : b < 6) :
    Matrix.trace
      (sgK m θ ax o ^ a * (sgGlue m).N *
        sgK m θ ax o ^ b * (sgGlue m).N *
        sgK m θ ax o ^ c * (sgGlue m).N *
        sgK m θ ax o ^ d) = 0 := by
  apply trace_three_N_powers (sgGlue m) (sgK m θ ax o)
    (blockK_BD (Hc m θ ax o)) a b c d
  intro w w' hw hw' hcopy hne
  exact sgK_pow_hkg_up_to_five_of_OAnti m hm θ ax o hanti
    b (by omega) w w' hw hw' hcopy hne


/-- Every p=6 ordered word with five pairing insertions vanishes.
The two powers selected by the five-N reduction are both below six, hence
the existing geometric corner-support result applies. The outer powers are
unrestricted and remain in their original order. -/
theorem sg_trace_p6_five_N_word_zero
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d e f : ℕ) (hb : b < 6) (hd : d < 6) :
    Matrix.trace
      (sgK m θ ax o ^ a * (sgGlue m).N *
        sgK m θ ax o ^ b * (sgGlue m).N *
        sgK m θ ax o ^ c * (sgGlue m).N *
        sgK m θ ax o ^ d * (sgGlue m).N *
        sgK m θ ax o ^ e * (sgGlue m).N *
        sgK m θ ax o ^ f) = 0 := by
  apply trace_five_N_powers_zero (sgGlue m) (sgK m θ ax o)
    (blockK_BD (Hc m θ ax o)) a b c d e f
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_five_of_OAnti m hm θ ax o hanti
      b (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_five_of_OAnti m hm θ ax o hanti
      d (by omega) w w' hw hw' hcopy hne


/-- The four cyclic representatives of the p=6 three-N stratum have
vanishing traces. Their orbit weights are 6, 6, 6, and 2; the last
representative is periodic with period two. This packages the representative
calculation, but does not yet identify it with the full ordered expansion. -/
theorem sg_trace_p6_three_N_representatives_zero
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    6 * Matrix.trace
      (sgK m θ ax o ^ 4 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N) +
    2 * Matrix.trace
      (sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N) = 0 := by
  have h1 := sg_trace_p6_three_N_word_zero m hm θ ax o hanti
    4 1 1 0 (by omega)
  have h2 := sg_trace_p6_three_N_word_zero m hm θ ax o hanti
    3 2 1 0 (by omega)
  have h3 := sg_trace_p6_three_N_word_zero m hm θ ax o hanti
    3 1 2 0 (by omega)
  have h4 := sg_trace_p6_three_N_word_zero m hm θ ax o hanti
    2 2 2 0 (by omega)
  have h1' : Matrix.trace
      (sgK m θ ax o ^ 4 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N) = 0 := by
    simpa [pow_one, pow_zero] using h1
  have h2' : Matrix.trace
      (sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N) = 0 := by
    simpa [pow_one, pow_zero] using h2
  have h3' : Matrix.trace
      (sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N) = 0 := by
    simpa [pow_one, pow_zero] using h3
  have h4' : Matrix.trace
      (sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N) = 0 := by
    simpa [pow_one, pow_zero] using h4
  rw [h1', h2', h3', h4']
  ring


/-- The representative-level odd-N strata at p=6 all vanish after
their cyclic orbit weights are applied. This combines r=1, r=3, and r=5;
the full ordered-expansion partition is a separate remaining theorem. -/
theorem sg_trace_p6_odd_N_representatives_zero
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    6 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N * sgK m θ ax o ^ 5) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 4 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N) +
    2 * Matrix.trace
      (sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 0) = 0 := by
  have h1 := sg_trace_p6_one_N_class_zero m θ ax o
  have h3 := sg_trace_p6_three_N_representatives_zero m hm θ ax o hanti
  have h5 := sg_trace_p6_five_N_word_zero m hm θ ax o hanti
    2 1 1 1 1 0 (by omega) (by omega)
  have h1' : Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N * sgK m θ ax o ^ 5) = 0 := by
    simpa [pow_one] using h1
  have h3' := h3
  have h5' : Matrix.trace
      (sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 0) = 0 := by
    simpa [pow_one] using h5
  rw [h1', h5']
  simpa only [mul_zero, zero_add, add_zero] using h3'


/-- The one-N cyclic representative in the ordered p=6 word expansion is
the same trace as the already-vanishing boundary representative. This bridges
only this single cyclic class; it does not claim the full trace split. -/
theorem sg_trace_p6_ordered_one_N_class_zero
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    Matrix.trace
      (sgK m θ ax o ^ 5 * (sgK m θ ax o * (sgGlue m).N)) = 0 := by
  calc
    Matrix.trace
        (sgK m θ ax o ^ 5 * (sgK m θ ax o * (sgGlue m).N)) =
      Matrix.trace
        ((sgK m θ ax o * (sgGlue m).N) * sgK m θ ax o ^ 5) := by
          exact Matrix.trace_mul_comm _ _
    _ = 0 := by
          simpa [pow_one] using
            sg_trace_p6_one_N_class_zero m θ ax o


/-- The ordered cyclic representative with two pairing insertions and K-gap
pattern (5,1) is exactly the corresponding lower-even boundary trace after a
cyclic rotation. This is one class-level bridge, not the complete p=6 split. -/
theorem sg_trace_p6_ordered_two_N_5_1_representative
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    Matrix.trace
      (sgK m θ ax o * sgK m θ ax o *
        sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N)) =
    Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 5 * (sgGlue m).N *
        sgK m θ ax o ^ 0) := by
  simpa [pow_succ, pow_one, pow_zero, Matrix.mul_assoc] using
    (trace_cyclic_list
      ([sgK m θ ax o, sgK m θ ax o, sgK m θ ax o,
        sgK m θ ax o, sgK m θ ax o, (sgGlue m).N] :
        List (Matrix (WSG m) (WSG m) ℂ))
      [sgK m θ ax o, (sgGlue m).N])


/-- The ordered cyclic representative with two pairing insertions and K-gap
pattern (4,2) is the corresponding lower-even boundary trace after a cyclic
rotation. This bridges one cyclic class only; it does not claim the full p=6
trace split. -/
theorem sg_trace_p6_ordered_two_N_4_2_representative
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    Matrix.trace
      (sgK m θ ax o * sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N)) =
    Matrix.trace
      (sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 4 * (sgGlue m).N *
        sgK m θ ax o ^ 0) := by
  simpa [pow_succ, pow_one, pow_zero, Matrix.mul_assoc] using
    (trace_cyclic_list
      ([sgK m θ ax o, sgK m θ ax o, sgK m θ ax o,
        sgK m θ ax o, (sgGlue m).N] :
        List (Matrix (WSG m) (WSG m) ℂ))
      [sgK m θ ax o, sgK m θ ax o, (sgGlue m).N])


/-- The periodic two-pairing representative with equal K-gaps (3,3)
is exactly the corresponding lower-even boundary trace. The six-choice word
has orbit weight three; this lemma bridges only that representative. -/
theorem sg_trace_p6_ordered_two_N_3_3_representative
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    Matrix.trace
      (sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N)) =
    Matrix.trace
      (sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 0) := by
  simpa [pow_succ, pow_zero, Matrix.mul_assoc]


/-- The three cyclic classes in the p=6 two-insertion stratum, with
orbit weights 6, 6, and 3, give exactly the first three lower-even boundary
trace terms. This is the representative sum, not the full 64-word partition. -/
theorem sg_trace_p6_ordered_two_N_representatives_boundary
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    6 * Matrix.trace
      (sgK m θ ax o * sgK m θ ax o *
        sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N)) +
    6 * Matrix.trace
      (sgK m θ ax o * sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N)) +
    3 * Matrix.trace
      (sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N)) =
    6 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 5 * (sgGlue m).N *
        sgK m θ ax o ^ 0) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 4 * (sgGlue m).N *
        sgK m θ ax o ^ 0) +
    3 * Matrix.trace
      (sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 0) := by
  rw [sg_trace_p6_ordered_two_N_5_1_representative m θ ax o,
    sg_trace_p6_ordered_two_N_4_2_representative m θ ax o,
    sg_trace_p6_ordered_two_N_3_3_representative m θ ax o]


/-- The r=4 cyclic representative with K-gap pattern (1,1,1,3)
is the corresponding lower-even boundary trace after a cyclic rotation.
This bridges one representative only; it does not claim the full r=4 stratum. -/
theorem sg_trace_p6_ordered_four_N_1_1_1_3_representative
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    Matrix.trace
      (sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N)) =
    Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 0) := by
  simpa [pow_succ, pow_one, pow_zero, Matrix.mul_assoc] using
    (trace_cyclic_list
      ([sgK m θ ax o, sgK m θ ax o, sgK m θ ax o, (sgGlue m).N] :
        List (Matrix (WSG m) (WSG m) ℂ))
      [sgK m θ ax o, (sgGlue m).N,
        sgK m θ ax o, (sgGlue m).N,
        sgK m θ ax o, (sgGlue m).N])


/-- The r=4 ordered representative with K-gap pattern (1,1,2,2)
is the corresponding lower-even boundary trace after expanding the six choices.
This bridges one representative only; it does not claim the full r=4 stratum. -/
theorem sg_trace_p6_ordered_four_N_1_1_2_2_representative
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    Matrix.trace
      ((sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N)) =
    Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 0) := by
  simpa [pow_succ, pow_one, pow_zero, Matrix.mul_assoc]


/-- The periodic r=4 representative with K-gap pattern (1,2,1,2)
is the corresponding lower-even boundary trace. Its choice word has orbit
weight three; this does not claim the full r=4 stratum. -/
theorem sg_trace_p6_ordered_four_N_1_2_1_2_representative
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    Matrix.trace
      ((sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N)) =
    Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 0) := by
  simpa [pow_succ, pow_one, pow_zero, Matrix.mul_assoc]


/-- The three cyclic classes in the p=6 r=4 stratum, with orbit
weights 6, 6, and 3, give exactly the last three lower-even boundary trace
terms. This sums the representatives only; it is not the full 64-word split. -/
theorem sg_trace_p6_ordered_four_N_representatives_boundary
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    6 * Matrix.trace
      (sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N)) +
    6 * Matrix.trace
      ((sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N)) +
    3 * Matrix.trace
      ((sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N)) =
    6 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 3 * (sgGlue m).N *
        sgK m θ ax o ^ 0) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 0) +
    3 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 0) := by
  rw [sg_trace_p6_ordered_four_N_1_1_1_3_representative m θ ax o,
    sg_trace_p6_ordered_four_N_1_1_2_2_representative m θ ax o,
    sg_trace_p6_ordered_four_N_1_2_1_2_representative m θ ax o]


/-- The four r=3 cyclic representatives from the generic p=6 expansion
become the four already-proved three-N representatives after substituting
A=K and B=K*N. Their orbit weights are 6, 6, 6, and 2. This bridges that
stratum only. -/
theorem sg_trace_p6_ordered_three_N_representatives_zero
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    6 * Matrix.trace
      (sgK m θ ax o * sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N)) +
    6 * Matrix.trace
      (sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N)) +
    6 * Matrix.trace
      (sgK m θ ax o * sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N)) +
    2 * Matrix.trace
      (sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N) *
        sgK m θ ax o *
        (sgK m θ ax o * (sgGlue m).N)) = 0 := by
  simpa [pow_succ, pow_one, pow_zero, Matrix.mul_assoc] using
    (sg_trace_p6_three_N_representatives_zero m hm θ ax o hanti)


/-- End-to-end p=6 cyclic trace assembly. It retains the K^6 and (K*N)^6
endpoints, vanishes all odd-insertion classes, and rewrites the r=2 and r=4
classes to the existing lower-even boundary traces. This is not a level-
induction or a p=8/p=10 result. -/
theorem sg_trace_p6_ordered_expansion_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K := sgK m θ ax o
    let N := (sgGlue m).N
    ((orderedWordExpansion K (K * N) 6).map Matrix.trace).sum =
      Matrix.trace (K ^ 6) +
      6 * Matrix.trace (K ^ 1 * N * K ^ 5 * N * K ^ 0) +
      6 * Matrix.trace (K ^ 2 * N * K ^ 4 * N * K ^ 0) +
      3 * Matrix.trace (K ^ 3 * N * K ^ 3 * N * K ^ 0) +
      6 * Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 3 * N * K ^ 0) +
      6 * Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 2 * N * K ^ 2 * N * K ^ 0) +
      3 * Matrix.trace (K ^ 1 * N * K ^ 2 * N * K ^ 1 * N * K ^ 2 * N * K ^ 0) +
      Matrix.trace ((K * N) ^ 6) := by
  dsimp only
  let K := sgK m θ ax o
  let N := (sgGlue m).N
  rw [trace_orderedWordExpansion_six_cyclic K (K * N)]
  have h1 :
      Matrix.trace (K * K * K * K * K * (K * N)) = 0 := by
    simpa [pow_succ, Matrix.mul_assoc] using
      (sg_trace_p6_ordered_one_N_class_zero m θ ax o)
  have h2 := sg_trace_p6_ordered_two_N_representatives_boundary m θ ax o
  have h3 := sg_trace_p6_ordered_three_N_representatives_zero
    m hm θ ax o hanti
  have h4 := sg_trace_p6_ordered_four_N_representatives_boundary m θ ax o
  have h5 :
      Matrix.trace (K * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) = 0 := by
    simpa [pow_succ, pow_one, pow_zero, Matrix.mul_assoc] using
      (sg_trace_p6_five_N_word_zero m hm θ ax o hanti
        2 1 1 1 1 0 (by omega) (by omega))
  have hrot4b :
      Matrix.trace (K * (K * N) * K * (K * N) * (K * N) * (K * N)) =
      Matrix.trace ((K * N) * (K * N) * K * (K * N) * K * (K * N)) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list
        ([K, K * N, K, K * N] : List (Matrix (WSG m) (WSG m) ℂ))
        [K * N, K * N])
  have hrot4c :
      Matrix.trace (K * (K * N) * (K * N) * K * (K * N) * (K * N)) =
      Matrix.trace ((K * N) * K * (K * N) * (K * N) * K * (K * N)) := by
    simpa [Matrix.mul_assoc] using
      (trace_cyclic_list
        ([K, K * N] : List (Matrix (WSG m) (WSG m) ℂ))
        [K * N, K, K * N, K * N])
  have hK : Matrix.trace (K * K * K * K * K * K) = Matrix.trace (K ^ 6) := by
    simp [pow_succ, Matrix.mul_assoc]
  have hN : Matrix.trace
      ((K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) =
      Matrix.trace ((K * N) ^ 6) := by
    simp [pow_succ, Matrix.mul_assoc]
  linear_combination hK + 6 * h1 + h2 + h3 + h4 + 6 * h5 +
    6 * hrot4b + 3 * hrot4c + hN


/-- Concrete p=6 lower-even-strata reduction for the Sierpinski glued
operator. This discharges the abstract power-support premise from the
geometric corner theorem, for m ≥ 3 and orientation-antisymmetric o. -/
theorem sg_trace_p6_lower_even_strata_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    6 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N * sgK m θ ax o ^ 5 *
        (sgGlue m).N * sgK m θ ax o ^ 0) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 2 * (sgGlue m).N * sgK m θ ax o ^ 4 *
        (sgGlue m).N * sgK m θ ax o ^ 0) +
    3 * Matrix.trace
      (sgK m θ ax o ^ 3 * (sgGlue m).N * sgK m θ ax o ^ 3 *
        (sgGlue m).N * sgK m θ ax o ^ 0) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N * sgK m θ ax o ^ 1 *
        (sgGlue m).N * sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 3 * (sgGlue m).N * sgK m θ ax o ^ 0) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N * sgK m θ ax o ^ 1 *
        (sgGlue m).N * sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N * sgK m θ ax o ^ 0) +
    3 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N * sgK m θ ax o ^ 2 *
        (sgGlue m).N * sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N * sgK m θ ax o ^ 0) =
    6 * (∑ x, if (sgGlue m).g x then
      (sgK m θ ax o ^ 1) x x *
      (sgK m θ ax o ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    6 * (∑ x, if (sgGlue m).g x then
      (sgK m θ ax o ^ 2) x x * (sgK m θ ax o ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    3 * (∑ x, if (sgGlue m).g x then
      (sgK m θ ax o ^ 3) x x * (sgK m θ ax o ^ 3) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    6 * (∑ x, if (sgGlue m).g x then
      ((sgK m θ ax o x x * (sgK m θ ax o ^ 1) ((sgGlue m).σ x) ((sgGlue m).σ x) *
        (sgK m θ ax o ^ 1) x x) * (sgK m θ ax o ^ 3) ((sgGlue m).σ x) ((sgGlue m).σ x)) else 0) +
    6 * (∑ x, if (sgGlue m).g x then
      ((sgK m θ ax o x x * (sgK m θ ax o ^ 1) ((sgGlue m).σ x) ((sgGlue m).σ x) *
        (sgK m θ ax o ^ 2) x x) * (sgK m θ ax o ^ 2) ((sgGlue m).σ x) ((sgGlue m).σ x)) else 0) +
    3 * (∑ x, if (sgGlue m).g x then
      ((sgK m θ ax o x x * (sgK m θ ax o ^ 2) ((sgGlue m).σ x) ((sgGlue m).σ x) *
        (sgK m θ ax o ^ 1) x x) * (sgK m θ ax o ^ 2) ((sgGlue m).σ x) ((sgGlue m).σ x)) else 0) := by
  apply trace_p6_lower_even_strata_boundary (sgGlue m) (sgK m θ ax o)
    (blockK_BD (Hc m θ ax o))
  intro n hn w w' hw hw' hcopy hne
  exact sgK_pow_hkg_up_to_five_of_OAnti m hm θ ax o hanti
    n hn w w' hw hw' hcopy hne


/-- Concrete top-stratum boundary reduction for the sixth moment. Together
with `sg_trace_p6_lower_even_strata_boundary`, this gives all even boundary
strata at p=6 for the Sierpinski glued operator. The top stratum is retained
as a trace with three diagonal corner insertions; it is not asserted to vanish. -/
theorem sg_trace_p6_top_stratum_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    Matrix.trace (sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N) =
    Matrix.trace (sgK m θ ax o *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      sgK m θ ax o *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      sgK m θ ax o *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  apply trace_p6_top_stratum_boundary (sgGlue m) (sgK m θ ax o)
    (blockK_BD (Hc m θ ax o))
  intro n hn w w' hw hw' hcopy hne
  exact sgK_pow_hkg_up_to_five_of_OAnti m hm θ ax o hanti
    n hn w w' hw hw' hcopy hne



/-- Unified concrete boundary expansion for all even strata of the sixth
moment. The lower strata are written as explicit weighted corner sums and the
top stratum as its diagonal-sandwich trace, so later axis-comparison proofs
can address the complete correction in one equation. No cancellation is
assumed by this identity. -/
theorem sg_trace_p6_all_even_strata_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    6 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N * sgK m θ ax o ^ 5 *
        (sgGlue m).N * sgK m θ ax o ^ 0) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 2 * (sgGlue m).N * sgK m θ ax o ^ 4 *
        (sgGlue m).N * sgK m θ ax o ^ 0) +
    3 * Matrix.trace
      (sgK m θ ax o ^ 3 * (sgGlue m).N * sgK m θ ax o ^ 3 *
        (sgGlue m).N * sgK m θ ax o ^ 0) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N * sgK m θ ax o ^ 1 *
        (sgGlue m).N * sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 3 * (sgGlue m).N * sgK m θ ax o ^ 0) +
    6 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N * sgK m θ ax o ^ 1 *
        (sgGlue m).N * sgK m θ ax o ^ 2 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N * sgK m θ ax o ^ 0) +
    3 * Matrix.trace
      (sgK m θ ax o ^ 1 * (sgGlue m).N * sgK m θ ax o ^ 2 *
        (sgGlue m).N * sgK m θ ax o ^ 1 * (sgGlue m).N *
        sgK m θ ax o ^ 2 * (sgGlue m).N * sgK m θ ax o ^ 0) +
    Matrix.trace
      (sgK m θ ax o * (sgGlue m).N * sgK m θ ax o *
        (sgGlue m).N * sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N * sgK m θ ax o *
        (sgGlue m).N * sgK m θ ax o * (sgGlue m).N) =
    6 * (∑ x, if (sgGlue m).g x then
      (sgK m θ ax o ^ 1) x x *
        (sgK m θ ax o ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    6 * (∑ x, if (sgGlue m).g x then
      (sgK m θ ax o ^ 2) x x *
        (sgK m θ ax o ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    3 * (∑ x, if (sgGlue m).g x then
      (sgK m θ ax o ^ 3) x x *
        (sgK m θ ax o ^ 3) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    6 * (∑ x, if (sgGlue m).g x then
      ((sgK m θ ax o x x *
        (sgK m θ ax o ^ 1) ((sgGlue m).σ x) ((sgGlue m).σ x) *
        (sgK m θ ax o ^ 1) x x) *
        (sgK m θ ax o ^ 3) ((sgGlue m).σ x) ((sgGlue m).σ x)) else 0) +
    6 * (∑ x, if (sgGlue m).g x then
      ((sgK m θ ax o x x *
        (sgK m θ ax o ^ 1) ((sgGlue m).σ x) ((sgGlue m).σ x) *
        (sgK m θ ax o ^ 2) x x) *
        (sgK m θ ax o ^ 2) ((sgGlue m).σ x) ((sgGlue m).σ x)) else 0) +
    3 * (∑ x, if (sgGlue m).g x then
      ((sgK m θ ax o x x *
        (sgK m θ ax o ^ 2) ((sgGlue m).σ x) ((sgGlue m).σ x) *
        (sgK m θ ax o ^ 1) x x) *
        (sgK m θ ax o ^ 2) ((sgGlue m).σ x) ((sgGlue m).σ x)) else 0) +
    Matrix.trace
      (sgK m θ ax o *
        Matrix.diagonal (fun y => if (sgGlue m).g y then
          sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
        sgK m θ ax o *
        Matrix.diagonal (fun y => if (sgGlue m).g y then
          sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
        sgK m θ ax o *
        Matrix.diagonal (fun y => if (sgGlue m).g y then
          sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  rw [sg_trace_p6_lower_even_strata_boundary m hm θ ax o hanti,
    sg_trace_p6_top_stratum_boundary m hm θ ax o hanti]

/-- The exact p=6 even-stratum boundary correction. The six-insertion
endpoint is kept as its diagonal-sandwich trace, with no axis-cancellation
claim built into this definition. -/
noncomputable def glueRHS6
    (m : ℕ) (K : Matrix (WSG m) (WSG m) ℂ) : ℂ :=
  6 * (∑ x, if (sgGlue m).g x then
    (K ^ 1) x x * (K ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
  6 * (∑ x, if (sgGlue m).g x then
    (K ^ 2) x x * (K ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
  3 * (∑ x, if (sgGlue m).g x then
    (K ^ 3) x x * (K ^ 3) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
  6 * (∑ x, if (sgGlue m).g x then
    ((K x x * (K ^ 1) ((sgGlue m).σ x) ((sgGlue m).σ x) *
      (K ^ 1) x x) * (K ^ 3) ((sgGlue m).σ x) ((sgGlue m).σ x) ) else 0) +
  6 * (∑ x, if (sgGlue m).g x then
    ((K x x * (K ^ 1) ((sgGlue m).σ x) ((sgGlue m).σ x) *
      (K ^ 2) x x) * (K ^ 2) ((sgGlue m).σ x) ((sgGlue m).σ x) ) else 0) +
  3 * (∑ x, if (sgGlue m).g x then
    ((K x x * (K ^ 2) ((sgGlue m).σ x) ((sgGlue m).σ x) *
      (K ^ 1) x x) * (K ^ 2) ((sgGlue m).σ x) ((sgGlue m).σ x) ) else 0) +
  Matrix.trace
    (K *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        K ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        K ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        K ((sgGlue m).σ y) ((sgGlue m).σ y) else 0))


/-- Full degree-six gluing identity for the actual operator. The ordered
word expansion is reduced using the established p=6 cyclic representative
lemmas; the remaining even-stratum contribution is retained exactly as
glueRHS6. This is a trace split, not an axis-cancellation or level-recurrence
theorem. -/
theorem pOpO_trace6_glue_final
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k)
    (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (hanti : OAnti (m + 1) o) :
    Matrix.trace ((pOpO (m + 1) θ ax o) ^ 6) =
      (∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 6)) +
        glueRHS6 m (sgK m θ ax o) := by
  let K := sgK m θ ax o
  let N := (sgGlue m).N
  let evenTerms :=
    6 * Matrix.trace (K ^ 1 * N * K ^ 5 * N * K ^ 0) +
    6 * Matrix.trace (K ^ 2 * N * K ^ 4 * N * K ^ 0) +
    3 * Matrix.trace (K ^ 3 * N * K ^ 3 * N * K ^ 0) +
    6 * Matrix.trace
      (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 3 * N * K ^ 0) +
    6 * Matrix.trace
      (K ^ 1 * N * K ^ 1 * N * K ^ 2 * N * K ^ 2 * N * K ^ 0) +
    3 * Matrix.trace
      (K ^ 1 * N * K ^ 2 * N * K ^ 1 * N * K ^ 2 * N * K ^ 0) +
    Matrix.trace ((K * N) ^ 6)
  have hwords :
      Matrix.trace ((pOpO (m + 1) θ ax o) ^ 6) =
        ((orderedWordExpansion K (K * N) 6).map Matrix.trace).sum := by
    simpa [K, N] using
      (pOpO_succ_trace_ordered_words m θ ax o hax1 hax2 6 (by omega))
  have hordered :
      ((orderedWordExpansion K (K * N) 6).map Matrix.trace).sum =
        Matrix.trace (K ^ 6) + evenTerms := by
    simpa [K, N, evenTerms, pow_succ, pow_one, pow_zero,
      Matrix.mul_assoc, add_assoc] using
      (sg_trace_p6_ordered_expansion_boundary m hm θ ax o hanti)
  have hcopy :
      Matrix.trace (K ^ 6) =
        ∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 6) := by
    simpa [K, sgK] using (trace_blockK_pow (Hc m θ ax o) 6)
  have heven : evenTerms = glueRHS6 m K := by
    simpa [K, N, evenTerms, glueRHS6, pow_succ, pow_one, pow_zero,
      Matrix.mul_assoc, add_assoc] using
      (sg_trace_p6_all_even_strata_boundary m hm θ ax o hanti)
  calc
    Matrix.trace ((pOpO (m + 1) θ ax o) ^ 6) =
        ((orderedWordExpansion K (K * N) 6).map Matrix.trace).sum := hwords
    _ = Matrix.trace (K ^ 6) + evenTerms := hordered
    _ = (∑ c : GCopy, Matrix.trace (Hc m θ ax o c ^ 6)) +
        glueRHS6 m K := by
      rw [hcopy, heven]


/-- Sixth-moment analogue of defectO: the difference of the two
axis traces at the same level and orientation. -/
noncomputable def defectO6 (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] : ℂ :=
  Matrix.trace ((pOpO m θ ax o) ^ 6) -
    Matrix.trace ((pOpO m θ ax' o) ^ 6)



/-- The sixth-moment defect depends on the orientation only through
its values on flux edges. This is the power-six analogue of defectO_congr. -/
theorem defectO6_congr
    (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o o' : Point → Point → Prop) [DecidableRel o] [DecidableRel o']
    (h : ∀ p q : Point, p ≠ q →
      EdgeB m p.1 p.2 q.1 q.2 = true →
      (if p ≤ q then (p, q) else (q, p)) ∈ fluxEdges m →
      (o p q ↔ o' p q)) :
    defectO6 m θ ax ax' o = defectO6 m θ ax ax' o' := by
  have e : ∀ b : ℕ → Axis, pOpO m θ b o = pOpO m θ b o' := by
    intro b
    funext x y
    exact pHeO_orient_congr m θ b o o' h x.1.1 y.1.1 x.2 y.2
  unfold defectO6
  rw [e ax, e ax']

/-- Exact recursion for the sixth-moment defect. The three subcopy defects
are separated, while the difference of the full p=6 boundary corrections is
kept explicit. In particular, this theorem does not assume that the boundary
difference vanishes or that the sixth-moment defect is stabilized. -/
theorem defectO6_succ
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ)
    (ax ax' : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k)
    (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (hax1' : ∀ k, ax' (3 ^ m + k) = ax' k)
    (hax2' : ∀ k, ax' (2 * 3 ^ m + k) = ax' k) :
    defectO6 (m + 1) θ ax ax' o =
      defectO6 m θ ax ax' o +
      defectO6 m θ ax ax' (oBo m o) +
      defectO6 m θ ax ax' (oCo m o) +
      (glueRHS6 m (sgK m θ ax o) -
        glueRHS6 m (sgK m θ ax' o)) := by
  have hA : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.A = pOpO m θ b o := fun _ => rfl
  have hB : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.B = pOpO m θ b (oBo m o) := fun _ => rfl
  have hC : ∀ b : ℕ → Axis,
      Hc m θ b o GCopy.C = pOpO m θ b (oCo m o) := fun _ => rfl
  unfold defectO6
  rw [pOpO_trace6_glue_final m hm θ ax o hax1 hax2 hanti,
    pOpO_trace6_glue_final m hm θ ax' o hax1' hax2' hanti]
  rw [sum_gcopy, sum_gcopy,
    hA ax, hA ax', hB ax, hB ax', hC ax, hC ax']
  ring


/-- The partner-corner diagonal weight sandwiches sgK to a diagonal
matrix: distinct glued states have zero coupling. -/
theorem sgK_corner_sandwich_offdiag_zero
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    ∀ x y : WSG m, x ≠ y →
      (Matrix.diagonal (fun z => if (sgGlue m).g z then
        sgK m θ ax o ((sgGlue m).σ z) ((sgGlue m).σ z) else 0) *
        sgK m θ ax o *
        Matrix.diagonal (fun z => if (sgGlue m).g z then
          sgK m θ ax o ((sgGlue m).σ z) ((sgGlue m).σ z) else 0)) x y = 0 := by
  apply diagonal_sandwich_offdiag_zero (g := (sgGlue m).g)
    (d := fun z => if (sgGlue m).g z then
      sgK m θ ax o ((sgGlue m).σ z) ((sgGlue m).σ z) else 0)
    (K := sgK m θ ax o)
  · intro x hx
    simp [hx]
  · intro x y hx hy hxy
    exact sgK_glued_offdiag m (by omega) θ ax o x y hx hy hxy


/-- Entrywise form of the concrete partner-corner sandwich. -/
theorem sgK_corner_sandwich_apply
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (x y : WSG m) :
    (Matrix.diagonal (fun z => if (sgGlue m).g z then
      sgK m θ ax o ((sgGlue m).σ z) ((sgGlue m).σ z) else 0) *
      sgK m θ ax o *
      Matrix.diagonal (fun z => if (sgGlue m).g z then
        sgK m θ ax o ((sgGlue m).σ z) ((sgGlue m).σ z) else 0)) x y =
      (if (sgGlue m).g x then
        sgK m θ ax o ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) *
      sgK m θ ax o x y *
      (if (sgGlue m).g y then
        sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) := by
  exact diagonal_sandwich_apply
    (fun z => if (sgGlue m).g z then
      sgK m θ ax o ((sgGlue m).σ z) ((sgGlue m).σ z) else 0)
    (sgK m θ ax o) x y


/-- The diagonal entries of the concrete partner-corner sandwich are the
paired diagonal products squared times the corresponding diagonal of sgK. -/
theorem sgK_corner_sandwich_diag_apply
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (x : WSG m) :
    (Matrix.diagonal (fun z => if (sgGlue m).g z then
      sgK m θ ax o ((sgGlue m).σ z) ((sgGlue m).σ z) else 0) *
      sgK m θ ax o *
      Matrix.diagonal (fun z => if (sgGlue m).g z then
        sgK m θ ax o ((sgGlue m).σ z) ((sgGlue m).σ z) else 0)) x x =
      (if (sgGlue m).g x then
        sgK m θ ax o ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) *
      sgK m θ ax o x x *
      (if (sgGlue m).g x then
        sgK m θ ax o ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
  exact sgK_corner_sandwich_apply m θ ax o x x


/-- The partner-corner sandwich is exactly the diagonal matrix formed from
its diagonal entries. This packages the entrywise formula and off-diagonal
vanishing into a matrix identity. -/
theorem sgK_corner_sandwich_eq_diagonal
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    (Matrix.diagonal (fun z => if (sgGlue m).g z then
      sgK m θ ax o ((sgGlue m).σ z) ((sgGlue m).σ z) else 0) *
      sgK m θ ax o *
      Matrix.diagonal (fun z => if (sgGlue m).g z then
        sgK m θ ax o ((sgGlue m).σ z) ((sgGlue m).σ z) else 0)) =
    Matrix.diagonal (fun z =>
      (Matrix.diagonal (fun w => if (sgGlue m).g w then
        sgK m θ ax o ((sgGlue m).σ w) ((sgGlue m).σ w) else 0) *
        sgK m θ ax o *
        Matrix.diagonal (fun w => if (sgGlue m).g w then
          sgK m θ ax o ((sgGlue m).σ w) ((sgGlue m).σ w) else 0)) z z) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp
  · rw [Matrix.diagonal_apply]
    simp only [if_neg hxy]
    exact sgK_corner_sandwich_offdiag_zero m hm θ ax o x y hxy




/-- Regroup the p=6 top boundary trace so the already-proved diagonal
sandwich identity can be applied. This is an exact reduction, not yet a
claim that the trace is a sum of cubes. -/
theorem sg_trace_p6_top_stratum_reduce_to_diagonal_sandwich
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    Matrix.trace (sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N) =
    Matrix.trace (sgK m θ ax o *
      Matrix.diagonal (fun z =>
        (Matrix.diagonal (fun y => if (sgGlue m).g y then
          sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
          sgK m θ ax o *
        Matrix.diagonal (fun y => if (sgGlue m).g y then
          sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) z z) *
      sgK m θ ax o *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  let D : Matrix (WSG m) (WSG m) ℂ :=
    Matrix.diagonal (fun y => if (sgGlue m).g y then
      sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)
  have hboundary :
      Matrix.trace (sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N) =
      Matrix.trace (sgK m θ ax o * D * sgK m θ ax o *
        D * sgK m θ ax o * D) := by
    simpa [D] using
      sg_trace_p6_top_stratum_boundary m hm θ ax o hanti
  have hsandwich :
      D * sgK m θ ax o * D =
        Matrix.diagonal (fun z => (D * sgK m θ ax o * D) z z) := by
    simpa [D] using
      sgK_corner_sandwich_eq_diagonal m hm θ ax o
  calc
    Matrix.trace (sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N) =
        Matrix.trace (sgK m θ ax o * D * sgK m θ ax o *
          D * sgK m θ ax o * D) := hboundary
    _ = Matrix.trace (sgK m θ ax o *
          (D * sgK m θ ax o * D) * sgK m θ ax o * D) := by
          simp [Matrix.mul_assoc]
    _ = Matrix.trace (sgK m θ ax o *
          Matrix.diagonal (fun z => (D * sgK m θ ax o * D) z z) *
          sgK m θ ax o * D) := by
          conv_lhs => rw [hsandwich]
    _ = Matrix.trace (sgK m θ ax o *
          Matrix.diagonal (fun z =>
            (Matrix.diagonal (fun y => if (sgGlue m).g y then
              sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
              sgK m θ ax o *
            Matrix.diagonal (fun y => if (sgGlue m).g y then
              sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) z z) *
          sgK m θ ax o *
          Matrix.diagonal (fun y => if (sgGlue m).g y then
            sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
          simp [D]




/-- Reassociate the alternating six-factor trace as a cubic trace. -/
theorem trace_K_D_alternating_six_eq_cube
    {X : Type*} [Fintype X] [DecidableEq X]
    (K D : Matrix X X ℂ) :
    Matrix.trace (K * D * K * D * K * D) =
      Matrix.trace ((K * D) ^ 3) := by
  rw [pow_succ, pow_two]
  simp only [Matrix.mul_assoc]


/-- The p=6 top stratum can be viewed as a cubic trace after the
already-proved boundary reduction. All geometric hypotheses are inherited
from the boundary theorem; this does not claim axis invariance. -/
theorem sg_trace_p6_top_stratum_cube
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    Matrix.trace (sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N) =
    Matrix.trace ((sgK m θ ax o * Matrix.diagonal (fun y =>
      if (sgGlue m).g y then
        sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) ) ^ 3) := by
  rw [sg_trace_p6_top_stratum_boundary m hm θ ax o hanti]
  exact trace_K_D_alternating_six_eq_cube
    (sgK m θ ax o)
    (Matrix.diagonal (fun y => if (sgGlue m).g y then
      sgK m θ ax o ((sgGlue m).σ y) ((sgGlue m).σ y) else 0))


/-- Evaluate the p=6 top boundary trace using support-sensitive two-index
trace collapse. This is an exact finite-level identity, not an axis-invariance
claim. -/
theorem sg_trace_p6_top_stratum_diagonal_cube
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    Matrix.trace (sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N *
      sgK m θ ax o * (sgGlue m).N) =
    ∑ x, if (sgGlue m).g x then
      (sgK m θ ax o x x *
        sgK m θ ax o ((sgGlue m).σ x) ((sgGlue m).σ x)) ^ 3 else 0 := by
  classical
  let d : WSG m → ℂ := fun x =>
    if (sgGlue m).g x then
      sgK m θ ax o ((sgGlue m).σ x) ((sgGlue m).σ x) else 0
  let D : Matrix (WSG m) (WSG m) ℂ := Matrix.diagonal d
  let a : WSG m → ℂ := fun x => (D * sgK m θ ax o * D) x x
  have hd : ∀ x, ¬ (sgGlue m).g x → d x = 0 := by
    intro x hx
    simp [d, hx]
  have ha : ∀ x, ¬ (sgGlue m).g x → a x = 0 := by
    intro x hx
    change (D * sgK m θ ax o * D) x x = 0
    rw [diagonal_sandwich_apply]
    simp [d, hx]
  have hKoff : ∀ x y, (sgGlue m).g x → (sgGlue m).g y →
      x ≠ y → sgK m θ ax o x y = 0 := by
    intro x y hx hy hxy
    exact sgK_glued_offdiag m (by omega) θ ax o x y hx hy hxy
  have hreduce :=
    sg_trace_p6_top_stratum_reduce_to_diagonal_sandwich m hm θ ax o hanti
  calc
    Matrix.trace (sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N *
        sgK m θ ax o * (sgGlue m).N) =
        Matrix.trace (sgK m θ ax o * Matrix.diagonal a *
          sgK m θ ax o * D) := by
          simpa only [D, a, d] using hreduce
    _ = ∑ x, if (sgGlue m).g x then
          sgK m θ ax o x x * a x * sgK m θ ax o x x * d x else 0 := by
          exact trace_kernel_diagonal_kernel_diagonal_collapse
            (sgK m θ ax o) (sgGlue m).g a d ha hd hKoff
    _ = ∑ x, if (sgGlue m).g x then
          (sgK m θ ax o x x *
            sgK m θ ax o ((sgGlue m).σ x) ((sgGlue m).σ x)) ^ 3 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hg : (sgGlue m).g x
          · simp only [if_pos hg]
            have hax : a x =
                d x * sgK m θ ax o x x * d x := by
              change (Matrix.diagonal d * sgK m θ ax o *
                Matrix.diagonal d) x x = _
              rw [diagonal_sandwich_apply]
            rw [hax]
            simp [d, hg]
            ring
          · simp [hg]




/-- Four alternating kernel/diagonal factors collapse to a pointwise fourth
power when the diagonal weight is supported on a set where K has no
off-diagonal entries. The support condition is used before invoking the
off-diagonal hypothesis. -/
theorem trace_alternating_four_supported_diagonal
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : X → Prop) [DecidablePred g]
    (K : Matrix X X ℂ) (d : X → ℂ)
    (hd : ∀ x, ¬ g x → d x = 0)
    (hK : ∀ x y, g x → g y → x ≠ y → K x y = 0) :
    Matrix.trace (K * Matrix.diagonal d * K * Matrix.diagonal d *
      K * Matrix.diagonal d * K * Matrix.diagonal d) =
      ∑ x, if g x then (K x x * d x) ^ 4 else 0 := by
  classical
  let D : Matrix X X ℂ := Matrix.diagonal d
  let e : X → ℂ := fun x => d x * K x x * d x
  have hD : D * K * D = Matrix.diagonal e := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [D, e, Matrix.mul_apply, Matrix.diagonal_apply]
    · rw [Matrix.diagonal_apply]
      simp only [if_neg hxy]
      have hz := diagonal_sandwich_offdiag_zero g d K hd hK x y hxy
      simpa [D] using hz
  have he : ∀ x, ¬ g x → e x = 0 := by
    intro x hx
    simp [e, hd x hx]
  have hcyc :
      Matrix.trace (K * D * K * D * K * D * K * D) =
        Matrix.trace (K * (D * K * D) * K * (D * K * D)) := by
    calc
      Matrix.trace (K * D * K * D * K * D * K * D) =
          Matrix.trace (D * K * D * K * D * K * D * K) := by
            rw [show K * D * K * D * K * D * K * D =
              K * (D * K * D * K * D * K * D) by simp [Matrix.mul_assoc]]
            exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((D * K * D) * K * (D * K * D) * K) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace (K * (D * K * D) * K * (D * K * D)) := by
            rw [Matrix.trace_mul_comm]
            simp [Matrix.mul_assoc]
  rw [hcyc, hD]
  have hKoff : ∀ x y, g x → g y → x ≠ y → K x y = 0 := hK
  have hcollapsed :=
    trace_kernel_diagonal_kernel_diagonal_collapse K g e e he he hKoff
  rw [hcollapsed]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hg : g x
  · simp only [if_pos hg]
    simp [e]
    ring
  · simp [hg]

/-- Five alternating kernel/diagonal factors collapse to a pointwise fifth
power when the diagonal weight is supported on a set where K has no
off-diagonal entries. This extends the p=8 collapse by one factor. -/
theorem trace_alternating_five_supported_diagonal
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : X → Prop) [DecidablePred g]
    (K : Matrix X X ℂ) (d : X → ℂ)
    (hd : ∀ x, ¬ g x → d x = 0)
    (hK : ∀ x y, g x → g y → x ≠ y → K x y = 0) :
    Matrix.trace (K * Matrix.diagonal d * K * Matrix.diagonal d *
      K * Matrix.diagonal d * K * Matrix.diagonal d *
      K * Matrix.diagonal d) =
      ∑ x, if g x then (K x x * d x) ^ 5 else 0 := by
  classical
  let D : Matrix X X ℂ := Matrix.diagonal d
  let e : X → ℂ := fun x => d x * K x x * d x
  let E : Matrix X X ℂ := D * K * D
  let f : X → ℂ := fun x => e x * K x x * e x
  have hD : E = Matrix.diagonal e := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [E, D, e, Matrix.mul_apply, Matrix.diagonal_apply]
    · rw [Matrix.diagonal_apply]
      simp only [if_neg hxy]
      have hz := diagonal_sandwich_offdiag_zero g d K hd hK x y hxy
      simpa [E, D] using hz
  have he : ∀ x, ¬ g x → e x = 0 := by
    intro x hx
    simp [e, hd x hx]
  have hE : Matrix.diagonal e * K * Matrix.diagonal e =
      Matrix.diagonal f := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [f, Matrix.mul_apply, Matrix.diagonal_apply]
    · rw [Matrix.diagonal_apply]
      simp only [if_neg hxy]
      exact diagonal_sandwich_offdiag_zero g e K he hK x y hxy
  have hf : ∀ x, ¬ g x → f x = 0 := by
    intro x hx
    simp [f, he x hx]
  have hcyc :
      Matrix.trace (K * D * K * D * K * D * K * D * K * D) =
        Matrix.trace (E * K * E * K * D * K) := by
    calc
      Matrix.trace (K * D * K * D * K * D * K * D * K * D) =
          Matrix.trace (D * K * D * K * D * K * D * K * D * K) := by
            rw [show K * D * K * D * K * D * K * D * K * D =
              K * (D * K * D * K * D * K * D * K * D) by
                simp [Matrix.mul_assoc]]
            exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E * K * E * K * D * K) := by
            simp [E, Matrix.mul_assoc]
  calc
    Matrix.trace (K * D * K * D * K * D * K * D * K * D) =
        Matrix.trace (Matrix.diagonal f * K * D * K) := by
          rw [hcyc, hD, hE]
    _ = Matrix.trace (Matrix.diagonal f * (K * D * K)) := by
          simp [Matrix.mul_assoc]
    _ = Matrix.trace ((K * D * K) * Matrix.diagonal f) := by
          exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace (K * D * K * Matrix.diagonal f) := by
          simp [Matrix.mul_assoc]
    _ = ∑ x, if g x then K x x * d x * K x x * f x else 0 := by
          exact trace_kernel_diagonal_kernel_diagonal_collapse K g d f hd hf hK
    _ = ∑ x, if g x then (K x x * d x) ^ 5 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hg : g x
          · simp only [if_pos hg]
            simp [f, e]
            ring
          · simp [hg]

/-- Concrete p=8 top-stratum boundary formula for the Sierpinski glued
operator. This specializes the generic eight-pairing reduction under OAnti.
The resulting ordered boundary sum is explicit; no cancellation is claimed. -/
theorem sg_trace_p8_top_stratum_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N * K ^ 0) =
    ∑ x, if (sgGlue m).g x then
      (([K ^ 0, K ^ 1,
        Matrix.diagonal (fun y => if (sgGlue m).g y then
          (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
        K ^ 1,
        Matrix.diagonal (fun y => if (sgGlue m).g y then
          (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
        K ^ 1,
        Matrix.diagonal (fun y => if (sgGlue m).g y then
          (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
        K ^ 1] : List (Matrix (WSG m) (WSG m) ℂ)).prod) x x *
        (K ^ 1) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
  dsimp
  apply trace_eight_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 1 1 1 1 1 0
  all_goals
    intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_five_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne






/-- The p=8 top boundary contribution collapses to pointwise fourth powers.
The proof composes the established boundary reduction with the generic trace
identity; cancellation with lower strata is not part of this statement. -/
theorem sg_trace_p8_top_stratum_diagonal_fourth
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N * K ^ 0) =
    ∑ x, if (sgGlue m).g x then
      (K x x * K ((sgGlue m).σ x) ((sgGlue m).σ x)) ^ 4 else 0 := by
  classical
  dsimp
  let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
  let g : WSG m → Prop := (sgGlue m).g
  let d : WSG m → ℂ := fun x =>
    if g x then K ((sgGlue m).σ x) ((sgGlue m).σ x) else 0
  let D : Matrix (WSG m) (WSG m) ℂ := Matrix.diagonal d
  have hd : ∀ x, ¬ g x → d x = 0 := by
    intro x hx
    simp [d, hx]
  have hKoff : ∀ x y, g x → g y → x ≠ y → K x y = 0 := by
    intro x y hx hy hxy
    exact sgK_glued_offdiag m (by omega) θ ax o x y hx hy hxy
  calc
    Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N * K ^ 0) =
        ∑ x, if g x then
          (([K ^ 0, K ^ 1, D, K ^ 1, D, K ^ 1, D, K ^ 1] :
            List (Matrix (WSG m) (WSG m) ℂ)).prod) x x * d x else 0 := by
          rw [sg_trace_p8_top_stratum_boundary m hm θ ax o hanti]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hg : (sgGlue m).g x
          · simp [K, g, d, D, hg]
          · simp [K, g, d, D, hg]
    _ = Matrix.trace ((K * D) ^ 4) := by
          exact trace_p8_supported_boundary_sum_as_fourth_power g K d hd
    _ = Matrix.trace (K * D * K * D * K * D * K * D) := by
          rw [trace_K_D_alternating_eight_eq_four]
    _ = ∑ x, if g x then (K x x * d x) ^ 4 else 0 := by
          exact trace_alternating_four_supported_diagonal g K d hd hKoff
    _ = ∑ x, if (sgGlue m).g x then
          (K x x * K ((sgGlue m).σ x) ((sgGlue m).σ x)) ^ 4 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hg : (sgGlue m).g x
          · simp only [if_pos hg]
            simp [K, d, g, hg]
          · simp [hg, g]

/-- Concrete p=10 top-stratum boundary formula for the Sierpinski glued
operator. This specializes the generic ten-pairing reduction under OAnti.
The ordered boundary sum is explicit; no cancellation or axis-independence
is asserted. -/
theorem sg_trace_p10_top_stratum_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N * K ^ 0) =
    ∑ x, if (sgGlue m).g x then
      (([K ^ 0, K ^ 1,
        Matrix.diagonal (fun y => if (sgGlue m).g y then
          (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
        K ^ 1,
        Matrix.diagonal (fun y => if (sgGlue m).g y then
          (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
        K ^ 1,
        Matrix.diagonal (fun y => if (sgGlue m).g y then
          (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
        K ^ 1,
        Matrix.diagonal (fun y => if (sgGlue m).g y then
          (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
        K ^ 1] : List (Matrix (WSG m) (WSG m) ℂ)).prod) x x *
        (K ^ 1) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
  dsimp
  apply trace_ten_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 1 1 1 1 1 1 1 0
  all_goals
    intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_five_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the first six-N cyclic class
(1,1,1,1,1,5) in the p=10 expansion. Its orbit has size six, hence
multiplicity ten. The result preserves the ordered diagonal boundary factors. -/
theorem sg_trace_p10_six_N_class_111115
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 5 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 5) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 1 1 5 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      5 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the second six-N cyclic class
(1,1,1,1,2,4) in the p=10 expansion. Its orbit has size six and
multiplicity ten. -/
theorem sg_trace_p10_six_N_class_111124
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 4 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 2 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 4) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 1 2 4 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      4 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the six-N cyclic class
(1,1,1,1,3,3) in the p=10 expansion. The six distinct cyclic rotations
give multiplicity ten; the boundary factors remain in their original order. -/
theorem sg_trace_p10_six_N_class_111133
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 3 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 3 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 3) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 1 3 3 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      3 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the fourth six-N cyclic class
(1,1,1,1,4,2) in the p=10 expansion. Its orbit has size six and
multiplicity ten. -/
theorem sg_trace_p10_six_N_class_111142
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 4 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 4 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 2) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 1 4 2 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      2 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the fifth six-N cyclic class
(1,1,1,2,1,4) in the p=10 expansion. Its orbit has size six and
multiplicity ten. -/
theorem sg_trace_p10_six_N_class_111214
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 4 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 2) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 4) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 2 1 4 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      2 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      4 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the sixth six-N cyclic class
(1,1,1,2,2,3) in the p=10 expansion. Its orbit has size six and
multiplicity ten. -/
theorem sg_trace_p10_six_N_class_111223
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 2) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 2 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 3) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 2 2 3 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      2 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      3 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the sixth six-N cyclic class
(1,1,1,2,3,2) in the p=10 expansion. Its orbit has size six and
multiplicity ten. -/
theorem sg_trace_p10_six_N_class_111232
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
      K ^ 3 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 2) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 3 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 2) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 2 3 2 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      2 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      2 (by omega) w w' hw hw' hcopy hne



/-- Concrete specialization of the distinct six-N cyclic class
(1,1,1,3,1,3) in the p=10 expansion. Its orbit has size six, so
its exact multiplicity is ten. This is distinct from the period-three
class (1,1,3,1,1,3), whose multiplicity is five. -/
theorem sg_trace_p10_six_N_class_111313
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 3) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 3) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 3 1 3 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      3 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      3 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the six-N cyclic class
(1,1,1,3,2,2) in the p=10 expansion. Its orbit has size six,
so the exact multiplicity is ten. -/
theorem sg_trace_p10_six_N_class_111322
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 3) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 2 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 2) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 3 2 2 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      3 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      2 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the six-N cyclic class
(1,1,1,4,1,2) in the p=10 expansion. Its orbit has size ten,
so its exact multiplicity is ten. -/
theorem sg_trace_p10_six_N_class_111412
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 4 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 4) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 2) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 1 4 1 2 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      4 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      2 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the six-N cyclic class
(1,1,2,1,1,4) in the p=10 expansion. Its orbit has size ten,
so its exact multiplicity is ten. -/
theorem sg_trace_p10_six_N_class_112114
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 4 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 2 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 4) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 2 1 1 4 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      4 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the sixth six-N cyclic class
(1,1,3,1,1,3) in the p=10 expansion. Its orbit has size three and
multiplicity five. -/
theorem sg_trace_p10_six_N_class_113113
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    5 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 3 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) =
    5 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 3 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 3) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 5 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 3 1 1 3 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      3 (by omega) w w' hw hw' hcopy hne




/-- Concrete specialization of the cyclic six-N class
(1,1,3,1,2,2) in the p=10 expansion. Its orbit has size six and
multiplicity ten. -/
theorem sg_trace_p10_six_N_class_113122
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 3 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 3 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 2 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 2) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 3 1 2 2 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      2 (by omega) w w' hw hw' hcopy hne


/-- Concrete specialization of the cyclic six-N class
(1,1,3,2,1,2) in the p=10 expansion. Its orbit has size six, hence
the exact multiplicity is ten. The ordered boundary form has three
diagonal corner factors, matching `trace_six_N_powers_boundary`. -/
theorem sg_trace_p10_six_N_class_113212
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 3 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
    10 * Matrix.trace (K ^ 0 * K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 3 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 2) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      K ^ 1 *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ 2) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  dsimp
  apply congrArg (fun z : ℂ => 10 * z)
  apply trace_six_N_powers_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
    1 1 3 2 1 2 0
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      1 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      2 (by omega) w w' hw hw' hcopy hne
  · intro w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
      2 (by omega) w w' hw hw' hcopy hne


/-- Concrete Sierpinski specialization of the complete eight-N stratum.
The five cyclic classes retain their exact multiplicities, including the
periodic class of weight five. This is a boundary reduction only. -/
theorem sg_trace_p10_eight_N_stratum_boundary
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) +
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
    5 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
    10 * trace_p10_eight_N_boundary_term (sgGlue m) K 1 1 1 1 1 1 1 3 +
    10 * trace_p10_eight_N_boundary_term (sgGlue m) K 1 1 1 1 1 1 2 2 +
    10 * trace_p10_eight_N_boundary_term (sgGlue m) K 1 1 1 1 1 2 1 2 +
    10 * trace_p10_eight_N_boundary_term (sgGlue m) K 1 1 1 1 2 1 1 2 +
    5 * trace_p10_eight_N_boundary_term (sgGlue m) K 1 1 2 1 1 1 1 2 := by
  dsimp
  apply trace_p10_eight_N_stratum_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
  intro n hn w w' hw hw' hcopy hne
  exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti n hn w w' hw hw' hcopy hne


 /-- Concrete specialization of the exact two-N p=10 stratum.
For m ≥ 4, the geometric corner-support bound supplies every power through
degree nine. This is a boundary-sum identity only; it does not assert
cancellation with the other even strata. -/
theorem sg_trace_p10_two_N_stratum_boundary
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 9 * (sgGlue m).N * K ^ 0) +
    10 * Matrix.trace (K ^ 2 * (sgGlue m).N * K ^ 8 * (sgGlue m).N * K ^ 0) +
    10 * Matrix.trace (K ^ 3 * (sgGlue m).N * K ^ 7 * (sgGlue m).N * K ^ 0) +
    10 * Matrix.trace (K ^ 4 * (sgGlue m).N * K ^ 6 * (sgGlue m).N * K ^ 0) +
    5 * Matrix.trace (K ^ 5 * (sgGlue m).N * K ^ 5 * (sgGlue m).N * K ^ 0) =
    10 * (∑ x, if (sgGlue m).g x then
      (K ^ 1) x x * (K ^ 9) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    10 * (∑ x, if (sgGlue m).g x then
      (K ^ 2) x x * (K ^ 8) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    10 * (∑ x, if (sgGlue m).g x then
      (K ^ 3) x x * (K ^ 7) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    10 * (∑ x, if (sgGlue m).g x then
      (K ^ 4) x x * (K ^ 6) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    5 * (∑ x, if (sgGlue m).g x then
      (K ^ 5) x x * (K ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
  dsimp
  apply trace_p10_two_N_stratum_boundary (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
  intro n hn w w' hw hw' hcopy hne
  exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti n hn w w' hw hw' hcopy hne


 /-- Concrete Sierpinski specialization of the (1,1,6,2) four-N
cyclic class in the p=10 expansion. The exact multiplicity is ten; the
nested corner sum retains the ordered factors from the generic reduction. -/
theorem sg_trace_p10_four_N_class_1162
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace
      (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 6 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
    10 * (∑ x, if (sgGlue m).g x then
      (∑ y, if (sgGlue m).g y then
        ((K ^ 0 * K ^ 1) x y *
          (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y)) *
          (K ^ 6) y x else 0) *
        (K ^ 2) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
  dsimp
  apply trace_p10_four_N_class_1162 (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
  intro n hn w w' hw hw' hcopy hne
  exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti n hn w w' hw hw' hcopy hne


/-- Concrete Sierpinski specialization of the (1,1,5,3) four-N
cyclic class in the p=10 expansion. Its multiplicity is ten; the
ordered corner factors are preserved by the generic reduction. -/
theorem sg_trace_p10_four_N_class_1153
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace
      (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 5 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) =
    10 * (∑ x, if (sgGlue m).g x then
      (∑ y, if (sgGlue m).g y then
        ((K ^ 0 * K ^ 1) x y *
          (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y)) *
          (K ^ 5) y x else 0) *
        (K ^ 3) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
  dsimp
  apply trace_p10_four_N_class_1153 (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
  intro n hn w w' hw hw' hcopy hne
  exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti n hn w w' hw hw' hcopy hne


/-- Concrete Sierpinski specialization of the (1,1,1,7) four-N
cyclic class in the p=10 expansion. Its multiplicity is ten. -/
theorem sg_trace_p10_four_N_class_1117
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace
      (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 7 * (sgGlue m).N * K ^ 0) =
    10 * (∑ x, if (sgGlue m).g x then
      (∑ y, if (sgGlue m).g y then
        ((K ^ 0 * K ^ 1) x y *
          (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y)) *
          (K ^ 1) y x else 0) *
        (K ^ 7) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
  dsimp
  apply trace_p10_four_N_class_1117 (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
  intro n hn w w' hw hw' hcopy hne
  exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti n hn w w' hw hw' hcopy hne


/-- Concrete Sierpinski specialization of the (1,1,2,6) four-N
cyclic class in the p=10 expansion. Its multiplicity is ten. -/
theorem sg_trace_p10_four_N_class_1126
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace
      (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 2 * (sgGlue m).N * K ^ 6 * (sgGlue m).N * K ^ 0) =
    10 * (∑ x, if (sgGlue m).g x then
      (∑ y, if (sgGlue m).g y then
        ((K ^ 0 * K ^ 1) x y *
          (K ^ 1) ((sgGlue m).σ y) ((sgGlue m).σ y)) *
          (K ^ 2) y x else 0) *
        (K ^ 6) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
  dsimp
  apply trace_p10_four_N_class_1126 (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
  intro n hn w w' hw hw' hcopy hne
  exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti n hn w w' hw hw' hcopy hne


/-- Concrete Sierpinski specialization of the (1,2,1,6) four-N
cyclic class in the p=10 expansion. Its multiplicity is ten. -/
theorem sg_trace_p10_four_N_class_1216
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    10 * Matrix.trace
      (K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 6 * (sgGlue m).N * K ^ 0) =
    10 * (∑ x, if (sgGlue m).g x then
      (∑ y, if (sgGlue m).g y then
        ((K ^ 0 * K ^ 1) x y *
          (K ^ 2) ((sgGlue m).σ y) ((sgGlue m).σ y)) *
          (K ^ 1) y x else 0) *
        (K ^ 6) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
  dsimp
  apply trace_p10_four_N_class_1216 (sgGlue m)
    (sgK m θ ax o) (blockK_BD (Hc m θ ax o))
  intro n hn w w' hw hw' hcopy hne
  exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti n hn w w' hw hw' hcopy hne


/-- Convert the concrete p=10 top boundary contribution into a fifth-power
trace of the kernel times its glued-corner diagonal. This is the operator-level
version of the generic supported-sum bridge; it does not claim cancellation
against the lower boundary strata. -/
theorem sg_trace_p10_top_stratum_fifth_power_trace
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N * K ^ 0) =
    Matrix.trace ((K * Matrix.diagonal (fun x =>
      if (sgGlue m).g x then K ((sgGlue m).σ x) ((sgGlue m).σ x) else 0)) ^ 5) := by
  classical
  dsimp
  let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
  let g : WSG m → Prop := (sgGlue m).g
  let d : WSG m → ℂ := fun x =>
    if g x then K ((sgGlue m).σ x) ((sgGlue m).σ x) else 0
  have hd : ∀ x, ¬ g x → d x = 0 := by
    intro x hx
    simp [d, hx]
  calc
    Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N * K ^ 0) =
        ∑ x, if g x then
          (([K ^ 0, K ^ 1, Matrix.diagonal d, K ^ 1,
            Matrix.diagonal d, K ^ 1, Matrix.diagonal d, K ^ 1,
            Matrix.diagonal d, K ^ 1] :
            List (Matrix (WSG m) (WSG m) ℂ)).prod) x x * d x else 0 := by
          rw [sg_trace_p10_top_stratum_boundary m hm θ ax o hanti]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hg : (sgGlue m).g x
          · simp [K, g, d, hg]
          · simp [K, g, d, hg]
    _ = Matrix.trace ((K * Matrix.diagonal d) ^ 5) := by
          exact trace_p10_supported_boundary_sum_as_fifth_power g K d hd
    _ = Matrix.trace ((K * Matrix.diagonal (fun x =>
          if (sgGlue m).g x then
            K ((sgGlue m).σ x) ((sgGlue m).σ x) else 0)) ^ 5) := by
          rfl


/-- The p=10 top boundary contribution collapses to pointwise fifth powers.
This composes the established boundary reduction with the generic supported
trace identity; cancellation with lower strata is not part of this statement. -/
theorem sg_trace_p10_top_stratum_diagonal_fifth
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N * K ^ 0) =
    ∑ x, if (sgGlue m).g x then
      (K x x * K ((sgGlue m).σ x) ((sgGlue m).σ x)) ^ 5 else 0 := by
  classical
  dsimp
  let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
  let g : WSG m → Prop := (sgGlue m).g
  let d : WSG m → ℂ := fun x =>
    if g x then K ((sgGlue m).σ x) ((sgGlue m).σ x) else 0
  let D : Matrix (WSG m) (WSG m) ℂ := Matrix.diagonal d
  have hd : ∀ x, ¬ g x → d x = 0 := by
    intro x hx
    simp [d, hx]
  have hKoff : ∀ x y, g x → g y → x ≠ y → K x y = 0 := by
    intro x y hx hy hxy
    exact sgK_glued_offdiag m (by omega) θ ax o x y hx hy hxy
  calc
    Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N * K ^ 0) =
        Matrix.trace ((K * D) ^ 5) := by
          exact sg_trace_p10_top_stratum_fifth_power_trace m hm θ ax o hanti
    _ = Matrix.trace (K * D * K * D * K * D * K * D * K * D) := by
          rw [trace_K_D_alternating_ten_eq_five]
    _ = ∑ x, if g x then (K x x * d x) ^ 5 else 0 := by
          exact trace_alternating_five_supported_diagonal g K d hd hKoff
    _ = ∑ x, if (sgGlue m).g x then
          (K x x * K ((sgGlue m).σ x) ((sgGlue m).σ x)) ^ 5 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hg : (sgGlue m).g x
          · simp only [if_pos hg]
            simp [K, d, g, hg]
          · simp [hg, g]


theorem sg_trace_p8_two_N_stratum_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 7 * (sgGlue m).N * K ^ 0) +
    8 * Matrix.trace (K ^ 2 * (sgGlue m).N * K ^ 6 * (sgGlue m).N * K ^ 0) +
    8 * Matrix.trace (K ^ 3 * (sgGlue m).N * K ^ 5 * (sgGlue m).N * K ^ 0) +
    4 * Matrix.trace (K ^ 4 * (sgGlue m).N * K ^ 4 * (sgGlue m).N * K ^ 0) =
    8 * (∑ x, if (sgGlue m).g x then
      (K ^ 1) x x * (K ^ 7) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    8 * (∑ x, if (sgGlue m).g x then
      (K ^ 2) x x * (K ^ 6) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    8 * (∑ x, if (sgGlue m).g x then
      (K ^ 3) x x * (K ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
    4 * (∑ x, if (sgGlue m).g x then
      (K ^ 4) x x * (K ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) := by
  dsimp
  let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
  have hkg : ∀ n, n ≤ 7 → ∀ w w',
      (sgGlue m).g w → (sgGlue m).g w' → w.1 = w'.1 → w ≠ w' →
        (K ^ n) w w' = 0 := by
    intro n hn w w' hw hw' hcopy hne
    have hside : 7 < 2 ^ m := by
      calc
        7 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    exact sgK_pow_hkg_of_OAnti m n θ ax o hanti (by omega)
      w w' hw hw' hcopy hne
  have h17 : Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 7 *
      (sgGlue m).N * K ^ 0) =
      ∑ x, if (sgGlue m).g x then
        (K ^ 1) x x * (K ^ 7) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
    simpa [pow_zero] using
      (trace_two_N_powers (sgGlue m) K 1 7 0
        (BD_pow K (blockK_BD (Hc m θ ax o)) 7)
        (by
          intro w w' hw hw' hcopy hne
          exact hkg 7 (by omega) w w' hw hw' hcopy hne))
  have h26 : Matrix.trace (K ^ 2 * (sgGlue m).N * K ^ 6 *
      (sgGlue m).N * K ^ 0) =
      ∑ x, if (sgGlue m).g x then
        (K ^ 2) x x * (K ^ 6) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
    simpa [pow_zero] using
      (trace_two_N_powers (sgGlue m) K 2 6 0
        (BD_pow K (blockK_BD (Hc m θ ax o)) 6)
        (by
          intro w w' hw hw' hcopy hne
          exact hkg 6 (by omega) w w' hw hw' hcopy hne))
  have h35 : Matrix.trace (K ^ 3 * (sgGlue m).N * K ^ 5 *
      (sgGlue m).N * K ^ 0) =
      ∑ x, if (sgGlue m).g x then
        (K ^ 3) x x * (K ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
    simpa [pow_zero] using
      (trace_two_N_powers (sgGlue m) K 3 5 0
        (BD_pow K (blockK_BD (Hc m θ ax o)) 5)
        (by
          intro w w' hw hw' hcopy hne
          exact hkg 5 (by omega) w w' hw hw' hcopy hne))
  have h44 : Matrix.trace (K ^ 4 * (sgGlue m).N * K ^ 4 *
      (sgGlue m).N * K ^ 0) =
      ∑ x, if (sgGlue m).g x then
        (K ^ 4) x x * (K ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
    simpa [pow_zero] using
      (trace_two_N_powers (sgGlue m) K 4 4 0
        (BD_pow K (blockK_BD (Hc m θ ax o)) 4)
        (by
          intro w w' hw hw' hcopy hne
          exact hkg 4 (by omega) w w' hw hw' hcopy hne))
  rw [h17, h26, h35, h44]



/-- Explicit nested sum for a concrete four-N boundary word. Factor
order is retained; only the terminal identity power has been removed. -/
private noncomputable def sg_trace_four_N_boundary_sum
    (m : ℕ) (K : Matrix (WSG m) (WSG m) ℂ)
    (a b c d : ℕ) : ℂ :=
  ∑ x, if (sgGlue m).g x then
    (∑ y, if (sgGlue m).g y then
      ((K ^ a) x y * (K ^ b) ((sgGlue m).σ y) ((sgGlue m).σ y)) *
        (K ^ c) y x else 0) *
      (K ^ d) ((sgGlue m).σ x) ((sgGlue m).σ x)
    else 0

/-- Concrete four-N boundary reduction under OAnti. The two required
corner powers are bounded by five, so the existing glued-corner spin
cancellation and the geometric estimate 5 < 2^m apply for m ≥ 3. -/
private theorem sg_trace_four_N_powers_boundary_sum
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d : ℕ) (hb : b ≤ 5) (hd : d ≤ 5) :
    Matrix.trace (sgK m θ ax o ^ a * (sgGlue m).N *
      sgK m θ ax o ^ b * (sgGlue m).N *
      sgK m θ ax o ^ c * (sgGlue m).N *
      sgK m θ ax o ^ d * (sgGlue m).N * sgK m θ ax o ^ 0) =
      sg_trace_four_N_boundary_sum m (sgK m θ ax o) a b c d := by
  let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
  have hkg : ∀ n, n ≤ 5 → ∀ w w',
      (sgGlue m).g w → (sgGlue m).g w' → w.1 = w'.1 → w ≠ w' →
        (K ^ n) w w' = 0 := by
    intro n hn w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_five_of_OAnti m hm θ ax o hanti
      n hn w w' hw hw' hcopy hne
  simpa [sg_trace_four_N_boundary_sum, K, pow_zero] using
    (trace_four_N_powers_explicit (sgGlue m) K
      (blockK_BD (Hc m θ ax o)) a b c d 0
      (by
        intro w w' hw hw' hcopy hne
        exact hkg b hb w w' hw hw' hcopy hne)
      (by
        intro w w' hw hw' hcopy hne
        exact hkg d hd w w' hw hw' hcopy hne))

/-- Complete four-N cyclic stratum of the p=8 ordered-word expansion.
The ten classes have exact multiplicities eight (eight classes), four
for the periodic class (1,3,1,3), and two for the alternating class
(2,2,2,2). This is a boundary identity, not an axis-cancellation claim. -/
theorem sg_trace_p8_four_N_stratum_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 5 * (sgGlue m).N * K ^ 0) +
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 4 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 4 * (sgGlue m).N * K ^ 0) +
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 4 * (sgGlue m).N * K ^ 0) +
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 3 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) +
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
      K ^ 3 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
    4 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) +
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) +
    2 * Matrix.trace (K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
    8 * sg_trace_four_N_boundary_sum m K 1 1 1 5 +
    8 * sg_trace_four_N_boundary_sum m K 1 1 4 2 +
    8 * sg_trace_four_N_boundary_sum m K 1 2 1 4 +
    8 * sg_trace_four_N_boundary_sum m K 1 1 2 4 +
    8 * sg_trace_four_N_boundary_sum m K 1 1 3 3 +
    8 * sg_trace_four_N_boundary_sum m K 1 3 2 2 +
    8 * sg_trace_four_N_boundary_sum m K 1 2 3 2 +
    4 * sg_trace_four_N_boundary_sum m K 1 3 1 3 +
    8 * sg_trace_four_N_boundary_sum m K 1 2 2 3 +
    2 * sg_trace_four_N_boundary_sum m K 2 2 2 2 := by
  dsimp
  rw [
    sg_trace_four_N_powers_boundary_sum m hm θ ax o hanti 1 1 1 5 (by omega) (by omega),
    sg_trace_four_N_powers_boundary_sum m hm θ ax o hanti 1 1 4 2 (by omega) (by omega),
    sg_trace_four_N_powers_boundary_sum m hm θ ax o hanti 1 2 1 4 (by omega) (by omega),
    sg_trace_four_N_powers_boundary_sum m hm θ ax o hanti 1 1 2 4 (by omega) (by omega),
    sg_trace_four_N_powers_boundary_sum m hm θ ax o hanti 1 1 3 3 (by omega) (by omega),
    sg_trace_four_N_powers_boundary_sum m hm θ ax o hanti 1 3 2 2 (by omega) (by omega),
    sg_trace_four_N_powers_boundary_sum m hm θ ax o hanti 1 2 3 2 (by omega) (by omega),
    sg_trace_four_N_powers_boundary_sum m hm θ ax o hanti 1 3 1 3 (by omega) (by omega),
    sg_trace_four_N_powers_boundary_sum m hm θ ax o hanti 1 2 2 3 (by omega) (by omega),
    sg_trace_four_N_powers_boundary_sum m hm θ ax o hanti 2 2 2 2 (by omega) (by omega)
  ]



/-- Complete six-N cyclic stratum of the eighth-moment expansion.
Its four run-length classes are (1,1,1,1,1,3), (1,1,1,1,2,2),
(1,1,1,2,1,2), and the period-two class (1,1,2,1,1,2), with
exact multiplicities eight, eight, eight, and four. -/
theorem sg_trace_p8_six_N_stratum_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    let D : ℕ → Matrix (WSG m) (WSG m) ℂ :=
      fun n => Matrix.diagonal (fun y => if (sgGlue m).g y then
        (K ^ n) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) +
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
    8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
    4 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 2 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
      K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
    8 * Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 1 * D 1 * K ^ 1 * D 3) +
    8 * Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 1 * D 1 * K ^ 2 * D 2) +
    8 * Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 1 * D 2 * K ^ 1 * D 2) +
    4 * Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 2 * D 1 * K ^ 1 * D 2) := by
  dsimp
  let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
  let D : ℕ → Matrix (WSG m) (WSG m) ℂ :=
    fun n => Matrix.diagonal (fun y => if (sgGlue m).g y then
      (K ^ n) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)
  have hkg : ∀ n, n ≤ 5 → ∀ w w',
      (sgGlue m).g w → (sgGlue m).g w' → w.1 = w'.1 → w ≠ w' →
        (K ^ n) w w' = 0 := by
    intro n hn w w' hw hw' hcopy hne
    exact sgK_pow_hkg_up_to_five_of_OAnti m hm θ ax o hanti
      n hn w w' hw hw' hcopy hne
  have h111113 :
      Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) =
      Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 1 * D 1 * K ^ 1 * D 3) := by
    simpa [D] using
      (trace_six_N_powers_boundary (sgGlue m) K
        (blockK_BD (Hc m θ ax o)) 1 1 1 1 1 3 0
        (by intro w w' hw hw' hcopy hne; exact hkg 1 (by omega) w w' hw hw' hcopy hne)
        (by intro w w' hw hw' hcopy hne; exact hkg 1 (by omega) w w' hw hw' hcopy hne)
        (by intro w w' hw hw' hcopy hne; exact hkg 3 (by omega) w w' hw hw' hcopy hne))
  have h111122 :
      Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
      Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 1 * D 1 * K ^ 2 * D 2) := by
    simpa [D] using
      (trace_six_N_powers_boundary (sgGlue m) K
        (blockK_BD (Hc m θ ax o)) 1 1 1 1 2 2 0
        (by intro w w' hw hw' hcopy hne; exact hkg 1 (by omega) w w' hw hw' hcopy hne)
        (by intro w w' hw hw' hcopy hne; exact hkg 1 (by omega) w w' hw hw' hcopy hne)
        (by intro w w' hw hw' hcopy hne; exact hkg 2 (by omega) w w' hw hw' hcopy hne))
  have h111212 :
      Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
      Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 1 * D 2 * K ^ 1 * D 2) := by
    simpa [D] using
      (trace_six_N_powers_boundary (sgGlue m) K
        (blockK_BD (Hc m θ ax o)) 1 1 1 2 1 2 0
        (by intro w w' hw hw' hcopy hne; exact hkg 1 (by omega) w w' hw hw' hcopy hne)
        (by intro w w' hw hw' hcopy hne; exact hkg 2 (by omega) w w' hw hw' hcopy hne)
        (by intro w w' hw hw' hcopy hne; exact hkg 2 (by omega) w w' hw hw' hcopy hne))
  have h112112 :
      Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 2 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) =
      Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 2 * D 1 * K ^ 1 * D 2) := by
    simpa [D] using
      (trace_six_N_powers_boundary (sgGlue m) K
        (blockK_BD (Hc m θ ax o)) 1 1 2 1 1 2 0
        (by intro w w' hw hw' hcopy hne; exact hkg 1 (by omega) w w' hw hw' hcopy hne)
        (by intro w w' hw hw' hcopy hne; exact hkg 1 (by omega) w w' hw hw' hcopy hne)
        (by intro w w' hw hw' hcopy hne; exact hkg 2 (by omega) w w' hw hw' hcopy hne))
  rw [h111113, h111122, h111212, h112112]



/-- Exact p=8 boundary correction assembled from all four even insertion
strata. The r=2 and r=4 strata are weighted corner sums, r=6 retains the
three ordered diagonal insertions, and r=8 is the fourth-power endpoint.
No cancellation or axis-independence is built into this definition. -/
noncomputable def glueRHS8
    (m : ℕ) (K : Matrix (WSG m) (WSG m) ℂ) : ℂ :=
  let D : ℕ → Matrix (WSG m) (WSG m) ℂ :=
    fun n => Matrix.diagonal (fun y => if (sgGlue m).g y then
      (K ^ n) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)
  8 * (∑ x, if (sgGlue m).g x then
    (K ^ 1) x x * (K ^ 7) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
  8 * (∑ x, if (sgGlue m).g x then
    (K ^ 2) x x * (K ^ 6) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
  8 * (∑ x, if (sgGlue m).g x then
    (K ^ 3) x x * (K ^ 5) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
  4 * (∑ x, if (sgGlue m).g x then
    (K ^ 4) x x * (K ^ 4) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0) +
  8 * sg_trace_four_N_boundary_sum m K 1 1 1 5 +
  8 * sg_trace_four_N_boundary_sum m K 1 1 4 2 +
  8 * sg_trace_four_N_boundary_sum m K 1 2 1 4 +
  8 * sg_trace_four_N_boundary_sum m K 1 1 2 4 +
  8 * sg_trace_four_N_boundary_sum m K 1 1 3 3 +
  8 * sg_trace_four_N_boundary_sum m K 1 3 2 2 +
  8 * sg_trace_four_N_boundary_sum m K 1 2 3 2 +
  4 * sg_trace_four_N_boundary_sum m K 1 3 1 3 +
  8 * sg_trace_four_N_boundary_sum m K 1 2 2 3 +
  2 * sg_trace_four_N_boundary_sum m K 2 2 2 2 +
  8 * Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 1 * D 1 * K ^ 1 * D 3) +
  8 * Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 1 * D 1 * K ^ 2 * D 2) +
  8 * Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 1 * D 2 * K ^ 1 * D 2) +
  4 * Matrix.trace (K ^ 0 * K ^ 1 * D 1 * K ^ 2 * D 1 * K ^ 1 * D 2) +
  (∑ x, if (sgGlue m).g x then
    (K x x * K ((sgGlue m).σ x) ((sgGlue m).σ x)) ^ 4 else 0)

/-- All even insertion strata of the eighth moment are reduced in one
identity. The coefficients are the exact cyclic orbit sizes from the
ordered-word inventory; periodic classes retain their shorter weights.
Odd strata and the full ordered expansion are intentionally separate. -/
theorem sg_trace_p8_all_even_strata_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    let E2 :=
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 7 * (sgGlue m).N * K ^ 0) +
      8 * Matrix.trace (K ^ 2 * (sgGlue m).N * K ^ 6 * (sgGlue m).N * K ^ 0) +
      8 * Matrix.trace (K ^ 3 * (sgGlue m).N * K ^ 5 * (sgGlue m).N * K ^ 0) +
      4 * Matrix.trace (K ^ 4 * (sgGlue m).N * K ^ 4 * (sgGlue m).N * K ^ 0)
    let E4 :=
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 5 * (sgGlue m).N * K ^ 0) +
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 4 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 4 * (sgGlue m).N * K ^ 0) +
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 2 * (sgGlue m).N * K ^ 4 * (sgGlue m).N * K ^ 0) +
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 3 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) +
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N *
        K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
        K ^ 3 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
      4 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) +
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
        K ^ 2 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) +
      2 * Matrix.trace (K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
        K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0)
    let E6 :=
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 3 * (sgGlue m).N * K ^ 0) +
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 2 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
      8 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0) +
      4 * Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 2 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 2 * (sgGlue m).N * K ^ 0)
    let E8 :=
      Matrix.trace (K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N *
        K ^ 1 * (sgGlue m).N * K ^ 1 * (sgGlue m).N * K ^ 0)
    E2 + E4 + E6 + E8 = glueRHS8 m K := by
  dsimp
  rw [sg_trace_p8_two_N_stratum_boundary m hm θ ax o hanti,
    sg_trace_p8_four_N_stratum_boundary m hm θ ax o hanti,
    sg_trace_p8_six_N_stratum_boundary m hm θ ax o hanti,
    sg_trace_p8_top_stratum_diagonal_fourth m hm θ ax o hanti]
  unfold glueRHS8
  rfl


-- The 16 odd cyclic classes need bounded reductions of at most seven K-factors.
set_option maxHeartbeats 2000000 in
/-- The complete odd-insertion part of the p=8 cyclic expansion vanishes.
The r=1 class is killed by the single-pairing trace lemma; r=3, r=5,
and r=7 classes are killed by the corresponding conditional multi-pairing
lemmas. All required middle powers are below 2^m for m >= 3. -/
theorem sg_trace_p8_odd_strata_zero
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    let N := (sgGlue m).N
8 * Matrix.trace (K * K * K * K * K * K * K * (K * N))
    + 8 * Matrix.trace (K * K * K * K * K * (K * N) * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * K * K * (K * N) * K * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * K * K * (K * N) * (K * N) * K * (K * N))
    + 8 * Matrix.trace (K * K * K * (K * N) * K * K * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * K * (K * N) * K * (K * N) * K * (K * N))
    + 8 * Matrix.trace (K * K * K * (K * N) * (K * N) * K * K * (K * N))
    + 8 * Matrix.trace (K * K * K * (K * N) * (K * N) * (K * N) * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * (K * N) * K * K * (K * N) * K * (K * N))
    + 8 * Matrix.trace (K * K * (K * N) * K * (K * N) * (K * N) * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * (K * N) * (K * N) * K * (K * N) * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * (K * N) * (K * N) * (K * N) * K * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * (K * N) * (K * N) * (K * N) * (K * N) * K * (K * N))
    + 8 * Matrix.trace (K * (K * N) * K * (K * N) * K * (K * N) * (K * N) * (K * N))
    + 8 * Matrix.trace (K * (K * N) * K * (K * N) * (K * N) * K * (K * N) * (K * N))
    + 8 * Matrix.trace (K * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) = 0 := by
  dsimp
  let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
  let N := (sgGlue m).N
  have hside : 7 < 2 ^ m := by
    calc
      7 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

  have hbd : BD (fun w : WSG m => w.1) K :=
    blockK_BD (Hc m θ ax o)
  have hkg : ∀ n, n ≤ 7 → ∀ w w',
      (sgGlue m).g w → (sgGlue m).g w' →
      w.1 = w'.1 → w ≠ w' → (K ^ n) w w' = 0 := by
    intro n hn w w' hw hw' hcopy hne
    exact sgK_pow_hkg_of_OAnti m n θ ax o hanti (by omega)
      w w' hw hw' hcopy hne
  have h3 (a b c d : ℕ) (hb : b ≤ 7) :
      Matrix.trace (K ^ a * N * K ^ b * N * K ^ c * N * K ^ d) = 0 := by
    have hxs : ∀ A, A ∈ ([K ^ a] : List (Matrix (WSG m) (WSG m) ℂ)) →
        BD (fun w : WSG m => w.1) A := by
      intro A hA
      simp only [List.mem_singleton] at hA
      subst A
      exact BD_pow K hbd a
    have hys : ∀ A, A ∈ ([K ^ c] : List (Matrix (WSG m) (WSG m) ℂ)) →
        BD (fun w : WSG m => w.1) A := by
      intro A hA
      simp only [List.mem_singleton] at hA
      subst A
      exact BD_pow K hbd c
    have hzs : ∀ A, A ∈ ([K ^ d] : List (Matrix (WSG m) (WSG m) ℂ)) →
        BD (fun w : WSG m => w.1) A := by
      intro A hA
      simp only [List.mem_singleton] at hA
      subst A
      exact BD_pow K hbd d
    simpa [List.prod_singleton, Matrix.mul_assoc] using
      (trace_three_N_word_zero (sgGlue m)
        ([K ^ a] : List (Matrix (WSG m) (WSG m) ℂ))
        ([K ^ c] : List (Matrix (WSG m) (WSG m) ℂ))
        ([K ^ d] : List (Matrix (WSG m) (WSG m) ℂ))
        (K ^ b) hxs hys hzs (BD_pow K hbd b) (hkg b hb))
  have h5 (a b c d e f : ℕ) (hb : b ≤ 7) (hd : d ≤ 7) :
      Matrix.trace (K ^ a * N * K ^ b * N * K ^ c * N *
        K ^ d * N * K ^ e * N * K ^ f) = 0 := by
    exact trace_five_N_powers_zero (sgGlue m) K hbd
      a b c d e f (hkg b hb) (hkg d hd)
  have h7 (a b c d e f g h : ℕ)
      (hb : b ≤ 7) (hd : d ≤ 7) (hf : f ≤ 7) :
      Matrix.trace (K ^ a * N * K ^ b * N * K ^ c * N *
        K ^ d * N * K ^ e * N * K ^ f * N * K ^ g * N * K ^ h) = 0 := by
    exact trace_seven_N_powers_zero (sgGlue m) K hbd
      a b c d e f g h (hkg b hb) (hkg d hd) (hkg f hf)

  have hrot_00000111 :
      Matrix.trace (K * K * K * K * K * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 1 * N * K ^ 6) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K, K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h3_00000111 : Matrix.trace (K * K * K * K * K * (K * N) * (K * N) * (K * N)) = 0 := by
    rw [hrot_00000111]
    exact h3 0 1 1 6 (by omega)

  have hrot_00001011 :
      Matrix.trace (K * K * K * K * (K * N) * K * (K * N) * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 5 * N * K ^ 2) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h3_00001011 : Matrix.trace (K * K * K * K * (K * N) * K * (K * N) * (K * N)) = 0 := by
    rw [hrot_00001011]
    exact h3 0 1 5 2 (by omega)

  have hrot_00001101 :
      Matrix.trace (K * K * K * K * (K * N) * (K * N) * K * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 2 * N * K ^ 5) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, N, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h3_00001101 : Matrix.trace (K * K * K * K * (K * N) * (K * N) * K * (K * N)) = 0 := by
    rw [hrot_00001101]
    exact h3 0 1 2 5 (by omega)

  have hrot_00010011 :
      Matrix.trace (K * K * K * (K * N) * K * K * (K * N) * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 4 * N * K ^ 3) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, K, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h3_00010011 : Matrix.trace (K * K * K * (K * N) * K * K * (K * N) * (K * N)) = 0 := by
    rw [hrot_00010011]
    exact h3 0 1 4 3 (by omega)

  have hrot_00010101 :
      Matrix.trace (K * K * K * (K * N) * K * (K * N) * K * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 2 * N * K ^ 2 * N * K ^ 4) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, K, N, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h3_00010101 : Matrix.trace (K * K * K * (K * N) * K * (K * N) * K * (K * N)) = 0 := by
    rw [hrot_00010101]
    exact h3 0 2 2 4 (by omega)

  have hrot_00011001 :
      Matrix.trace (K * K * K * (K * N) * (K * N) * K * K * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 3 * N * K ^ 4) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, N, K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h3_00011001 : Matrix.trace (K * K * K * (K * N) * (K * N) * K * K * (K * N)) = 0 := by
    rw [hrot_00011001]
    exact h3 0 1 3 4 (by omega)

  have hrot_00100101 :
      Matrix.trace (K * K * (K * N) * K * K * (K * N) * K * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 2 * N * K ^ 3 * N * K ^ 3) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, K, K, N, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h3_00100101 : Matrix.trace (K * K * (K * N) * K * K * (K * N) * K * (K * N)) = 0 := by
    rw [hrot_00100101]
    exact h3 0 2 3 3 (by omega)

  have hrot_00011111 :
      Matrix.trace (K * K * K * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 4) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, N, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h5_00011111 : Matrix.trace (K * K * K * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) = 0 := by
    rw [hrot_00011111]
    exact h5 0 1 1 1 1 4 (by omega) (by omega)

  have hrot_00101111 :
      Matrix.trace (K * K * (K * N) * K * (K * N) * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 3 * N * K ^ 2) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, K, N, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h5_00101111 : Matrix.trace (K * K * (K * N) * K * (K * N) * (K * N) * (K * N) * (K * N)) = 0 := by
    rw [hrot_00101111]
    exact h5 0 1 1 1 3 2 (by omega) (by omega)

  have hrot_00110111 :
      Matrix.trace (K * K * (K * N) * (K * N) * K * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 1 * N * K ^ 3 * N * K ^ 1 * N * K ^ 2) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, N, K, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h5_00110111 : Matrix.trace (K * K * (K * N) * (K * N) * K * (K * N) * (K * N) * (K * N)) = 0 := by
    rw [hrot_00110111]
    exact h5 0 1 1 3 1 2 (by omega) (by omega)

  have hrot_00111011 :
      Matrix.trace (K * K * (K * N) * (K * N) * (K * N) * K * (K * N) * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 1 * N * K ^ 2 * N * K ^ 1 * N * K ^ 3) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, N, K, N, K, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h5_00111011 : Matrix.trace (K * K * (K * N) * (K * N) * (K * N) * K * (K * N) * (K * N)) = 0 := by
    rw [hrot_00111011]
    exact h5 0 1 1 2 1 3 (by omega) (by omega)

  have hrot_00111101 :
      Matrix.trace (K * K * (K * N) * (K * N) * (K * N) * (K * N) * K * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 2 * N * K ^ 3) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, N, K, N, K, N, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h5_00111101 : Matrix.trace (K * K * (K * N) * (K * N) * (K * N) * (K * N) * K * (K * N)) = 0 := by
    rw [hrot_00111101]
    exact h5 0 1 1 1 2 3 (by omega) (by omega)

  have hrot_01010111 :
      Matrix.trace (K * (K * N) * K * (K * N) * K * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 1 * N * K ^ 2 * N * K ^ 2 * N * K ^ 2) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, K, N, K, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h5_01010111 : Matrix.trace (K * (K * N) * K * (K * N) * K * (K * N) * (K * N) * (K * N)) = 0 := by
    rw [hrot_01010111]
    exact h5 0 1 1 2 2 2 (by omega) (by omega)

  have hrot_01011011 :
      Matrix.trace (K * (K * N) * K * (K * N) * (K * N) * K * (K * N) * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 2 * N * K ^ 1 * N * K ^ 2 * N * K ^ 2) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, K, N, K, N, K, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h5_01011011 : Matrix.trace (K * (K * N) * K * (K * N) * (K * N) * K * (K * N) * (K * N)) = 0 := by
    rw [hrot_01011011]
    exact h5 0 1 2 1 2 2 (by omega) (by omega)

  have hrot_01111111 :
      Matrix.trace (K * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 0 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 2) := by
    simpa [Matrix.mul_assoc, pow_zero, Matrix.one_mul, pow_succ] using
      (trace_cyclic_list ([K, K] : List (Matrix (WSG m) (WSG m) ℂ)) ([N, K, N, K, N, K, N, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))

  have h7_01111111 : Matrix.trace (K * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) = 0 := by
    rw [hrot_01111111]
    exact h7 0 1 1 1 1 1 1 2 (by omega) (by omega) (by omega)

  have h1_00000001 : Matrix.trace (K * K * K * K * K * K * K * (K * N)) = 0 := by
    simpa [pow_succ, Matrix.mul_assoc] using
      (trace_pow_mul_N_zero (sgGlue m) K
        (blockK_BD (Hc m θ ax o)) 8)

  linear_combination 8 * h1_00000001 + 8 * h3_00000111 + 8 * h3_00001011 + 8 * h3_00001101 + 8 * h3_00010011 + 8 * h3_00010101 + 8 * h3_00011001 + 8 * h3_00100101 + 8 * h5_00011111 + 8 * h5_00101111 + 8 * h5_00110111 + 8 * h5_00111011 + 8 * h5_00111101 + 8 * h5_01010111 + 8 * h5_01011011 + 8 * h7_01111111


-- This proof checks the 20 even cyclic rotations and their exact orbit weights.
set_option maxHeartbeats 2000000 in
/-- Complete eighth-moment cyclic trace split for the glued matrix sum.
The ordered expansion is grouped into all 36 cyclic classes; the odd
classes vanish under OAnti and every even class is reduced to glueRHS8.
This is a level-local trace identity, not yet an all-level recurrence. -/
theorem sg_trace_p8_ordered_expansion_boundary
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
    Matrix.trace ((K + K * (sgGlue m).N) ^ 8) =
      Matrix.trace (K ^ 8) + glueRHS8 m K := by
  dsimp
  let K : Matrix (WSG m) (WSG m) ℂ := sgK m θ ax o
  let N := (sgGlue m).N

  let E2 :=
    8 * Matrix.trace (K ^ 1 * N * K ^ 7 * N) +
    8 * Matrix.trace (K ^ 2 * N * K ^ 6 * N) +
    8 * Matrix.trace (K ^ 3 * N * K ^ 5 * N) +
    4 * Matrix.trace (K ^ 4 * N * K ^ 4 * N)
  let E4 :=
    8 * Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 5 * N) +
    8 * Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 4 * N * K ^ 2 * N) +
    8 * Matrix.trace (K ^ 1 * N * K ^ 2 * N * K ^ 1 * N * K ^ 4 * N) +
    8 * Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 2 * N * K ^ 4 * N) +
    8 * Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 3 * N * K ^ 3 * N) +
    8 * Matrix.trace (K ^ 1 * N * K ^ 3 * N * K ^ 2 * N * K ^ 2 * N) +
    8 * Matrix.trace (K ^ 1 * N * K ^ 2 * N * K ^ 3 * N * K ^ 2 * N) +
    4 * Matrix.trace (K ^ 1 * N * K ^ 3 * N * K ^ 1 * N * K ^ 3 * N) +
    8 * Matrix.trace (K ^ 1 * N * K ^ 2 * N * K ^ 2 * N * K ^ 3 * N) +
    2 * Matrix.trace (K ^ 2 * N * K ^ 2 * N * K ^ 2 * N * K ^ 2 * N)
  let E6 :=
    8 * Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N *
      K ^ 1 * N * K ^ 1 * N * K ^ 3 * N) +
    8 * Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N *
      K ^ 1 * N * K ^ 2 * N * K ^ 2 * N) +
    8 * Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N *
      K ^ 2 * N * K ^ 1 * N * K ^ 2 * N) +
    4 * Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 2 * N *
      K ^ 1 * N * K ^ 1 * N * K ^ 2 * N)
  let E8 :=
    Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N *
      K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N)


  have hrot_even_00000011 :
      Matrix.trace (K * K * K * K * K * K * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 7 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, K, K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00000101 :
      Matrix.trace (K * K * K * K * K * (K * N) * K * (K * N)) =
        Matrix.trace (K ^ 2 * N * K ^ 6 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00001001 :
      Matrix.trace (K * K * K * K * (K * N) * K * K * (K * N)) =
        Matrix.trace (K ^ 3 * N * K ^ 5 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00001111 :
      Matrix.trace (K * K * K * K * (K * N) * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 5 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00010001 :
      Matrix.trace (K * K * K * (K * N) * K * K * K * (K * N)) =
        Matrix.trace (K ^ 4 * N * K ^ 4 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00010111 :
      Matrix.trace (K * K * K * (K * N) * K * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 4 * N * K ^ 2 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00011011 :
      Matrix.trace (K * K * K * (K * N) * (K * N) * K * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 2 * N * K ^ 1 * N * K ^ 4 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, N, K, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00011101 :
      Matrix.trace (K * K * K * (K * N) * (K * N) * (K * N) * K * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 2 * N * K ^ 4 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, N, K, N, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00100111 :
      Matrix.trace (K * K * (K * N) * K * K * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 3 * N * K ^ 3 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, K, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00101011 :
      Matrix.trace (K * K * (K * N) * K * (K * N) * K * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 3 * N * K ^ 2 * N * K ^ 2 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, K, N, K, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00101101 :
      Matrix.trace (K * K * (K * N) * K * (K * N) * (K * N) * K * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 2 * N * K ^ 3 * N * K ^ 2 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, K, N, K, N, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00110011 :
      Matrix.trace (K * K * (K * N) * (K * N) * K * K * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 3 * N * K ^ 1 * N * K ^ 3 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, N, K, K, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00110101 :
      Matrix.trace (K * K * (K * N) * (K * N) * K * (K * N) * K * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 2 * N * K ^ 2 * N * K ^ 3 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, N, K, K, N, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_00111111 :
      Matrix.trace (K * K * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 3 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, N, K, N, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_01010101 :
      Matrix.trace (K * (K * N) * K * (K * N) * K * (K * N) * K * (K * N)) =
        Matrix.trace (K ^ 2 * N * K ^ 2 * N * K ^ 2 * N * K ^ 2 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, K, N, K, K, N, K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_01011111 :
      Matrix.trace (K * (K * N) * K * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 2 * N * K ^ 2 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, K, N, K, N, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_01101111 :
      Matrix.trace (K * (K * N) * (K * N) * K * (K * N) * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 2 * N * K ^ 1 * N * K ^ 2 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, N, K, K, N, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_01110111 :
      Matrix.trace (K * (K * N) * (K * N) * (K * N) * K * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 2 * N * K ^ 1 * N * K ^ 1 * N * K ^ 2 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, N, K, N, K, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hrot_even_11111111 :
      Matrix.trace ((K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) =
        Matrix.trace (K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N * K ^ 1 * N) := by
    simpa [Matrix.mul_assoc, pow_succ, pow_one, pow_zero,
      Matrix.one_mul, Matrix.mul_one] using
      (trace_cyclic_list ([K, N] : List (Matrix (WSG m) (WSG m) ℂ)) ([K, N, K, N, K, N, K, N, K, N, K, N, K, N] : List (Matrix (WSG m) (WSG m) ℂ)))


  have hEvenRep :
      8 * Matrix.trace (K * K * K * K * K * K * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * K * K * K * (K * N) * K * (K * N))
    + 8 * Matrix.trace (K * K * K * K * (K * N) * K * K * (K * N))
    + 8 * Matrix.trace (K * K * K * K * (K * N) * (K * N) * (K * N) * (K * N))
    + 4 * Matrix.trace (K * K * K * (K * N) * K * K * K * (K * N))
    + 8 * Matrix.trace (K * K * K * (K * N) * K * (K * N) * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * K * (K * N) * (K * N) * K * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * K * (K * N) * (K * N) * (K * N) * K * (K * N))
    + 8 * Matrix.trace (K * K * (K * N) * K * K * (K * N) * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * (K * N) * K * (K * N) * K * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * (K * N) * K * (K * N) * (K * N) * K * (K * N))
    + 4 * Matrix.trace (K * K * (K * N) * (K * N) * K * K * (K * N) * (K * N))
    + 8 * Matrix.trace (K * K * (K * N) * (K * N) * K * (K * N) * K * (K * N))
    + 8 * Matrix.trace (K * K * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N))
    + 2 * Matrix.trace (K * (K * N) * K * (K * N) * K * (K * N) * K * (K * N))
    + 8 * Matrix.trace (K * (K * N) * K * (K * N) * (K * N) * (K * N) * (K * N) * (K * N))
    + 8 * Matrix.trace (K * (K * N) * (K * N) * K * (K * N) * (K * N) * (K * N) * (K * N))
    + 4 * Matrix.trace (K * (K * N) * (K * N) * (K * N) * K * (K * N) * (K * N) * (K * N))
    + 1 * Matrix.trace ((K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) =
        E2 + E4 + E6 + E8 := by
    simp [E2, E4, E6, E8, pow_zero, Matrix.mul_one, Matrix.mul_assoc]
    linear_combination 8 * hrot_even_00000011 + 8 * hrot_even_00000101 + 8 * hrot_even_00001001 + 8 * hrot_even_00001111 + 4 * hrot_even_00010001 + 8 * hrot_even_00010111 + 8 * hrot_even_00011011 + 8 * hrot_even_00011101 + 8 * hrot_even_00100111 + 8 * hrot_even_00101011 + 8 * hrot_even_00101101 + 4 * hrot_even_00110011 + 8 * hrot_even_00110101 + 8 * hrot_even_00111111 + 2 * hrot_even_01010101 + 8 * hrot_even_01011111 + 8 * hrot_even_01101111 + 4 * hrot_even_01110111 + 1 * hrot_even_11111111


  have hOdd :
      8 * Matrix.trace (K * K * K * K * K * K * K * (K * N)) +
      8 * Matrix.trace (K * K * K * K * K * (K * N) * (K * N) * (K * N)) +
      8 * Matrix.trace (K * K * K * K * (K * N) * K * (K * N) * (K * N)) +
      8 * Matrix.trace (K * K * K * (K * N) * K * K * (K * N) * (K * N)) +
      8 * Matrix.trace (K * K * K * (K * N) * K * (K * N) * K * (K * N)) +
      8 * Matrix.trace (K * K * (K * N) * K * K * (K * N) * K * (K * N)) +
      8 * Matrix.trace (K * K * (K * N) * K * (K * N) * K * (K * N) * K) +
      8 * Matrix.trace (K * K * (K * N) * K * (K * N) * (K * N) * K) +
      8 * Matrix.trace (K * (K * N) * K * (K * N) * K * (K * N) * K * (K * N)) +
      8 * Matrix.trace (K * (K * N) * K * (K * N) * K * (K * N) * (K * N)) +
      8 * Matrix.trace (K * (K * N) * K * (K * N) * (K * N) * K * (K * N)) +
      8 * Matrix.trace (K * (K * N) * (K * N) * K * (K * N) * K * (K * N)) +
      8 * Matrix.trace (K * (K * N) * (K * N) * (K * N) * K * (K * N) * K) +
      8 * Matrix.trace ((K * N) * K * (K * N) * K * (K * N) * (K * N) * K) +
      8 * Matrix.trace ((K * N) * K * (K * N) * (K * N) * K * (K * N) * K) +
      8 * Matrix.trace ((K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N) * (K * N)) = 0 := by
    simpa [Matrix.mul_assoc] using
      (sg_trace_p8_odd_strata_zero m hm θ ax o hanti)


  have hAll : E2 + E4 + E6 + E8 = glueRHS8 m K := by
    simpa [E2, E4, E6, E8, pow_zero, Matrix.mul_one,
      Matrix.mul_assoc] using
      (sg_trace_p8_all_even_strata_boundary m hm θ ax o hanti)
  have hCyclicSplit :
      ((orderedWordExpansion K (K * N) 8).map Matrix.trace).sum =
        Matrix.trace (K ^ 8) + E2 + E4 + E6 + E8 := by
    rw [trace_orderedWordExpansion_eight_cyclic K (K * N)]
    linear_combination hOdd + hEvenRep
  calc
    Matrix.trace ((K + K * N) ^ 8) =
        ((orderedWordExpansion K (K * N) 8).map Matrix.trace).sum :=
      trace_orderedWordExpansion K (K * N) 8
    _ = Matrix.trace (K ^ 8) + E2 + E4 + E6 + E8 := hCyclicSplit
    _ = Matrix.trace (K ^ 8) + glueRHS8 m K := by rw [hAll]

/-- The p=10 four-N word, reduced to its exact nested corner sum.
The only hypotheses are the two required middle-power corner conditions;
for the concrete Sierpinski operator they follow from OAnti and m ≥ 4. -/
end EvgenyTheorem
