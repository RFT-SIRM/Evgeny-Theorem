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
  exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
    n hn w w' hw hw' hcopy hne


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
  exact sgK_pow_hkg_up_to_nine_of_OAnti m hm θ ax o hanti
    n hn w w' hw hw' hcopy hne


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

end EvgenyTheorem
