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
  rw [Matrix.trace, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp [Matrix.trace, Matrix.diag, blockK]

/-- Powers of a block-diagonal matrix are computed independently in each block. -/
theorem blockK_pow (H : ι → Matrix X X ℂ) (n : ℕ) :
    blockK H ^ n = blockK (fun c => H c ^ n) := by
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

end EvgenyTheorem
