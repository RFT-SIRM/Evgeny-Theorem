import EvgenyTheorem.GlueK
import EvgenyTheorem.EdgeStep
import EvgenyTheorem.OrientSq
import EvgenyTheorem.PairUnit

/-!
# Corner hypotheses `hkg` and `hu2` for the glued operator

* `hkg`: two distinct glued points of one copy are either the same point with different spin
  (diagonal entry, spin-diagonal) or two distinct corners (not adjacent for `m ≥ 1`).
* `hu2`: for the same point and different spins, `(K·K)` vanishes by the edge identity
  `pHeO_edge_mul'`; for two distinct corners of one copy the two partners lie in different
  copies, so the hypothesis of `GlueDiag` is never satisfied.
-/

namespace EvgenyTheorem

open Matrix

/-! ### Corners -/

theorem glued_corner {m : ℕ} {w : WSG m} (h : (sgGlue m).g w) :
    w.2.1.1 = (0, 0) ∨ w.2.1.1 = (2 ^ m, 0) ∨ w.2.1.1 = (0, 2 ^ m) := by
  have h' : ∃ w', glW m w w' := h
  obtain ⟨w', hw'⟩ := h'
  have hg : gl m w.1 w.2.1.1 w'.1 w'.2.1.1 := hw'.1
  rcases hg with ⟨_, b, _, _⟩ | ⟨_, b, _, _⟩ | ⟨_, b, _, _⟩ | ⟨_, b, _, _⟩ |
    ⟨_, b, _, _⟩ | ⟨_, b, _, _⟩
  · exact Or.inr (Or.inl b)
  · exact Or.inl b
  · exact Or.inr (Or.inr b)
  · exact Or.inl b
  · exact Or.inr (Or.inr b)
  · exact Or.inr (Or.inl b)

theorem corners_far {m : ℕ} (hm : 1 ≤ m) {p q : Point}
    (hp : p = (0, 0) ∨ p = (2 ^ m, 0) ∨ p = (0, 2 ^ m))
    (hq : q = (0, 0) ∨ q = (2 ^ m, 0) ∨ q = (0, 2 ^ m))
    (hne : p ≠ q) : ¬ EdgeB m p.1 p.2 q.1 q.2 = true := by
  intro hE
  have hd := EdgeB_dist hE
  have h2 : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    first
      | exact hne rfl
      | (dsimp only at hd; omega)
      | (simp at hd; omega)

/-- The two glued corners of one copy have partners in different copies. -/
theorem gl_partner_inj {m : ℕ} {c c1 c2 : GCopy} {p q p1 q1 : Point}
    (h1 : gl m c p c1 p1) (h2 : gl m c q c2 q1) (hc : c1 = c2) : p = q := by
  subst hc
  cases c <;> cases c1 <;> simp [gl, Prod.ext_iff] at h1 h2 ⊢ <;> omega

/-! ### Entries of `Hc` -/

theorem Hc_zero_diag (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (c : GCopy) (x y : Pt m × C2) (hp : x.1.1 = y.1.1) (hs : x.2 ≠ y.2) :
    Hc m θ ax o c x y = 0 := by
  cases c
  · show pHeO m θ ax o x.1.1 y.1.1 x.2 y.2 = 0
    rw [hp, pHeO_diag, if_neg hs]
  · show pHeO m θ ax (oBo m o) x.1.1 y.1.1 x.2 y.2 = 0
    rw [hp, pHeO_diag, if_neg hs]
  · show pHeO m θ ax (oCo m o) x.1.1 y.1.1 x.2 y.2 = 0
    rw [hp, pHeO_diag, if_neg hs]

theorem Hc_zero_edge (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (c : GCopy) (x y : Pt m × C2) (hpq : x.1.1 ≠ y.1.1)
    (hE : ¬ EdgeB m x.1.1.1 x.1.1.2 y.1.1.1 y.1.1.2 = true) :
    Hc m θ ax o c x y = 0 := by
  cases c
  · exact pHeO_zero_of_not_edge m θ ax o hpq hE x.2 y.2
  · exact pHeO_zero_of_not_edge m θ ax (oBo m o) hpq hE x.2 y.2
  · exact pHeO_zero_of_not_edge m θ ax (oCo m o) hpq hE x.2 y.2

/-- A nonzero `sgK` entry either preserves the geometric coordinate or follows an
edge of the Sierpinski graph. This is the one-step support lemma used by the
higher-power support induction. -/
theorem sgK_entry_local (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] (w w' : WSG m)
    (h : sgK m θ ax o w w' ≠ 0) :
    w.2.1.1 = w'.2.1.1 ∨
      EdgeB m w.2.1.1.1 w.2.1.1.2 w'.2.1.1.1 w'.2.1.1.2 = true := by
  by_cases hc : w.1 = w'.1
  · have e : sgK m θ ax o w w' = Hc m θ ax o w.1 w.2 w'.2 := by
      show (if w.1 = w'.1 then Hc m θ ax o w.1 w.2 w'.2 else 0) = _
      rw [if_pos hc]
    by_cases hp : w.2.1.1 = w'.2.1.1
    · exact Or.inl hp
    · right
      by_contra hE
      have hz := Hc_zero_edge m θ ax o w.1 w.2 w'.2 hp hE
      apply h
      rw [e, hz]
  · have hz : sgK m θ ax o w w' = 0 := by
      simp [sgK, blockK, hc]
    exact (h hz).elim

/-- A nonzero one-step `sgK` entry changes each lattice coordinate by at most one.
This combines `sgK_entry_local` with the six-direction bound for `EdgeB`. -/
theorem sgK_entry_coord_dist (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] (w w' : WSG m)
    (h : sgK m θ ax o w w' ≠ 0) :
    w.2.1.1.1 ≤ w'.2.1.1.1 + 1 ∧ w'.2.1.1.1 ≤ w.2.1.1.1 + 1 ∧
    w.2.1.1.2 ≤ w'.2.1.1.2 + 1 ∧ w'.2.1.1.2 ≤ w.2.1.1.2 + 1 := by
  rcases sgK_entry_local m θ ax o w w' h with hp | hE
  · simp only [hp]
    omega
  · exact EdgeB_dist hE

/-! ### `hkg` -/

theorem sgK_hkg (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] :
    ∀ w w', (sgGlue m).g w → (sgGlue m).g w' → w.1 = w'.1 → w ≠ w' →
      sgK m θ ax o w w' = 0 := by
  intro w w' hw hw' hc hne
  have e : sgK m θ ax o w w' = Hc m θ ax o w.1 w.2 w'.2 := by
    show (if w.1 = w'.1 then Hc m θ ax o w.1 w.2 w'.2 else 0) = _
    rw [if_pos hc]
  rw [e]
  by_cases hp : w.2.1.1 = w'.2.1.1
  · have hs : w.2.2 ≠ w'.2.2 := fun h => hne (Prod.ext hc (Prod.ext (Subtype.ext hp) h))
    exact Hc_zero_diag m θ ax o w.1 w.2 w'.2 hp hs
  · exact Hc_zero_edge m θ ax o w.1 w.2 w'.2 hp
      (corners_far hm (glued_corner hw) (glued_corner hw') hp)

/-- Any two distinct glued states have zero one-step sgK coupling.
Within one copy this is sgK_hkg; across different copies it follows from
the block-diagonal definition of sgK. -/
theorem sgK_glued_offdiag (m : ℕ) (hm : 1 ≤ m) (θ : ℝ)
    (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    (w w' : WSG m) (hw : (sgGlue m).g w) (hw' : (sgGlue m).g w')
    (hne : w ≠ w') :
    sgK m θ ax o w w' = 0 := by
  by_cases hc : w.1 = w'.1
  · exact sgK_hkg m hm θ ax o w w' hw hw' hc hne
  · have hz : sgK m θ ax o w w' = 0 := by
      simp [sgK, blockK, hc]
    exact hz

/-! ### `hu2` -/

theorem blockK_mul_same {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
    (H : ι → Matrix X X ℂ) (w w' : ι × X) (hc : w.1 = w'.1) :
    (blockK H * blockK H) w w' = (H w.1 * H w.1) w.2 w'.2 := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single w.1]
  · refine Finset.sum_congr rfl (fun y _ => ?_)
    simp [blockK, hc]
  · intro c _ hne
    refine Finset.sum_eq_zero (fun y _ => ?_)
    have : w.1 ≠ c := fun h => hne h.symm
    simp [blockK, this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem local_sq_zero (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (oo : Point → Point → Prop)
    [DecidableRel oo] (hanti : OAnti m oo) (p : Point) (x : Pt m) (s s' : C2) (hs : s ≠ s') :
    ∑ t : C2, pHeO m θ ax oo p x.1 s t * pHeO m θ ax oo x.1 p t s' = 0 := by
  by_cases hx : p = x.1
  · apply Finset.sum_eq_zero
    intro t _
    rw [← hx, pHeO_diag, pHeO_diag]
    by_cases h1 : s = t
    · have h2 : ¬ t = s' := fun h => hs (h1.trans h)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · by_cases hE : EdgeB m p.1 p.2 x.1.1 x.1.2 = true
    · rw [pHeO_edge_mul' m θ ax oo hanti hx hE s s', if_neg hs]
    · apply Finset.sum_eq_zero
      intro t _
      rw [pHeO_zero_of_not_edge m θ ax oo hx hE s t, zero_mul]

theorem sq_zero_gen (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (oo : Point → Point → Prop)
    [DecidableRel oo] (hanti : OAnti m oo) (M : Matrix (Pt m × C2) (Pt m × C2) ℂ)
    (hM : ∀ x y, M x y = pHeO m θ ax oo x.1.1 y.1.1 x.2 y.2)
    (a b : Pt m × C2) (hab : a.1.1 = b.1.1) (hs : a.2 ≠ b.2) : (M * M) a b = 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro x _
  simp only [hM]
  rw [← hab]
  exact local_sq_zero m θ ax oo hanti a.1.1 x a.2 b.2 hs

theorem oanti_A (m : ℕ) (o : Point → Point → Prop) (hanti : OAnti (m + 1) o) : OAnti m o := by
  intro p q hp hq hpq
  have hp' : p ∈ vertexOrder (m + 1) := by
    have := GCopy.shift_mem m GCopy.A hp
    rwa [shiftA_eq] at this
  have hq' : q ∈ vertexOrder (m + 1) := by
    have := GCopy.shift_mem m GCopy.A hq
    rwa [shiftA_eq] at this
  exact hanti p q hp' hq' hpq

theorem oanti_B (m : ℕ) (o : Point → Point → Prop) (hanti : OAnti (m + 1) o) :
    OAnti m (oBo m o) := by
  intro p q hp hq hpq
  have hne : GCopy.B.shift m p ≠ GCopy.B.shift m q :=
    fun h => hpq (GCopy.shift_inj m GCopy.B h)
  exact hanti _ _ (GCopy.shift_mem m GCopy.B hp) (GCopy.shift_mem m GCopy.B hq) hne

theorem oanti_C (m : ℕ) (o : Point → Point → Prop) (hanti : OAnti (m + 1) o) :
    OAnti m (oCo m o) := by
  intro p q hp hq hpq
  have hne : GCopy.C.shift m p ≠ GCopy.C.shift m q :=
    fun h => hpq (GCopy.shift_inj m GCopy.C h)
  exact hanti _ _ (GCopy.shift_mem m GCopy.C hp) (GCopy.shift_mem m GCopy.C hq) hne

/-! ### Hermiticity of the concrete copy operators -/

/-- Antisymmetry at level m + 1 descends to each copy orientation, so each
concrete copy operator is Hermitian. This discharges the operator-level premise
used by the all-powers spin-block cancellation lemma. -/
theorem Hc_hermitian_of_OAnti (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) (c : GCopy) :
    Matrix.conjTranspose (Hc m θ ax o c) = Hc m θ ax o c := by
  cases c with
  | A =>
      change Matrix.conjTranspose (pOpO m θ ax o) = pOpO m θ ax o
      exact pOpO_hermitian_of_OAnti m θ ax o (oanti_A m o hanti)
  | B =>
      change Matrix.conjTranspose (pOpO m θ ax (oBo m o)) =
        pOpO m θ ax (oBo m o)
      exact pOpO_hermitian_of_OAnti m θ ax (oBo m o) (oanti_B m o hanti)
  | C =>
      change Matrix.conjTranspose (pOpO m θ ax (oCo m o)) =
        pOpO m θ ax (oCo m o)
      exact pOpO_hermitian_of_OAnti m θ ax (oCo m o) (oanti_C m o hanti)

/-- The concrete glued operator is Hermitian whenever the orientation
relation is antisymmetric at the parent level. -/
theorem sgK_hermitian_of_OAnti (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    Matrix.conjTranspose (sgK m θ ax o) = sgK m θ ax o := by
  ext w w'
  by_cases hc : w.1 = w'.1
  · have hH := Hc_hermitian_of_OAnti m θ ax o hanti w'.1
    have hentry := congrFun (congrFun hH w.2) w'.2
    simpa [sgK, blockK, Matrix.conjTranspose_apply, hc] using hentry
  · have hrev : w'.1 ≠ w.1 := by
      intro h
      exact hc h.symm
    simp [sgK, blockK, Matrix.conjTranspose_apply, hc, hrev]

/-- Reversing any expanded K/N word conjugates its trace in the concrete
glued model. This records the exact adjoint symmetry needed for the reversal
orbits in the p=6,8,10 ledger; it does not claim that each trace is real. -/
theorem trace_sgK_N_word_reverse_of_OAnti
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (xs : List (Matrix (WSG m) (WSG m) ℂ))
    (hxs : ∀ M, M ∈ xs → M = sgK m θ ax o ∨ M = (sgGlue m).N) :
    star (Matrix.trace xs.prod) = Matrix.trace xs.reverse.prod := by
  exact trace_K_N_word_reverse (sgK m θ ax o) ((sgGlue m).N)
    (sgK_hermitian_of_OAnti m θ ax o hanti)
    (GlueData.N_hermitian (sgGlue m)) xs hxs

/-- For every natural power, the same-point opposite-spin entry in a glued
copy vanishes under the original level's orientation-antisymmetry hypothesis.
This combines concrete Hermiticity with quaternionic spin-block closure. -/
theorem sgK_pow_samePoint_spinOffdiag_zero_of_OAnti
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) (c : GCopy) (n : ℕ) (p : Pt m) :
    (sgK m θ ax o ^ n) (c, (p, (0 : C2))) (c, (p, (1 : C2))) = 0 := by
  exact sgK_pow_samePoint_spinOffdiag_zero m θ ax o
    (fun c' => Hc_hermitian_of_OAnti m θ ax o hanti c') c n p

/-! ### All-power glued-corner vanishing -/

/-- Hermiticity transfers the quaternion-form cancellation to either ordering
of distinct spin states at the same geometric point. -/
theorem Hc_pow_samePoint_spinOffdiag_zero_any
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) (c : GCopy) (n : ℕ)
    (p : Pt m) (s t : C2) (hst : s ≠ t) :
    (Hc m θ ax o c ^ n) (p, s) (p, t) = 0 := by
  have hH : ∀ c' : GCopy,
      Matrix.conjTranspose (Hc m θ ax o c') = Hc m θ ax o c' :=
    fun c' => Hc_hermitian_of_OAnti m θ ax o hanti c'
  have hpow : Matrix.conjTranspose ((Hc m θ ax o c) ^ n) =
      (Hc m θ ax o c) ^ n := by
    rw [Matrix.conjTranspose_pow, hH c]
  have h01 :
      (Hc m θ ax o c ^ n) (p, (0 : C2)) (p, (1 : C2)) = 0 :=
    Hc_pow_samePoint_spinOffdiag_zero m θ ax o hH c n p
  have h10 :
      (Hc m θ ax o c ^ n) (p, (1 : C2)) (p, (0 : C2)) = 0 := by
    have h := congrFun (congrFun hpow (p, (0 : C2))) (p, (1 : C2))
    have hstar :
        star ((Hc m θ ax o c ^ n) (p, (1 : C2)) (p, (0 : C2))) =
          (Hc m θ ax o c ^ n) (p, (0 : C2)) (p, (1 : C2)) := by
      simpa [Matrix.conjTranspose_apply] using h
    rw [h01] at hstar
    exact star_eq_zero.mp hstar
  fin_cases s <;> fin_cases t <;> simp_all

/-- Under orientation antisymmetry, every natural power of the glued operator
satisfies the corner-vanishing condition needed by the three-pairing reduction. -/
theorem sgK_pow_GlueDiag_of_OAnti
    (m n : ℕ)
    (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    GlueDiag (sgGlue m) (sgK m θ ax o ^ n) := by
  intro w w' hw hw' hc hσc hne
  have hc' : w.1 = w'.1 := hc
  have hσc' : (sgσ m w).1 = (sgσ m w').1 := hσc
  by_cases hp : w.2.1.1 = w'.2.1.1
  · have hpt : w.2.1 = w'.2.1 := Subtype.ext hp
    have hs : w.2.2 ≠ w'.2.2 :=
      fun h => hne (Prod.ext hc' (Prod.ext hpt h))
    have e : (sgK m θ ax o ^ n) w w' =
        (Hc m θ ax o w.1 ^ n) w.2 w'.2 := by
      rw [sgK, blockK_pow_local]
      change blockK (fun c' => Hc m θ ax o c' ^ n) w w' = _
      simp [blockK, hc']
    rw [e]
    have hzero := Hc_pow_samePoint_spinOffdiag_zero_any
      m θ ax o hanti w.1 n w.2.1 w.2.2 w'.2.2 hs
    have hsecond : (w.2.1, w'.2.2) = w'.2 := Prod.ext hpt rfl
    simpa only [hsecond] using hzero
  · exfalso
    have h1 := (glW_sgσ hw).1
    have h2 := (glW_sgσ hw').1
    rw [← hc'] at h2
    exact hp (gl_partner_inj h1 h2 hσc')

theorem Hc_sq_zero (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (hanti : OAnti (m + 1) o) (c : GCopy) (a b : Pt m × C2)
    (hab : a.1.1 = b.1.1) (hs : a.2 ≠ b.2) :
    (Hc m θ ax o c * Hc m θ ax o c) a b = 0 := by
  cases c
  · exact sq_zero_gen m θ ax o (oanti_A m o hanti) (Hc m θ ax o GCopy.A)
      (fun x y => rfl) a b hab hs
  · exact sq_zero_gen m θ ax (oBo m o) (oanti_B m o hanti) (Hc m θ ax o GCopy.B)
      (fun x y => rfl) a b hab hs
  · exact sq_zero_gen m θ ax (oCo m o) (oanti_C m o hanti) (Hc m θ ax o GCopy.C)
      (fun x y => rfl) a b hab hs

theorem sgK_hu2 (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (hanti : OAnti (m + 1) o) :
    GlueDiag (sgGlue m) (sgK m θ ax o * sgK m θ ax o) := by
  intro w w' hw hw' hc hσc hne
  have hc' : w.1 = w'.1 := hc
  have hσc' : (sgσ m w).1 = (sgσ m w').1 := hσc
  by_cases hp : w.2.1.1 = w'.2.1.1
  · have hs : w.2.2 ≠ w'.2.2 :=
      fun h => hne (Prod.ext hc' (Prod.ext (Subtype.ext hp) h))
    have e : (sgK m θ ax o * sgK m θ ax o) w w' =
        (Hc m θ ax o w.1 * Hc m θ ax o w.1) w.2 w'.2 :=
      blockK_mul_same (Hc m θ ax o) w w' hc'
    rw [e]
    exact Hc_sq_zero m θ ax o hanti w.1 w.2 w'.2 hp hs
  · exfalso
    have h1 := (glW_sgσ hw).1
    have h2 := (glW_sgσ hw').1
    rw [← hc'] at h2
    exact hp (gl_partner_inj h1 h2 hσc')

/-! ### Gluing identity without corner hypotheses -/

theorem pOpO_trace4_glue_final (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] (hanti : OAnti (m + 1) o)
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k) (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k) :
    Matrix.trace (pOpO (m + 1) θ ax o * pOpO (m + 1) θ ax o * pOpO (m + 1) θ ax o *
        pOpO (m + 1) θ ax o) = glueRHS m (sgK m θ ax o) :=
  pOpO_trace4_glue m θ ax o hax1 hax2 (sgK_hkg m hm θ ax o) (sgK_hu2 m θ ax o hanti)

/-!
### Higher-power support boundary

The arbitrary-power glued-corner condition is now proved separately above by
`sgK_pow_GlueDiag_of_OAnti`: under `OAnti (m + 1) o`, every natural power
`sgK ^ n` satisfies `GlueDiag (sgGlue m)`. Its same-coordinate case uses
Hermiticity and quaternionic spin-block cancellation; its distinct-coordinate
case follows from the glued-partner injectivity argument. Thus the corner
hypothesis needed by the conditional three-pairing reduction is available for
every exponent under the stated orientation hypothesis.

The coordinate-support lemmas below are a different tool: they bound where
entries of `sgK ^ n` can be nonzero, but do not replace the stronger
spin-resolved `GlueDiag` theorem. The full higher-moment boundary formula and
the all-level residual recurrence remain separate open obligations.
-/

/-! ### Generic coordinate support for powers (induction scaffold)

For a sparse operator whose nonzero entries change each coordinate by at most
one, every nonzero entry of its n-th power must lie within coordinate distance
n. This is the support estimate needed before applying the graph-specific
corner analysis to higher moments.
-/

theorem pow_entry_coord_dist
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : Matrix W W ℂ) (coord : W → ℕ × ℕ)
    (hK : ∀ i j, K i j ≠ 0 →
      (coord i).1 ≤ (coord j).1 + 1 ∧
      (coord j).1 ≤ (coord i).1 + 1 ∧
      (coord i).2 ≤ (coord j).2 + 1 ∧
      (coord j).2 ≤ (coord i).2 + 1) :
    ∀ n i j, (K ^ n) i j ≠ 0 →
      (coord i).1 ≤ (coord j).1 + n ∧
      (coord j).1 ≤ (coord i).1 + n ∧
      (coord i).2 ≤ (coord j).2 + n ∧
      (coord j).2 ≤ (coord i).2 + n := by
  classical
  intro n
  induction n with
  | zero =>
      intro i j h
      by_cases hij : i = j
      · subst j
        simp
      · simp [Matrix.one_apply, hij] at h
  | succ n ih =>
      intro i j h
      have hmul : (K ^ n * K) i j ≠ 0 := by
        simpa [pow_succ] using h
      have hex : ∃ k, (K ^ n) i k * K k j ≠ 0 := by
        by_contra hn
        push_neg at hn
        apply hmul
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro k hk
        exact hn k
      obtain ⟨k, hk⟩ := hex
      have hleft : (K ^ n) i k ≠ 0 := fun hz => hk (by simp [hz])
      have hright : K k j ≠ 0 := fun hz => hk (by simp [hz])
      obtain ⟨h1, h2, h3, h4⟩ := ih i k hleft
      obtain ⟨h5, h6, h7, h8⟩ := hK k j hright
      exact ⟨by omega, by omega, by omega, by omega⟩

/-- Specialization of the generic support estimate to the glued Sierpinski
operator. This bounds geometric coordinates of every nonzero power entry;
it does not by itself establish the stronger corner-vanishing hypotheses needed
for the higher-moment trace reduction. -/
theorem sgK_pow_entry_coord_dist (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    ∀ n w w', (sgK m θ ax o ^ n) w w' ≠ 0 →
      w.2.1.1.1 ≤ w'.2.1.1.1 + n ∧
      w'.2.1.1.1 ≤ w.2.1.1.1 + n ∧
      w.2.1.1.2 ≤ w'.2.1.1.2 + n ∧
      w'.2.1.1.2 ≤ w.2.1.1.2 + n := by
  apply pow_entry_coord_dist (K := sgK m θ ax o)
    (coord := fun w => (w.2.1.1.1, w.2.1.1.2))
  intro w w' h
  exact sgK_entry_coord_dist m θ ax o w w' h


/-- Converse support form: if one geometric coordinate separates two states
by more than the power length, the corresponding matrix entry must vanish.
This is a generic consequence of `pow_entry_coord_dist`, not a claim that
nearby corner entries vanish. -/
theorem pow_entry_zero_of_coord_gap
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : Matrix W W ℂ) (coord : W → ℕ × ℕ)
    (hK : ∀ i j, K i j ≠ 0 →
      (coord i).1 ≤ (coord j).1 + 1 ∧
      (coord j).1 ≤ (coord i).1 + 1 ∧
      (coord i).2 ≤ (coord j).2 + 1 ∧
      (coord j).2 ≤ (coord i).2 + 1)
    (n : ℕ) (i j : W)
    (hgap : (coord i).1 > (coord j).1 + n ∨
      (coord j).1 > (coord i).1 + n ∨
      (coord i).2 > (coord j).2 + n ∨
      (coord j).2 > (coord i).2 + n) :
    (K ^ n) i j = 0 := by
  by_contra hzero
  have hne : (K ^ n) i j ≠ 0 := fun h => hzero h
  obtain ⟨h1, h2, h3, h4⟩ :=
    pow_entry_coord_dist K coord hK n i j hne
  rcases hgap with hgap | hgap | hgap | hgap <;> omega


/-- Geometric support corollary for the glued Sierpinski operator:
entries of `sgK ^ n` vanish when either coordinate gap exceeds `n`.
This remains a distance-based support statement, not the stronger
same-coordinate/different-spin corner cancellation needed for all moments. -/
theorem sgK_pow_entry_zero_of_coord_gap
    (m n : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (w w')
    (hgap : w.2.1.1.1 > w'.2.1.1.1 + n ∨
      w'.2.1.1.1 > w.2.1.1.1 + n ∨
      w.2.1.1.2 > w'.2.1.1.2 + n ∨
      w'.2.1.1.2 > w.2.1.1.2 + n) :
    (sgK m θ ax o ^ n) w w' = 0 := by
  apply pow_entry_zero_of_coord_gap
    (K := sgK m θ ax o)
    (coord := fun z => (z.2.1.1.1, z.2.1.1.2))
    (hK := sgK_entry_coord_dist m θ ax o)
    (n := n) (i := w) (j := w') hgap


/-- Distinct geometric Sierpinski corners differ by exactly the side length
in one coordinate. -/
theorem corner_coord_gap {m : ℕ} {p q : Point}
    (hp : p = (0, 0) ∨ p = (2 ^ m, 0) ∨ p = (0, 2 ^ m))
    (hq : q = (0, 0) ∨ q = (2 ^ m, 0) ∨ q = (0, 2 ^ m))
    (hne : p ≠ q) :
    p.1 = q.1 + 2 ^ m ∨ q.1 = p.1 + 2 ^ m ∨
      p.2 = q.2 + 2 ^ m ∨ q.2 = p.2 + 2 ^ m := by
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;>
    subst p <;> subst q <;> simp_all <;> omega

/-- Between distinct glued geometric corners, every power shorter than the
side length has zero matrix entry. This is the geometric-corner case only;
it does not cover states with the same coordinate and different spin. -/
theorem sgK_pow_zero_of_distinct_glued_corner_coords
    (m n : ℕ) (hn : n < 2 ^ m)
    (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    (w w' : WSG m)
    (hw : (sgGlue m).g w) (hw' : (sgGlue m).g w')
    (hcoord : w.2.1.1 ≠ w'.2.1.1) :
    (sgK m θ ax o ^ n) w w' = 0 := by
  have hgap := corner_coord_gap (glued_corner hw) (glued_corner hw') hcoord
  rcases hgap with hgap | hgap | hgap | hgap
  · apply sgK_pow_entry_zero_of_coord_gap
    exact Or.inl (by omega)
  · apply sgK_pow_entry_zero_of_coord_gap
    exact Or.inr (Or.inl (by omega))
  · apply sgK_pow_entry_zero_of_coord_gap
    exact Or.inr (Or.inr (Or.inl (by omega)))
  · apply sgK_pow_entry_zero_of_coord_gap
    exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Reusable same-copy off-diagonal vanishing for powers of the concrete
glued operator. The proof splits the partner-coordinate case, handled by
GlueDiag, from distinct geometric corners, handled by the path-length bound. -/
theorem sgK_pow_hkg_of_OAnti
    (m n : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) (hn : n < 2 ^ m) :
    ∀ w w', (sgGlue m).g w → (sgGlue m).g w' →
      w.1 = w'.1 → w ≠ w' → (sgK m θ ax o ^ n) w w' = 0 := by
  intro w w' hw hw' hcopy hne
  have hdiag := sgK_pow_GlueDiag_of_OAnti m n θ ax o hanti
  by_cases hpartner : (sgσ m w).1 = (sgσ m w').1
  · exact hdiag w w' hw hw' hcopy hpartner hne
  · have h1 := (glW_sgσ hw).1
    have h2 := (glW_sgσ hw').1
    have hcoord : w.2.1.1 ≠ w'.2.1.1 := by
      intro hsame
      have h1' : gl m w.1 w.2.1.1 (sgσ m w).1 (sgσ m w).2.1.1 := h1
      have h2' : gl m w.1 w.2.1.1 (sgσ m w').1 (sgσ m w').2.1.1 := by
        simpa [hcopy, hsame] using h2
      have huniq := gl_unique m h1' h2'
      exact hpartner huniq.1
    exact sgK_pow_zero_of_distinct_glued_corner_coords
      m n hn θ ax o w w' hw hw' hcoord

/-- Under orientation antisymmetry, the glued corner lemma supplies the
middle-power hypothesis required to annihilate every ordered three-pairing
trace word whose middle exponent is below the geometric bound. -/
theorem trace_three_N_powers_of_OAnti
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d : ℕ) (hb : b < 2 ^ m) :
    Matrix.trace (sgK m θ ax o ^ a * (sgGlue m).N *
      sgK m θ ax o ^ b * (sgGlue m).N *
      sgK m θ ax o ^ c * (sgGlue m).N * sgK m θ ax o ^ d) = 0 := by
  apply trace_three_N_powers (sgGlue m) (sgK m θ ax o)
    (blockK_BD _) a b c d
  intro w w' hw hw' hcopy hne
  have hdiag := sgK_pow_GlueDiag_of_OAnti m b θ ax o hanti
  by_cases hpartner : (sgσ m w).1 = (sgσ m w').1
  · exact hdiag w w' hw hw' hcopy hpartner hne
  ·
    have h1 := (glW_sgσ hw).1
    have h2 := (glW_sgσ hw').1
    have hcoord : w.2.1.1 ≠ w'.2.1.1 := by
      intro hsame
      have h1' : gl m w.1 w.2.1.1 (sgσ m w).1 (sgσ m w).2.1.1 := h1
      have h2' : gl m w.1 w.2.1.1 (sgσ m w').1 (sgσ m w').2.1.1 := by
        simpa [hcopy, hsame] using h2
      have huniq := gl_unique m h1' h2'
      exact hpartner huniq.1
    exact sgK_pow_zero_of_distinct_glued_corner_coords
      m b hb θ ax o w w' hw hw' hcoord


-- The concrete specialization expands nested finite sums and needs more elaboration time.
set_option maxHeartbeats 400000 in
/-- Concrete four-pairing boundary formula for the glued Sierpinski operator.
Both middle exponents are below the side length, so the all-power spin
cancellation and the distinct-corner support bound discharge the two required
corner hypotheses. -/
theorem trace_four_N_powers_explicit_of_OAnti
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d e : ℕ) (hb : b < 2 ^ m) (hd : d < 2 ^ m) :
    Matrix.trace (sgK m θ ax o ^ a * (sgGlue m).N *
      sgK m θ ax o ^ b * (sgGlue m).N *
      sgK m θ ax o ^ c * (sgGlue m).N *
      sgK m θ ax o ^ d * (sgGlue m).N * sgK m θ ax o ^ e) =
      ∑ x, if (sgGlue m).g x then
        (∑ y, if (sgGlue m).g y then
          ((sgK m θ ax o ^ e * sgK m θ ax o ^ a) x y *
            (sgK m θ ax o ^ b) ((sgGlue m).σ y) ((sgGlue m).σ y)) *
            (sgK m θ ax o ^ c) y x
          else 0) *
          (sgK m θ ax o ^ d) ((sgGlue m).σ x) ((sgGlue m).σ x)
        else 0 := by
  have hkg : ∀ n, n < 2 ^ m →
      ∀ w w', (sgGlue m).g w → (sgGlue m).g w' →
        w.1 = w'.1 → w ≠ w' → (sgK m θ ax o ^ n) w w' = 0 := by
    intro n hn
    exact sgK_pow_hkg_of_OAnti m n θ ax o hanti hn
  exact trace_four_N_powers_explicit (sgGlue m) (sgK m θ ax o)
    (blockK_BD _) a b c d e (hkg b hb) (hkg d hd)


/-- Three-pairing specialization: if the middle power is below the side
length, the three-N trace stratum vanishes. The corner condition is obtained
from the all-power spin cancellation and the distinct glued-corner support
bound, rather than assumed separately. -/
theorem trace_three_N_word_zero_of_OAnti
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d : ℕ) (hb : b < 2 ^ m) :
    Matrix.trace (sgK m θ ax o ^ a * (sgGlue m).N *
      sgK m θ ax o ^ b * (sgGlue m).N *
      sgK m θ ax o ^ c * (sgGlue m).N * sgK m θ ax o ^ d) = 0 := by
  have hkg := sgK_pow_hkg_of_OAnti m b θ ax o hanti hb
  have hbd : BD (fun w : WSG m => w.1) (sgK m θ ax o) := blockK_BD _
  have hxs : ∀ A, A ∈ ([sgK m θ ax o ^ a] : List (Matrix (WSG m) (WSG m) ℂ)) →
      BD (fun w : WSG m => w.1) A := by
    intro A hA
    simp only [List.mem_singleton] at hA
    simpa [hA] using (BD_pow (sgK m θ ax o) hbd a)
  have hys : ∀ A, A ∈ ([sgK m θ ax o ^ c] : List (Matrix (WSG m) (WSG m) ℂ)) →
      BD (fun w : WSG m => w.1) A := by
    intro A hA
    simp only [List.mem_singleton] at hA
    simpa [hA] using (BD_pow (sgK m θ ax o) hbd c)
  have hzs : ∀ A, A ∈ ([sgK m θ ax o ^ d] : List (Matrix (WSG m) (WSG m) ℂ)) →
      BD (fun w : WSG m => w.1) A := by
    intro A hA
    simp only [List.mem_singleton] at hA
    simpa [hA] using (BD_pow (sgK m θ ax o) hbd d)
  simpa using trace_three_N_word_zero (sgGlue m)
    ([sgK m θ ax o ^ a] : List (Matrix (WSG m) (WSG m) ℂ))
    ([sgK m θ ax o ^ c] : List (Matrix (WSG m) (WSG m) ℂ))
    ([sgK m θ ax o ^ d] : List (Matrix (WSG m) (WSG m) ℂ))
    (sgK m θ ax o ^ b) hxs hys hzs (BD_pow (sgK m θ ax o) hbd b) hkg


/-- Five-pairing specialization under orientation antisymmetry. The two
middle-power corner conditions are discharged separately using the geometric
bound; this is a conditional vanishing theorem, not an unconditional
all-pairing cancellation claim. -/
theorem trace_five_N_powers_zero_of_OAnti
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d e f : ℕ) (hb : b < 2 ^ m) (hd : d < 2 ^ m) :
    Matrix.trace (sgK m θ ax o ^ a * (sgGlue m).N *
      sgK m θ ax o ^ b * (sgGlue m).N *
      sgK m θ ax o ^ c * (sgGlue m).N *
      sgK m θ ax o ^ d * (sgGlue m).N *
      sgK m θ ax o ^ e * (sgGlue m).N * sgK m θ ax o ^ f) = 0 := by
  have hkg : ∀ n, n < 2 ^ m →
      ∀ w w', (sgGlue m).g w → (sgGlue m).g w' → w.1 = w'.1 → w ≠ w' →
        (sgK m θ ax o ^ n) w w' = 0 := by
    intro n hn w w' hw hw' hcopy hne
    have hdiag := sgK_pow_GlueDiag_of_OAnti m n θ ax o hanti
    by_cases hpartner : (sgσ m w).1 = (sgσ m w').1
    · exact hdiag w w' hw hw' hcopy hpartner hne
    · have h1 := (glW_sgσ hw).1
      have h2 := (glW_sgσ hw').1
      have hcoord : w.2.1.1 ≠ w'.2.1.1 := by
        intro hsame
        have h1' : gl m w.1 w.2.1.1 (sgσ m w).1 (sgσ m w).2.1.1 := h1
        have h2' : gl m w.1 w.2.1.1 (sgσ m w').1 (sgσ m w').2.1.1 := by
          simpa [hcopy, hsame] using h2
        have huniq := gl_unique m h1' h2'
        exact hpartner huniq.1
      exact sgK_pow_zero_of_distinct_glued_corner_coords
        m n hn θ ax o w w' hw hw' hcoord
  exact trace_five_N_powers_zero (sgGlue m) (sgK m θ ax o)
    (blockK_BD _) a b c d e f (hkg b hb) (hkg d hd)


end EvgenyTheorem


namespace EvgenyTheorem


/-- Concrete seven-pairing vanishing theorem. The three selected middle
powers are below the side length, so their corner-off-diagonal hypotheses
follow from orientation antisymmetry and the geometric support bound. -/
theorem trace_seven_N_powers_zero_of_OAnti
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d e f g h : ℕ)
    (hb : b < 2 ^ m) (hd : d < 2 ^ m) (hf : f < 2 ^ m) :
    Matrix.trace (sgK m θ ax o ^ a * (sgGlue m).N *
      sgK m θ ax o ^ b * (sgGlue m).N *
      sgK m θ ax o ^ c * (sgGlue m).N *
      sgK m θ ax o ^ d * (sgGlue m).N *
      sgK m θ ax o ^ e * (sgGlue m).N *
      sgK m θ ax o ^ f * (sgGlue m).N *
      sgK m θ ax o ^ g * (sgGlue m).N * sgK m θ ax o ^ h) = 0 := by
  have hkg : ∀ n, n < 2 ^ m →
      ∀ w w', (sgGlue m).g w → (sgGlue m).g w' →
        w.1 = w'.1 → w ≠ w' → (sgK m θ ax o ^ n) w w' = 0 := by
    intro n hn
    exact sgK_pow_hkg_of_OAnti m n θ ax o hanti hn
  exact trace_seven_N_powers_zero (sgGlue m) (sgK m θ ax o)
    (blockK_BD _) a b c d e f g h (hkg b hb) (hkg d hd) (hkg f hf)


/-- Concrete nine-pairing vanishing theorem. The four selected middle
powers are below the side length, so their corner-off-diagonal hypotheses
follow from orientation antisymmetry and the geometric support bound. -/
theorem trace_nine_N_powers_zero_of_OAnti
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d e f g h i j : ℕ)
    (hb : b < 2 ^ m) (hd : d < 2 ^ m)
    (hf : f < 2 ^ m) (hh : h < 2 ^ m) :
    Matrix.trace (sgK m θ ax o ^ a * (sgGlue m).N *
      sgK m θ ax o ^ b * (sgGlue m).N *
      sgK m θ ax o ^ c * (sgGlue m).N *
      sgK m θ ax o ^ d * (sgGlue m).N *
      sgK m θ ax o ^ e * (sgGlue m).N *
      sgK m θ ax o ^ f * (sgGlue m).N *
      sgK m θ ax o ^ g * (sgGlue m).N *
      sgK m θ ax o ^ h * (sgGlue m).N *
      sgK m θ ax o ^ i * (sgGlue m).N * sgK m θ ax o ^ j) = 0 := by
  have hkg : ∀ n, n < 2 ^ m →
      ∀ w w', (sgGlue m).g w → (sgGlue m).g w' →
        w.1 = w'.1 → w ≠ w' → (sgK m θ ax o ^ n) w w' = 0 := by
    intro n hn
    exact sgK_pow_hkg_of_OAnti m n θ ax o hanti hn
  exact trace_nine_N_powers_zero (sgGlue m) (sgK m θ ax o)
    (blockK_BD _) a b c d e f g h i j
    (hkg b hb) (hkg d hd) (hkg f hf) (hkg h hh)


/-- Six-pairing boundary reduction for the concrete glued operator.
The three corner hypotheses are discharged from orientation antisymmetry
and the geometric distance bound, provided b, d, f are below the side length.
This is a boundary identity, not a vanishing theorem. -/
theorem trace_six_N_powers_boundary_of_OAnti
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d e f g : ℕ)
    (hb : b < 2 ^ m) (hd : d < 2 ^ m) (hf : f < 2 ^ m) :
    Matrix.trace (sgK m θ ax o ^ a * (sgGlue m).N *
      sgK m θ ax o ^ b * (sgGlue m).N *
      sgK m θ ax o ^ c * (sgGlue m).N *
      sgK m θ ax o ^ d * (sgGlue m).N *
      sgK m θ ax o ^ e * (sgGlue m).N *
      sgK m θ ax o ^ f * (sgGlue m).N * sgK m θ ax o ^ g) =
    Matrix.trace (sgK m θ ax o ^ g * sgK m θ ax o ^ a *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (sgK m θ ax o ^ b) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      sgK m θ ax o ^ c *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (sgK m θ ax o ^ d) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0) *
      sgK m θ ax o ^ e *
      Matrix.diagonal (fun y => if (sgGlue m).g y then
        (sgK m θ ax o ^ f) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0)) := by
  have hkg : ∀ n, n < 2 ^ m →
      ∀ w w', (sgGlue m).g w → (sgGlue m).g w' →
        w.1 = w'.1 → w ≠ w' → (sgK m θ ax o ^ n) w w' = 0 := by
    intro n hn
    exact sgK_pow_hkg_of_OAnti m n θ ax o hanti hn
  exact trace_six_N_powers_boundary (sgGlue m) (sgK m θ ax o)
    (blockK_BD _) a b c d e f g (hkg b hb) (hkg d hd) (hkg f hf)


/-- Eight-pairing boundary reduction for the concrete glued operator.
All four corner hypotheses are derived from OAnti and the geometric distance
bound. The conclusion is the explicit endpoint sum from
`trace_eight_N_powers_boundary`; it is not a cancellation theorem. -/
theorem trace_eight_N_powers_boundary_of_OAnti
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d e f g h i : ℕ)
    (hb : b < 2 ^ m) (hd : d < 2 ^ m)
    (hf : f < 2 ^ m) (hh : h < 2 ^ m) :
    Matrix.trace (sgK m θ ax o ^ a * (sgGlue m).N *
      sgK m θ ax o ^ b * (sgGlue m).N *
      sgK m θ ax o ^ c * (sgGlue m).N *
      sgK m θ ax o ^ d * (sgGlue m).N *
      sgK m θ ax o ^ e * (sgGlue m).N *
      sgK m θ ax o ^ f * (sgGlue m).N *
      sgK m θ ax o ^ g * (sgGlue m).N *
      sgK m θ ax o ^ h * (sgGlue m).N * sgK m θ ax o ^ i) =
      ∑ x, if (sgGlue m).g x then
        (([sgK m θ ax o ^ i, sgK m θ ax o ^ a,
          Matrix.diagonal (fun y => if (sgGlue m).g y then
            (sgK m θ ax o ^ b) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
          sgK m θ ax o ^ c,
          Matrix.diagonal (fun y => if (sgGlue m).g y then
            (sgK m θ ax o ^ d) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
          sgK m θ ax o ^ e,
          Matrix.diagonal (fun y => if (sgGlue m).g y then
            (sgK m θ ax o ^ f) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
          sgK m θ ax o ^ g] : List (Matrix (WSG m) (WSG m) ℂ)).prod) x x *
          (sgK m θ ax o ^ h) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
  have hkg : ∀ n, n < 2 ^ m →
      ∀ w w', (sgGlue m).g w → (sgGlue m).g w' →
        w.1 = w'.1 → w ≠ w' → (sgK m θ ax o ^ n) w w' = 0 := by
    intro n hn
    exact sgK_pow_hkg_of_OAnti m n θ ax o hanti hn
  exact trace_eight_N_powers_boundary (sgGlue m) (sgK m θ ax o)
    (blockK_BD _) a b c d e f g h i
    (hkg b hb) (hkg d hd) (hkg f hf) (hkg h hh)


/-- Ten-pairing boundary reduction for the concrete glued operator.
The five corner hypotheses are discharged from OAnti and the geometric
distance bound. The conclusion is the endpoint-sum formula from
`trace_ten_N_powers_boundary`; no cancellation is asserted. -/
theorem trace_ten_N_powers_boundary_of_OAnti
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o)
    (a b c d e f g h i j k : ℕ)
    (hb : b < 2 ^ m) (hd : d < 2 ^ m)
    (hf : f < 2 ^ m) (hh : h < 2 ^ m) (hj : j < 2 ^ m) :
    Matrix.trace (sgK m θ ax o ^ a * (sgGlue m).N *
      sgK m θ ax o ^ b * (sgGlue m).N *
      sgK m θ ax o ^ c * (sgGlue m).N *
      sgK m θ ax o ^ d * (sgGlue m).N *
      sgK m θ ax o ^ e * (sgGlue m).N *
      sgK m θ ax o ^ f * (sgGlue m).N *
      sgK m θ ax o ^ g * (sgGlue m).N *
      sgK m θ ax o ^ h * (sgGlue m).N *
      sgK m θ ax o ^ i * (sgGlue m).N *
      sgK m θ ax o ^ j * (sgGlue m).N * sgK m θ ax o ^ k) =
      ∑ x, if (sgGlue m).g x then
        (([sgK m θ ax o ^ k, sgK m θ ax o ^ a,
          Matrix.diagonal (fun y => if (sgGlue m).g y then
            (sgK m θ ax o ^ b) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
          sgK m θ ax o ^ c,
          Matrix.diagonal (fun y => if (sgGlue m).g y then
            (sgK m θ ax o ^ d) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
          sgK m θ ax o ^ e,
          Matrix.diagonal (fun y => if (sgGlue m).g y then
            (sgK m θ ax o ^ f) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
          sgK m θ ax o ^ g,
          Matrix.diagonal (fun y => if (sgGlue m).g y then
            (sgK m θ ax o ^ h) ((sgGlue m).σ y) ((sgGlue m).σ y) else 0),
          sgK m θ ax o ^ i] : List (Matrix (WSG m) (WSG m) ℂ)).prod) x x *
          (sgK m θ ax o ^ j) ((sgGlue m).σ x) ((sgGlue m).σ x) else 0 := by
  have hkg : ∀ n, n < 2 ^ m →
      ∀ w w', (sgGlue m).g w → (sgGlue m).g w' →
        w.1 = w'.1 → w ≠ w' → (sgK m θ ax o ^ n) w w' = 0 := by
    intro n hn
    exact sgK_pow_hkg_of_OAnti m n θ ax o hanti hn
  exact trace_ten_N_powers_boundary (sgGlue m) (sgK m θ ax o)
    (blockK_BD _) a b c d e f g h i j k
    (hkg b hb) (hkg d hd) (hkg f hf) (hkg h hh) (hkg j hj)

end EvgenyTheorem
