import EvgenyTheorem.GlueSG
import EvgenyTheorem.OpSplit3
import EvgenyTheorem.OrientSq

/-!
# The operator `H_{m+1}` as `E K Eᵀ`

`K` is block diagonal with the three copy operators (with the orientation transported from
level `m+1`), `E = Emat (sgπ m)`.  Combined with `sg_trace4_glue` this gives the gluing
identity for the *actual* operator.  Remaining hypotheses (`hkg`, `hu2`) are corner facts.
-/

namespace EvgenyTheorem

open Matrix

/-! ### Abstract part: block-diagonal matrices and pushforwards -/

section Abstract

/-- Block-diagonal matrix with blocks `H c`. -/
def blockK {ι X : Type*} [DecidableEq ι] (H : ι → Matrix X X ℂ) :
    Matrix (ι × X) (ι × X) ℂ :=
  fun w w' => if w.1 = w'.1 then H w.1 w.2 w'.2 else 0

theorem blockK_BD {ι X : Type*} [DecidableEq ι] (H : ι → Matrix X X ℂ) :
    BD (fun w : ι × X => w.1) (blockK H) := by
  intro w w' h
  have h' : w.1 ≠ w'.1 := h
  simp [blockK, h']

theorem EK_apply {ι X V : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
    [Fintype V] [DecidableEq V] (πc : ι → X → V) (H : ι → Matrix X X ℂ) (v : V) (c' : ι) (y : X) :
    (Emat (fun w : ι × X => πc w.1 w.2) * blockK H) v (c', y) =
      (Emat (πc c') * H c') v y := by
  simp only [Matrix.mul_apply, Emat, blockK, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single c']
  · simp
  · intro c _ hne
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ c') h

theorem EKEt_eq_sum {ι X V : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
    [Fintype V] [DecidableEq V] (πc : ι → X → V) (H : ι → Matrix X X ℂ) :
    Emat (fun w : ι × X => πc w.1 w.2) * blockK H * (Emat (fun w : ι × X => πc w.1 w.2))ᵀ =
      ∑ c, Emat (πc c) * H c * (Emat (πc c))ᵀ := by
  ext v v'
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [EK_apply]
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  first
    | rfl
    | simp [Matrix.transpose_apply, Emat]

theorem Ec_entry {X V : Type*} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    (π : X → V) (M : Matrix X X ℂ) (v v' : V) :
    (Emat π * M * (Emat π)ᵀ) v v' =
      ∑ x, ∑ y, (if π x = v then (1 : ℂ) else 0) * M x y * (if π y = v' then (1 : ℂ) else 0) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Emat, Finset.sum_mul]
  exact Finset.sum_comm

theorem sum_sum_ind {X V : Type*} [Fintype X] [DecidableEq V] (π : X → V)
    (hinj : Function.Injective π) (M : X → X → ℂ) (x0 y0 : X) (v v' : V)
    (hx : π x0 = v) (hy : π y0 = v') :
    ∑ x, ∑ y, (if π x = v then (1 : ℂ) else 0) * M x y * (if π y = v' then (1 : ℂ) else 0) =
      M x0 y0 := by
  rw [Finset.sum_eq_single x0]
  · rw [Finset.sum_eq_single y0]
    · simp [hx, hy]
    · intro y _ hne
      have : π y ≠ v' := fun h => hne (hinj (h.trans hy.symm))
      simp [this]
    · simp
  · intro x _ hne
    have : π x ≠ v := fun h => hne (hinj (h.trans hx.symm))
    simp [this]
  · simp

theorem sum_sum_ind_zero_left {X V : Type*} [Fintype X] [DecidableEq V] (π : X → V)
    (M : X → X → ℂ) (v v' : V) (h : ∀ x, π x ≠ v) :
    ∑ x, ∑ y, (if π x = v then (1 : ℂ) else 0) * M x y * (if π y = v' then (1 : ℂ) else 0) =
      0 := by
  simp [h]

theorem sum_sum_ind_zero_right {X V : Type*} [Fintype X] [DecidableEq V] (π : X → V)
    (M : X → X → ℂ) (v v' : V) (h : ∀ y, π y ≠ v') :
    ∑ x, ∑ y, (if π x = v then (1 : ℂ) else 0) * M x y * (if π y = v' then (1 : ℂ) else 0) =
      0 := by
  simp [h]

end Abstract

theorem sum_gcopy (f : GCopy → ℂ) : ∑ c, f c = f .A + f .B + f .C := by
  have h : (Finset.univ : Finset GCopy) = {GCopy.A, GCopy.B, GCopy.C} := by
    ext x
    cases x <;> simp
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]

/-! ### Concrete part -/

theorem GCopy.shift_inj (m : ℕ) (c : GCopy) {x y : Point}
    (h : c.shift m x = c.shift m y) : x = y := by
  cases c <;> exact shiftPoint_injective _ _ _ h

theorem sgπ_inj (m : ℕ) (c : GCopy) :
    Function.Injective (fun x : Pt m × C2 => sgπ m (c, x)) := by
  intro x y h
  have h1 : c.shift m x.1.1 = c.shift m y.1.1 := congrArg (fun z => z.1.1) h
  have h2 : x.2 = y.2 := by
    have h3 := congrArg Prod.snd h
    exact h3
  exact Prod.ext (Subtype.ext (GCopy.shift_inj m c h1)) h2

/-- The three copy operators. -/
noncomputable def Hc (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] : GCopy → Matrix (Pt m × C2) (Pt m × C2) ℂ
  | .A => fun x y => pHeO m θ ax o x.1.1 y.1.1 x.2 y.2
  | .B => fun x y => pHeO m θ ax (oBo m o) x.1.1 y.1.1 x.2 y.2
  | .C => fun x y => pHeO m θ ax (oCo m o) x.1.1 y.1.1 x.2 y.2

/-- Every local spin block of each copy operator has quaternionic form.
This is the concrete input needed to apply the abstract spin-block power lemma. -/
theorem Hc_spinBlock_quaternionForm (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] (c : GCopy) (p q : Pt m) :
    SU2QuaternionForm (spinBlock (Hc m θ ax o c) p q) := by
  cases c with
  | A =>
      change SU2QuaternionForm (pHeO_spinBlock m θ ax o p.1 q.1)
      exact pHeO_spinBlock_quaternionForm m θ ax o p.1 q.1
  | B =>
      change SU2QuaternionForm (pHeO_spinBlock m θ ax (oBo m o) p.1 q.1)
      exact pHeO_spinBlock_quaternionForm m θ ax (oBo m o) p.1 q.1
  | C =>
      change SU2QuaternionForm (pHeO_spinBlock m θ ax (oCo m o) p.1 q.1)
      exact pHeO_spinBlock_quaternionForm m θ ax (oCo m o) p.1 q.1

/-- Every spin block of every natural power of a copy operator has
quaternionic form. This specializes the generic power-closure lemma to the
three concrete operators used by the gluing construction. -/
theorem Hc_pow_spinBlock_quaternionForm (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] (c : GCopy) :
    ∀ n p q, SU2QuaternionForm (spinBlock ((Hc m θ ax o c) ^ n) p q) := by
  apply spinBlock_pow_quaternionForm
  intro p q
  exact Hc_spinBlock_quaternionForm m θ ax o c p q


/-! ### Concrete second-power cancellation under orientation antisymmetry -/

/-- The second power of each copy has zero same-point opposite-spin entry.
Unlike the all-powers statement below, this uses the already established
explicit diagonal formula for the square of the point operator. -/
theorem Hc_sq_samePoint_spinOffdiag_zero (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : ∀ c : GCopy, OAnti m
      (match c with
       | .A => o
       | .B => oBo m o
       | .C => oCo m o))
    (c : GCopy) (p : Pt m) :
    (Hc m θ ax o c ^ 2) (p, (0 : C2)) (p, (1 : C2)) = 0 := by
  have hdiag : (Hc m θ ax o c * Hc m θ ax o c)
      (p, (0 : C2)) (p, (1 : C2)) = 0 := by
    cases c with
    | A =>
        change (pOpO m θ ax o * pOpO m θ ax o)
          (p, (0 : C2)) (p, (1 : C2)) = 0
        have h := pOpO_sq_diag m θ ax o (hanti .A) p (0 : C2) (1 : C2)
        simpa using h
    | B =>
        change (pOpO m θ ax (oBo m o) * pOpO m θ ax (oBo m o))
          (p, (0 : C2)) (p, (1 : C2)) = 0
        have h := pOpO_sq_diag m θ ax (oBo m o) (hanti .B) p (0 : C2) (1 : C2)
        simpa using h
    | C =>
        change (pOpO m θ ax (oCo m o) * pOpO m θ ax (oCo m o))
          (p, (0 : C2)) (p, (1 : C2)) = 0
        have h := pOpO_sq_diag m θ ax (oCo m o) (hanti .C) p (0 : C2) (1 : C2)
        simpa using h
  rw [pow_two]
  exact hdiag

/-! ### Hermiticity of the copy operators -/

/-- An orientation-antisymmetric point operator is Hermitian. -/
theorem pOpO_hermitian_of_OAnti (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] (hanti : OAnti m o) :
    Matrix.conjTranspose (pOpO m θ ax o) = pOpO m θ ax o := by
  ext x y
  change star (pHeO m θ ax o y.1.1 x.1.1 y.2 x.2) =
    pHeO m θ ax o x.1.1 y.1.1 x.2 y.2
  by_cases hpq : x.1.1 = y.1.1
  · subst y
    simp [pHeO_diag]
  · have hp : x.1.1 ∈ vertexOrder m := x.1.2
    have hq : y.1.1 ∈ vertexOrder m := y.1.2
    by_cases hE : EdgeB m x.1.1.1 x.1.1.2 y.1.1.1 y.1.1.2 = true
    · have hE' : EdgeB m y.1.1.1 y.1.1.2 x.1.1.1 x.1.1.2 = true := by
        rw [EdgeB_symm m]
        exact hE
      rw [pHeO_edge_eq m θ ax o hpq hE, pHeO_edge_eq m θ ax o hpq.symm hE']
      have hor := hanti x.1.1 y.1.1 hp hq hpq
      have hswap := edgeU_swap m θ ax x.1.1 y.1.1
      rw [hswap]
      by_cases ho : o x.1.1 y.1.1
      · have hnot : ¬ o y.1.1 x.1.1 := (hor.mp ho)
        simp [ho, hnot, Matrix.conjTranspose_apply]
      · have hrev : o y.1.1 x.1.1 := by
          by_contra hn
          exact ho ((hor.mpr hn))
        simp [ho, hrev, Matrix.conjTranspose_apply]
    · have hE' : ¬ EdgeB m y.1.1.1 y.1.1.2 x.1.1.1 x.1.1.2 = true := by
        rw [EdgeB_symm m]
        exact hE
      rw [pHeO_zero_of_not_edge m θ ax o hpq hE,
        pHeO_zero_of_not_edge m θ ax o hpq.symm hE']
      simp

/-- All three copies are Hermitian when the original orientation is
antisymmetric; the B and C cases use the transported orientation lemmas. -/
theorem Hc_hermitian_of_OAnti (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] (hanti : OAnti (m + 1) o) :
    ∀ c : GCopy, Matrix.conjTranspose (Hc m θ ax o c) = Hc m θ ax o c := by
  intro c
  cases c with
  | A =>
      change Matrix.conjTranspose (pOpO m θ ax o) = pOpO m θ ax o
      exact pOpO_hermitian_of_OAnti m θ ax o (oanti_A m o hanti)
  | B =>
      change Matrix.conjTranspose (pOpO m θ ax (oBo m o)) = pOpO m θ ax (oBo m o)
      exact pOpO_hermitian_of_OAnti m θ ax (oBo m o) (oanti_B m o hanti)
  | C =>
      change Matrix.conjTranspose (pOpO m θ ax (oCo m o)) = pOpO m θ ax (oCo m o)
      exact pOpO_hermitian_of_OAnti m θ ax (oCo m o) (oanti_C m o hanti)

/-! ### Same-coordinate spin cancellation for powers of a copy -/

/-- If the three copy operators are Hermitian, then every natural power has
zero same-point, opposite-spin entry. The quaternion-form hypothesis is
provided concretely by `Hc_spinBlock_quaternionForm`; only Hermiticity remains
as an explicit operator-level premise. -/
theorem Hc_pow_samePoint_spinOffdiag_zero (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hH : ∀ c : GCopy, Matrix.conjTranspose (Hc m θ ax o c) = Hc m θ ax o c)
    (c : GCopy) (n : ℕ) (p : Pt m) :
    (Hc m θ ax o c ^ n) (p, (0 : C2)) (p, (1 : C2)) = 0 := by
  have hform : ∀ p q, SU2QuaternionForm (spinBlock (Hc m θ ax o c) p q) := by
    intro p q
    exact Hc_spinBlock_quaternionForm m θ ax o c p q
  have hpow : Matrix.conjTranspose ((Hc m θ ax o c) ^ n) =
      (Hc m θ ax o c) ^ n := by
    rw [Matrix.conjTranspose_pow, hH c]
  exact spinBlock_pow_diagonal_offdiag_zero (Hc m θ ax o c) hform n p hpow

/-- The block-diagonal operator on three disjoint copies. -/
noncomputable def sgK (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] : Matrix (WSG m) (WSG m) ℂ :=
  blockK (Hc m θ ax o)

/-- Powers of a block-diagonal matrix are computed independently in each block.
This local copy avoids a dependency cycle with the trace-splitting module. -/
theorem blockK_mul_local {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] (H G : ι → Matrix X X ℂ) :
    blockK H * blockK G = blockK (fun c => H c * G c) := by
  ext w w'
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hc : w.1 = w'.1
  · have e : blockK (fun c => H c * G c) w w' =
        (H w.1 * G w.1) w.2 w'.2 := by
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
  · have e : blockK (fun c => H c * G c) w w' = 0 := by
      simp [blockK, hc]
    rw [e]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    refine Finset.sum_eq_zero (fun y _ => ?_)
    by_cases h1 : w.1 = c
    · have : c ≠ w'.1 := fun h => hc (h1.trans h)
      simp [blockK, this]
    · simp [blockK, h1]

/-- Powers of a block-diagonal matrix are computed independently in each block.
This local copy avoids a dependency cycle with the trace-splitting module. -/
theorem blockK_pow_local {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [DecidableEq X] (H : ι → Matrix X X ℂ) (n : ℕ) :
    blockK H ^ n = blockK (fun c => H c ^ n) := by
  induction n with
  | zero =>
      ext ⟨i, x⟩ ⟨j, y⟩
      by_cases hij : i = j <;> by_cases hxy : x = y <;>
        simp [blockK, hij, hxy]
  | succ n ih =>
      rw [pow_succ, ih, blockK_mul_local]
      exact congrArg blockK (funext fun c => by rw [pow_succ])

/-! ### Transfer of copy-level cancellation to the glued index set -/

/-- Same-point opposite-spin entries also vanish in every power of the
three-copy block operator, provided each copy operator is Hermitian. -/
theorem sgK_pow_samePoint_spinOffdiag_zero (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hH : ∀ c : GCopy, Matrix.conjTranspose (Hc m θ ax o c) = Hc m θ ax o c)
    (c : GCopy) (n : ℕ) (p : Pt m) :
    (sgK m θ ax o ^ n) (c, (p, (0 : C2))) (c, (p, (1 : C2))) = 0 := by
  rw [sgK, blockK_pow_local]
  change (blockK (fun c' => Hc m θ ax o c' ^ n))
      (c, (p, (0 : C2))) (c, (p, (1 : C2))) = 0
  simp only [blockK, if_pos rfl]
  exact Hc_pow_samePoint_spinOffdiag_zero m θ ax o hH c n p

/-- Generic evaluation of one copy's contribution. -/
theorem copy_gen (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (oo : Point → Point → Prop) [DecidableRel oo]
    (c : GCopy) (P : Point → Prop) [DecidablePred P] (un : Point → Point)
    (hP : ∀ z, P z ↔ ∃ x ∈ vertexOrder m, c.shift m x = z)
    (hun : ∀ x ∈ vertexOrder m, un (c.shift m x) = x)
    (v v' : Pt (m + 1) × C2) :
    ∑ x : Pt m × C2, ∑ y : Pt m × C2,
        (if sgπ m (c, x) = v then (1 : ℂ) else 0) * pHeO m θ ax oo x.1.1 y.1.1 x.2 y.2 *
          (if sgπ m (c, y) = v' then (1 : ℂ) else 0) =
      if P v.1.1 ∧ P v'.1.1 then pHeO m θ ax oo (un v.1.1) (un v'.1.1) v.2 v'.2 else 0 := by
  have hpre : ∀ u : Pt (m + 1) × C2, (∃ x : Pt m × C2, sgπ m (c, x) = u) ↔ P u.1.1 := by
    intro u
    constructor
    · rintro ⟨x, rfl⟩
      exact (hP _).mpr ⟨x.1.1, List.mem_toFinset.mp x.1.2, rfl⟩
    · intro h
      obtain ⟨x, hx, hxs⟩ := (hP _).mp h
      exact ⟨(⟨x, List.mem_toFinset.mpr hx⟩, u.2), Prod.ext (Subtype.ext hxs) rfl⟩
  by_cases h1 : P v.1.1
  · by_cases h2 : P v'.1.1
    · obtain ⟨x0, hx0⟩ := (hpre v).mpr h1
      obtain ⟨y0, hy0⟩ := (hpre v').mpr h2
      refine (sum_sum_ind (fun x => sgπ m (c, x)) (sgπ_inj m c)
        (fun x y => pHeO m θ ax oo x.1.1 y.1.1 x.2 y.2) x0 y0 v v' hx0 hy0).trans ?_
      rw [if_pos (And.intro h1 h2)]
      subst hx0 hy0
      have hxm := List.mem_toFinset.mp x0.1.2
      have hym := List.mem_toFinset.mp y0.1.2
      have e1 : (sgπ m (c, x0)).1.1 = c.shift m x0.1.1 := rfl
      have e2 : (sgπ m (c, y0)).1.1 = c.shift m y0.1.1 := rfl
      have e3 : (sgπ m (c, x0)).2 = x0.2 := rfl
      have e4 : (sgπ m (c, y0)).2 = y0.2 := rfl
      rw [e1, e2, e3, e4, hun _ hxm, hun _ hym]
    · have hn : ∀ y : Pt m × C2, sgπ m (c, y) ≠ v' :=
        fun y hy => h2 ((hpre v').mp ⟨y, hy⟩)
      refine (sum_sum_ind_zero_right (fun x => sgπ m (c, x))
        (fun x y => pHeO m θ ax oo x.1.1 y.1.1 x.2 y.2) v v' hn).trans ?_
      rw [if_neg (fun h => h2 h.2)]
  · have hn : ∀ x : Pt m × C2, sgπ m (c, x) ≠ v :=
      fun x hx => h1 ((hpre v).mp ⟨x, hx⟩)
    refine (sum_sum_ind_zero_left (fun x => sgπ m (c, x))
      (fun x y => pHeO m θ ax oo x.1.1 y.1.1 x.2 y.2) v v' hn).trans ?_
    rw [if_neg (fun h => h1 h.1)]

theorem shiftA_eq (m : ℕ) (x : Point) : GCopy.shift m .A x = x := by
  simp [GCopy.shift, shiftPoint]

theorem hP_A (m : ℕ) (z : Point) :
    inA m z ↔ ∃ x ∈ vertexOrder m, GCopy.shift m .A x = z := by
  constructor
  · intro h
    exact ⟨z, List.mem_toFinset.mp h, shiftA_eq m z⟩
  · rintro ⟨x, hx, rfl⟩
    rw [shiftA_eq]
    exact List.mem_toFinset.mpr hx

theorem hP_B (m : ℕ) (z : Point) :
    inB m z ↔ ∃ x ∈ vertexOrder m, GCopy.shift m .B x = z := by
  constructor
  · intro h
    exact ⟨unB m z, inB_mem h, inB_shift h⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ (vertexOrder m).toFinset := List.mem_toFinset.mpr hx
    refine ⟨?_, ?_⟩
    · simp [GCopy.shift, shiftPoint]
    · simpa [GCopy.shift, shiftPoint] using hx'

theorem hP_C (m : ℕ) (z : Point) :
    inC m z ↔ ∃ x ∈ vertexOrder m, GCopy.shift m .C x = z := by
  constructor
  · intro h
    exact ⟨unC m z, inC_mem h, inC_shift h⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ (vertexOrder m).toFinset := List.mem_toFinset.mpr hx
    refine ⟨?_, ?_⟩
    · simp [GCopy.shift, shiftPoint]
    · simpa [GCopy.shift, shiftPoint] using hx'

theorem copy_A (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    (v v' : Pt (m + 1) × C2) :
    (Emat (fun x : Pt m × C2 => sgπ m (GCopy.A, x)) * Hc m θ ax o GCopy.A *
        (Emat (fun x : Pt m × C2 => sgπ m (GCopy.A, x)))ᵀ) v v' =
      KAo m θ ax o v.1.1 v'.1.1 v.2 v'.2 := by
  rw [Ec_entry]
  exact copy_gen m θ ax o GCopy.A (inA m) id (hP_A m)
    (fun x _ => shiftA_eq m x) v v'

theorem copy_B (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    (v v' : Pt (m + 1) × C2) :
    (Emat (fun x : Pt m × C2 => sgπ m (GCopy.B, x)) * Hc m θ ax o GCopy.B *
        (Emat (fun x : Pt m × C2 => sgπ m (GCopy.B, x)))ᵀ) v v' =
      KBo m θ ax o v.1.1 v'.1.1 v.2 v'.2 := by
  rw [Ec_entry]
  exact copy_gen m θ ax (oBo m o) GCopy.B (inB m) (unB m) (hP_B m)
    (fun x _ => by simp [unB, GCopy.shift, shiftPoint]) v v'

theorem copy_C (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    (v v' : Pt (m + 1) × C2) :
    (Emat (fun x : Pt m × C2 => sgπ m (GCopy.C, x)) * Hc m θ ax o GCopy.C *
        (Emat (fun x : Pt m × C2 => sgπ m (GCopy.C, x)))ᵀ) v v' =
      KCo m θ ax o v.1.1 v'.1.1 v.2 v'.2 := by
  rw [Ec_entry]
  exact copy_gen m θ ax (oCo m o) GCopy.C (inC m) (unC m) (hP_C m)
    (fun x _ => by simp [unC, GCopy.shift, shiftPoint]) v v'

/-- **`H_{m+1} = E K Eᵀ`**, for an arbitrary orientation `o`. -/
theorem sg_EKEt (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop) [DecidableRel o]
    (hax1 : ∀ k, ax (3 ^ m + k) = ax k) (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k) :
    Emat (sgπ m) * sgK m θ ax o * (Emat (sgπ m))ᵀ = pOpO (m + 1) θ ax o := by
  have h := EKEt_eq_sum (fun (c : GCopy) (x : Pt m × C2) => sgπ m (c, x)) (Hc m θ ax o)
  refine h.trans ?_
  ext v v'
  show _ = pHeO (m + 1) θ ax o v.1.1 v'.1.1 v.2 v'.2
  rw [Matrix.sum_apply, sum_gcopy, pHeO_succ m θ ax o hax1 hax2 v.1.1 v'.1.1 v.2 v'.2]
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (copy_A m θ ax o v v') (copy_B m θ ax o v v'))
    (copy_C m θ ax o v v')

/-- Right-hand side of the gluing identity. -/
noncomputable def glueRHS (m : ℕ) (K : Matrix (WSG m) (WSG m) ℂ) : ℂ :=
  Matrix.trace (K * K * K * K) +
    4 * ∑ a, (if (sgGlue m).g a then (K * K * K) a a * K ((sgGlue m).σ a) ((sgGlue m).σ a)
      else 0) +
    2 * ∑ a, (if (sgGlue m).g a then (K * K) a a * (K * K) ((sgGlue m).σ a) ((sgGlue m).σ a)
      else 0) +
    ∑ a, (if (sgGlue m).g a then K a a * K a a * (K ((sgGlue m).σ a) ((sgGlue m).σ a) *
      K ((sgGlue m).σ a) ((sgGlue m).σ a)) else 0)

/-- **Gluing identity for the actual operator.** Only the corner hypotheses
`hkg`, `hu2` remain to be discharged. -/
theorem pOpO_trace4_glue (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (hax1 : ∀ k, ax (3 ^ m + k) = ax k)
    (hax2 : ∀ k, ax (2 * 3 ^ m + k) = ax k)
    (hkg : ∀ w w', (sgGlue m).g w → (sgGlue m).g w' → w.1 = w'.1 → w ≠ w' →
      sgK m θ ax o w w' = 0)
    (hu2 : GlueDiag (sgGlue m) (sgK m θ ax o * sgK m θ ax o)) :
    Matrix.trace (pOpO (m + 1) θ ax o * pOpO (m + 1) θ ax o * pOpO (m + 1) θ ax o *
        pOpO (m + 1) θ ax o) = glueRHS m (sgK m θ ax o) := by
  rw [← sg_EKEt m θ ax o hax1 hax2]
  exact sg_trace4_glue m (sgK m θ ax o) (blockK_BD _) hkg hu2

end EvgenyTheorem
