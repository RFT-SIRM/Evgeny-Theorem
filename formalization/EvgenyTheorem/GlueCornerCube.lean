import EvgenyTheorem.GlueCornerGeom
import EvgenyTheorem.GlueTrace

namespace EvgenyTheorem

open Matrix

/-- A matrix on `V × C2` built from 2×2 blocks. -/
def MatB {V : Type*} (B : V → V → Matrix C2 C2 ℂ) : Matrix (V × C2) (V × C2) ℂ :=
  fun a b => B a.1 b.1 a.2 b.2

theorem MatB_mul {V : Type*} [Fintype V] (B G : V → V → Matrix C2 C2 ℂ) :
    MatB B * MatB G = MatB (fun y z => ∑ w, B y w * G w z) := by
  ext ⟨y, i⟩ ⟨z, j⟩
  simp [Matrix.mul_apply, MatB, Fintype.sum_prod_type, Matrix.sum_apply]

theorem MatB_cube_diag {V : Type*} [Fintype V] (B : V → V → Matrix C2 C2 ℂ) (x : V) (i : C2) :
    (MatB B * MatB B * MatB B) (x, i) (x, i) =
      (∑ y, ∑ z, B x y * B y z * B z x) i i := by
  rw [MatB_mul, MatB_mul]
  have h : ∑ w, (∑ u, B x u * B u w) * B w x = ∑ y, ∑ z, B x y * B y z * B z x := by
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  show (∑ w, (∑ u, B x u * B u w) * B w x) i i = _
  rw [h]

theorem pOpO_eq_MatB (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (oo : Point → Point → Prop)
    [DecidableRel oo] :
    pOpO m θ ax oo = MatB (fun y z : Pt m => Bk m θ ax oo y.1 z.1) := by
  ext ⟨y, i⟩ ⟨z, j⟩
  rfl

theorem cube_diag_corner (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (oo : Point → Point → Prop)
    [DecidableRel oo] (hanti : OAnti m oo) {p q r : Point} (hc : CornerNbrs m p q r)
    (x : Pt m) (hx : x.1 = p) (i : C2) :
    (pOpO m θ ax oo * pOpO m θ ax oo * pOpO m θ ax oo) (x, i) (x, i) =
      ((pdeg m p : ℕ) : ℂ) ^ 3 + 4 * ((pdeg m p : ℕ) : ℂ) + ((pdeg m q : ℕ) : ℂ) +
        ((pdeg m r : ℕ) : ℂ) - 2 * cC θ := by
  subst hx
  obtain ⟨hq, hr, hpq, hpr, hqr, hEpq, hEpr, hEqr, hnb, hone⟩ := hc
  obtain ⟨qP, rfl⟩ : ∃ qP : Pt m, qP.1 = q := ⟨⟨q, List.mem_toFinset.mpr hq⟩, rfl⟩
  obtain ⟨rP, rfl⟩ : ∃ rP : Pt m, rP.1 = r := ⟨⟨r, List.mem_toFinset.mpr hr⟩, rfl⟩
  have hxv : x.1 ∈ vertexOrder m := List.mem_toFinset.mp x.2
  have hErp : EdgeB m rP.1.1 rP.1.2 x.1.1 x.1.2 = true := by
    rw [EdgeB_symm m]; exact hEpr
  have hy : ∀ y : Pt m, y ≠ x → y ≠ qP → y ≠ rP → Bk m θ ax oo x.1 y.1 = 0 := by
    intro y h1 h2 h3
    by_cases hE : EdgeB m x.1.1 x.1.2 y.1.1 y.1.2 = true
    · exfalso
      rcases hnb y.1 (List.mem_toFinset.mp y.2) hE with h | h
      · exact h2 (Subtype.ext h)
      · exact h3 (Subtype.ext h)
    · exact Bk_zero m θ ax oo (fun h => h1 (Subtype.ext h.symm)) hE
  have hz : ∀ z : Pt m, z ≠ x → z ≠ qP → z ≠ rP → Bk m θ ax oo z.1 x.1 = 0 := by
    intro z h1 h2 h3
    by_cases hE : EdgeB m z.1.1 z.1.2 x.1.1 x.1.2 = true
    · exfalso
      have hE' : EdgeB m x.1.1 x.1.2 z.1.1 z.1.2 = true := by
        rw [EdgeB_symm m]; exact hE
      rcases hnb z.1 (List.mem_toFinset.mp z.2) hE' with h | h
      · exact h2 (Subtype.ext h)
      · exact h3 (Subtype.ext h)
    · exact Bk_zero m θ ax oo (fun h => h1 (Subtype.ext h)) hE
  have an : ∀ {a b : Point}, a ∈ vertexOrder m → b ∈ vertexOrder m → a ≠ b →
      (oo a b ↔ ¬ oo b a) := fun ha hb hab => hanti _ _ ha hb hab
  have hqv : qP.1 ∈ vertexOrder m := hq
  have hrv : rP.1 ∈ vertexOrder m := hr
  have hs3 : Bk m θ ax oo x.1 rP.1 = (Bk m θ ax oo rP.1 x.1)ᴴ := by
    rw [Bk_swap m θ ax oo hpr (an hxv hrv hpr) hEpr, Matrix.conjTranspose_conjTranspose]
  have key : ∑ y : Pt m, ∑ z : Pt m,
      Bk m θ ax oo x.1 y.1 * Bk m θ ax oo y.1 z.1 * Bk m θ ax oo z.1 x.1 =
      (((pdeg m x.1 : ℕ) : ℂ) ^ 3 + 4 * ((pdeg m x.1 : ℕ) : ℂ) + ((pdeg m qP.1 : ℕ) : ℂ) +
        ((pdeg m rP.1 : ℕ) : ℂ)) • (1 : Matrix C2 C2 ℂ) +
      (Bk m θ ax oo x.1 qP.1 * Bk m θ ax oo qP.1 rP.1 * Bk m θ ax oo rP.1 x.1 +
        (Bk m θ ax oo x.1 qP.1 * Bk m θ ax oo qP.1 rP.1 * Bk m θ ax oo rP.1 x.1)ᴴ) :=
    cube_diag_abstract (fun y z : Pt m => Bk m θ ax oo y.1 z.1) x qP rP
      (fun h => hpq (congrArg Subtype.val h)) (fun h => hpr (congrArg Subtype.val h))
      (fun h => hqr (congrArg Subtype.val h)) hy hz _ _ _
      (Bk_diag m θ ax oo x.1) (Bk_diag m θ ax oo qP.1) (Bk_diag m θ ax oo rP.1)
      (Bk_mul m θ ax oo hpq (an hxv hqv hpq) hEpq)
      (Bk_mul m θ ax oo hpr (an hxv hrv hpr) hEpr)
      (Bk_swap m θ ax oo hpq (an hxv hqv hpq) hEpq)
      (Bk_swap m θ ax oo hqr (an hqv hrv hqr) hEqr) hs3
  have hT := tri_add_conj m θ ax oo hpq hqr hpr.symm hEpq hEqr hErp hone
  rw [pOpO_eq_MatB, MatB_cube_diag, key, hT]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  ring

/-- The cube of a copy block at a corner does not depend on the axis function. -/
theorem cube_axis_indep (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis) (oo : Point → Point → Prop)
    [DecidableRel oo] (hanti : OAnti m oo) (x : Pt m)
    (hx : x.1 = (0, 0) ∨ x.1 = (2 ^ m, 0) ∨ x.1 = (0, 2 ^ m)) (i : C2) :
    (pOpO m θ ax oo * pOpO m θ ax oo * pOpO m θ ax oo) (x, i) (x, i) =
      (pOpO m θ ax' oo * pOpO m θ ax' oo * pOpO m θ ax' oo) (x, i) (x, i) := by
  rcases hx with h | h | h
  · rw [cube_diag_corner m θ ax oo hanti (corner_O m) x h i,
      cube_diag_corner m θ ax' oo hanti (corner_O m) x h i]
  · rw [cube_diag_corner m θ ax oo hanti (corner_X m) x h i,
      cube_diag_corner m θ ax' oo hanti (corner_X m) x h i]
  · rw [cube_diag_corner m θ ax oo hanti (corner_Y m) x h i,
      cube_diag_corner m θ ax' oo hanti (corner_Y m) x h i]

theorem glued_point (m : ℕ) (c : GCopy) (p : Point) (h : ∃ c' p', gl m c p c' p') :
    p = (0, 0) ∨ p = (2 ^ m, 0) ∨ p = (0, 2 ^ m) := by
  obtain ⟨c', p', h⟩ := h
  rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;>
    first | exact Or.inl h | exact Or.inr (Or.inl h) | exact Or.inr (Or.inr h)

/-- The corner condition `hcorner` of `defectO_succ`, proved. -/
theorem sgK_corner_data (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (hanti : OAnti (m + 1) o) :
    ∀ a, (sgGlue m).g a →
      (sgK m θ ax o * sgK m θ ax o * sgK m θ ax o) a a =
          (sgK m θ ax' o * sgK m θ ax' o * sgK m θ ax' o) a a ∧
        (sgK m θ ax o * sgK m θ ax o) a a = (sgK m θ ax' o * sgK m θ ax' o) a a ∧
        sgK m θ ax o a a = sgK m θ ax' o a a := by
  intro a ha
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c, x, i⟩ := a
    obtain ⟨w', hgl, -⟩ := ha
    have hx := glued_point m c x.1 ⟨w'.1, w'.2.1.1, hgl⟩
    rw [sgK_cube_eq, sgK_cube_eq]
    cases c
    · exact cube_axis_indep m θ ax ax' o (oanti_A m o hanti) x hx i
    · exact cube_axis_indep m θ ax ax' (oBo m o) (oanti_B m o hanti) x hx i
    · exact cube_axis_indep m θ ax ax' (oCo m o) (oanti_C m o hanti) x hx i
  · rw [sgK_sq_diag m θ ax o hanti, sgK_sq_diag m θ ax' o hanti]
  · rw [sgK_diag, sgK_diag]


/-- The sum of cubic diagonal entries over glued states is independent of
 the axis assignment. The pointwise corner identity is supplied by
 sgK_corner_data; the result concerns the diagonal cube contribution only. -/
theorem sgK_glued_cube_diag_sum_axis_indep
    (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    (∑ a, if (sgGlue m).g a then
      (sgK m θ ax o * sgK m θ ax o * sgK m θ ax o) a a else 0) =
    (∑ a, if (sgGlue m).g a then
      (sgK m θ ax' o * sgK m θ ax' o * sgK m θ ax' o) a a else 0) := by
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hg : (sgGlue m).g a
  · simp only [hg, ↓reduceIte]
    exact (sgK_corner_data m θ ax ax' o hanti a hg).1
  · simp [hg]


/-- The full fourth-moment corner correction is independent of the axis
assignment, by the pointwise corner identities for powers one through three. -/
theorem cornerTerm_sgK_axis_indep
    (m : ℕ) (θ : ℝ) (ax ax' : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (hanti : OAnti (m + 1) o) :
    cornerTerm m (sgK m θ ax o) = cornerTerm m (sgK m θ ax' o) := by
  apply cornerTerm_congr
  exact sgK_corner_data m θ ax ax' o hanti

end EvgenyTheorem
