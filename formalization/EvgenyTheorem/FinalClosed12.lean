import EvgenyTheorem.FinalOrient12
import EvgenyTheorem.GlueRows12

namespace EvgenyTheorem

/-- Adjacent-level invariance of the complete positive-even H12 boundary
contribution in the flipped-corner orientation for the recursive face axis. -/
theorem glueRHS12_sgK_til_succ_faceAxis
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) :
    glueRHS12 (m + 1) (sgK (m + 1) θ faceAxis (oTil (m + 2))) =
      glueRHS12 m (sgK m θ faceAxis (oTil (m + 1))) := by
  simpa [glueRHS12] using
    sg_trace_p12_all_positive_even_N_word_strata_adjacent
      m hm θ faceAxis
      (faceAxis_pow1 m (by omega))
      (faceAxis_pow2 m (by omega))

theorem glueRHS12_sgK_til_succ_constAxis
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) :
    glueRHS12 (m + 1) (sgK (m + 1) θ (fun _ => 2) (oTil (m + 2))) =
      glueRHS12 m (sgK m θ (fun _ => 2) (oTil (m + 1))) := by
  simpa [glueRHS12] using
    sg_trace_p12_all_positive_even_N_word_strata_adjacent
      m hm θ (fun _ => 2)
      (by intro k; rfl)
      (by intro k; rfl)

/-- The face-axis H12 boundary contribution is constant from level five onward. -/
theorem glueRHS12_sgK_til_eq_level5_faceAxis
    (θ : ℝ) :
    ∀ m, 4 ≤ m →
      glueRHS12 m (sgK m θ faceAxis (oTil (m + 1))) =
        glueRHS12 5 (sgK 5 θ faceAxis (oTil 6)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
      exact (glueRHS12_sgK_til_succ_faceAxis 4 le_rfl θ).symm
  | succ n hn ih =>
      rw [glueRHS12_sgK_til_succ_faceAxis n hn θ, ih]

/-- The constant-axis H12 boundary contribution is constant from level five onward. -/
theorem glueRHS12_sgK_til_eq_level5_constAxis
    (θ : ℝ) :
    ∀ m, 4 ≤ m →
      glueRHS12 m (sgK m θ (fun _ => 2) (oTil (m + 1))) =
        glueRHS12 5 (sgK 5 θ (fun _ => 2) (oTil 6)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
      exact (glueRHS12_sgK_til_succ_constAxis 4 le_rfl θ).symm
  | succ n hn ih =>
      rw [glueRHS12_sgK_til_succ_constAxis n hn θ, ih]

/-- The orientation difference of the H12 defects is constant for all levels
at least five, since the boundary expression is orientation-independent. -/
theorem defectO12_orientation_difference_succ_invariant
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) :
    (defectO12 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) -
      defectO12 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1))) =
    (defectO12 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO12 m θ faceAxis (fun _ => 2) (oTil m)) := by
  rw [defectO12_orientation_difference_succ m hm θ,
    glueRHS12_num_eq_til m hm θ faceAxis,
    glueRHS12_num_eq_til m hm θ (fun _ => 2)]
  ring

theorem defectO12_orientation_difference_eq_level5
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) :
    (defectO12 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO12 m θ faceAxis (fun _ => 2) (oTil m)) =
    (defectO12 5 θ faceAxis (fun _ => 2) (oNum 5) -
      defectO12 5 θ faceAxis (fun _ => 2) (oTil 5)) := by
  induction m, hm using Nat.le_induction with
  | base => exact (defectO12_orientation_difference_succ_invariant 4 le_rfl θ).symm
  | succ n hn ih => rw [defectO12_orientation_difference_succ_invariant n hn θ, ih]

/-- The level-five constant in the affine H12 recurrence. -/
noncomputable def defectO12_num_residual_constant (θ : ℝ) : ℂ :=
  (glueRHS12 5 (sgK 5 θ faceAxis (oTil 6)) -
    glueRHS12 5 (sgK 5 θ (fun _ => 2) (oTil 6))) -
  (defectO12 5 θ faceAxis (fun _ => 2) (oNum 5) -
    defectO12 5 θ faceAxis (fun _ => 2) (oTil 5))

/-- Exact affine recurrence for the H12 numbering-orientation defect from
level five onward. Its constant is the level-five boundary residual minus
the level-five orientation difference. -/
theorem defectO12_succ_num_level5_constant_boundary
    (θ : ℝ) (m : ℕ) (hm : 4 ≤ m) :
    defectO12 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      3 * defectO12 m θ faceAxis (fun _ => 2) (oNum m) +
        defectO12_num_residual_constant θ := by
  rw [defectO12_succ_num m hm θ,
    glueRHS12_num_eq_til m hm θ faceAxis,
    glueRHS12_num_eq_til m hm θ (fun _ => 2),
    glueRHS12_sgK_til_eq_level5_faceAxis θ m hm,
    glueRHS12_sgK_til_eq_level5_constAxis θ m hm]
  have hgap := defectO12_orientation_difference_eq_level5 m hm θ
  unfold defectO12_num_residual_constant
  linear_combination -hgap

/-- Scalar affine recurrence solver over the complex numbers. -/
theorem affine_closed_form_aux (D : ℕ → ℂ) (c : ℂ)
    (h : ∀ n, D (n + 1) = 3 * D n + c) :
    ∀ n, D n = (3 : ℂ) ^ n * (D 0 + c / 2) - c / 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [h n, ih]; ring

/-- Closed affine form of the twelfth-moment defect from level five onward. -/
theorem defectO12_num_affine_closed_form_from_level5
    (θ : ℝ) :
    ∀ n : ℕ,
      defectO12 (n + 5) θ faceAxis (fun _ => 2) (oNum (n + 5)) =
        (3 : ℂ) ^ n *
          (defectO12 5 θ faceAxis (fun _ => 2) (oNum 5) +
            defectO12_num_residual_constant θ / 2) -
          defectO12_num_residual_constant θ / 2 := by
  let D : ℕ → ℂ :=
    fun k => defectO12 (k + 5) θ faceAxis (fun _ => 2) (oNum (k + 5))
  have hrec : ∀ n, D (n + 1) = 3 * D n + defectO12_num_residual_constant θ := by
    intro n
    exact defectO12_succ_num_level5_constant_boundary θ (n + 5) (by omega)
  intro n
  have hclosed := affine_closed_form_aux D (defectO12_num_residual_constant θ) hrec n
  simpa [D] using hclosed

/-- Unconditional affine recurrence for the H12 numbering-orientation defect. -/
theorem defectO12_succ_num_level5_constant_boundary_unconditional
    (θ : ℝ) (m : ℕ) (hm : 4 ≤ m) :
    defectO12 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      3 * defectO12 m θ faceAxis (fun _ => 2) (oNum m) +
        defectO12_num_residual_constant θ := by
  exact defectO12_succ_num_level5_constant_boundary θ m hm

/-- Unconditional closed affine formula for the H12 numbering-orientation defect
at every level `n + 5`. -/
theorem defectO12_num_affine_closed_form_from_level5_unconditional
    (θ : ℝ) :
    ∀ n : ℕ,
      defectO12 (n + 5) θ faceAxis (fun _ => 2) (oNum (n + 5)) =
        (3 : ℂ) ^ n *
          (defectO12 5 θ faceAxis (fun _ => 2) (oNum 5) +
            defectO12_num_residual_constant θ / 2) -
          defectO12_num_residual_constant θ / 2 := by
  exact defectO12_num_affine_closed_form_from_level5 θ


/-- Unconditional affine closed form for the H12 numbering-orientation defect
beginning at level four. The recurrence is proved for every m >= 4, so no
additional finite transition from level three is needed for this range. -/
theorem defectO12_num_affine_closed_form_from_level4_unconditional
    (θ : ℝ) :
    ∀ n : ℕ,
      defectO12 (n + 4) θ faceAxis (fun _ => 2) (oNum (n + 4)) =
        (3 : ℂ) ^ n *
          (defectO12 4 θ faceAxis (fun _ => 2) (oNum 4) +
            defectO12_num_residual_constant θ / 2) -
          defectO12_num_residual_constant θ / 2 := by
  let D : ℕ → ℂ :=
    fun k => defectO12 (k + 4) θ faceAxis (fun _ => 2) (oNum (k + 4))
  have hrec : ∀ n, D (n + 1) = 3 * D n + defectO12_num_residual_constant θ := by
    intro n
    simpa [D, Nat.add_assoc] using
      defectO12_succ_num_level5_constant_boundary θ (n + 4) (by omega)
  intro n
  have hclosed :=
    affine_closed_form_aux D (defectO12_num_residual_constant θ) hrec n
  simpa [D] using hclosed


/-- First adjacent-level transport of the flipped-orientation H12 boundary
term, including the finite step from level three to level four. -/
theorem glueRHS12_sgK_til_succ_faceAxis_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    glueRHS12 (m + 1) (sgK (m + 1) θ faceAxis (oTil (m + 2))) =
      glueRHS12 m (sgK m θ faceAxis (oTil (m + 1))) := by
  simpa [glueRHS12] using
    sg_trace_p12_all_positive_even_N_word_strata_adjacent_level3
      m hm θ faceAxis
      (faceAxis_pow1 m (by omega))
      (faceAxis_pow2 m (by omega))

theorem glueRHS12_sgK_til_succ_constAxis_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    glueRHS12 (m + 1) (sgK (m + 1) θ (fun _ => 2) (oTil (m + 2))) =
      glueRHS12 m (sgK m θ (fun _ => 2) (oTil (m + 1))) := by
  simpa [glueRHS12] using
    sg_trace_p12_all_positive_even_N_word_strata_adjacent_level3
      m hm θ (fun _ => 2)
      (by intro k; rfl)
      (by intro k; rfl)

/-- The flipped-orientation H12 boundary term is constant from level three
onward; the m=3 base is transported once to the already established level-5
stable value. -/
theorem glueRHS12_sgK_til_eq_level5_faceAxis_from_level3
    (θ : ℝ) (m : ℕ) (hm : 3 ≤ m) :
    glueRHS12 m (sgK m θ faceAxis (oTil (m + 1))) =
      glueRHS12 5 (sgK 5 θ faceAxis (oTil 6)) := by
  by_cases hm4 : 4 ≤ m
  · exact glueRHS12_sgK_til_eq_level5_faceAxis θ m hm4
  · have hmEq : m = 3 := by omega
    subst m
    calc
      glueRHS12 3 (sgK 3 θ faceAxis (oTil 4)) =
          glueRHS12 4 (sgK 4 θ faceAxis (oTil 5)) :=
        (glueRHS12_sgK_til_succ_faceAxis_level3 3 le_rfl θ).symm
      _ = glueRHS12 5 (sgK 5 θ faceAxis (oTil 6)) :=
        glueRHS12_sgK_til_eq_level5_faceAxis θ 4 (by omega)

theorem glueRHS12_sgK_til_eq_level5_constAxis_from_level3
    (θ : ℝ) (m : ℕ) (hm : 3 ≤ m) :
    glueRHS12 m (sgK m θ (fun _ => 2) (oTil (m + 1))) =
      glueRHS12 5 (sgK 5 θ (fun _ => 2) (oTil 6)) := by
  by_cases hm4 : 4 ≤ m
  · exact glueRHS12_sgK_til_eq_level5_constAxis θ m hm4
  · have hmEq : m = 3 := by omega
    subst m
    calc
      glueRHS12 3 (sgK 3 θ (fun _ => 2) (oTil 4)) =
          glueRHS12 4 (sgK 4 θ (fun _ => 2) (oTil 5)) :=
        (glueRHS12_sgK_til_succ_constAxis_level3 3 le_rfl θ).symm
      _ = glueRHS12 5 (sgK 5 θ (fun _ => 2) (oTil 6)) :=
        glueRHS12_sgK_til_eq_level5_constAxis θ 4 (by omega)

/-- The orientation gap is invariant already at the finite level-three
transition. The seven-step glued-row theorem and Hermitian diagonal
contraction are exactly what is needed for this base case. -/
theorem defectO12_orientation_difference_succ_invariant_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    (defectO12 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) -
      defectO12 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1))) =
    (defectO12 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO12 m θ faceAxis (fun _ => 2) (oTil m)) := by
  rw [defectO12_orientation_difference_succ_level3 m hm θ,
    glueRHS12_num_eq_til_from_level3 m hm θ faceAxis,
    glueRHS12_num_eq_til_from_level3 m hm θ (fun _ => 2)]
  ring

/-- Every H12 orientation gap from level three onward is the exact
level-five gap. -/
theorem defectO12_orientation_difference_eq_level5_from_level3
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    (defectO12 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO12 m θ faceAxis (fun _ => 2) (oTil m)) =
    (defectO12 5 θ faceAxis (fun _ => 2) (oNum 5) -
      defectO12 5 θ faceAxis (fun _ => 2) (oTil 5)) := by
  by_cases hm4 : 4 ≤ m
  · exact defectO12_orientation_difference_eq_level5 m hm4 θ
  · have hmEq : m = 3 := by omega
    subst m
    calc
      (defectO12 3 θ faceAxis (fun _ => 2) (oNum 3) -
        defectO12 3 θ faceAxis (fun _ => 2) (oTil 3)) =
        (defectO12 4 θ faceAxis (fun _ => 2) (oNum 4) -
          defectO12 4 θ faceAxis (fun _ => 2) (oTil 4)) := by
            symm
            exact defectO12_orientation_difference_succ_invariant_level3 3 le_rfl θ
      _ = (defectO12 5 θ faceAxis (fun _ => 2) (oNum 5) -
            defectO12 5 θ faceAxis (fun _ => 2) (oTil 5)) :=
          defectO12_orientation_difference_eq_level5 4 (by omega) θ

/-- The missing finite bridge m=3 to m=4 is now unconditional in Lean:
D_4^(12) = 3 D_3^(12) + C_12, with C_12 defined by the exact level-five
boundary residual. -/
theorem defectO12_succ_num_level3_constant_boundary
    (θ : ℝ) (m : ℕ) (hm : 3 ≤ m) :
    defectO12 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      3 * defectO12 m θ faceAxis (fun _ => 2) (oNum m) +
        defectO12_num_residual_constant θ := by
  rw [defectO12_succ_num_level3 m hm θ,
    glueRHS12_num_eq_til_from_level3 m hm θ faceAxis,
    glueRHS12_num_eq_til_from_level3 m hm θ (fun _ => 2),
    glueRHS12_sgK_til_eq_level5_faceAxis_from_level3 θ m hm,
    glueRHS12_sgK_til_eq_level5_constAxis_from_level3 θ m hm]
  have hgap := defectO12_orientation_difference_eq_level5_from_level3 m hm θ
  unfold defectO12_num_residual_constant
  linear_combination -hgap

/-- Explicit finite base transition at level three. -/
theorem defectO12_num_finite_base_bridge_level3
    (θ : ℝ) :
    defectO12 4 θ faceAxis (fun _ => 2) (oNum 4) =
      3 * defectO12 3 θ faceAxis (fun _ => 2) (oNum 3) +
        defectO12_num_residual_constant θ := by
  exact defectO12_succ_num_level3_constant_boundary θ 3 le_rfl

/-- Unconditional affine closed form for H12 from level three onward. This
includes the finite 3 -> 4 bridge and the stable recurrence for every later
level, rather than leaving level three as an external base certificate. -/
theorem defectO12_num_affine_closed_form_from_level3_unconditional
    (θ : ℝ) :
    ∀ n : ℕ,
      defectO12 (n + 3) θ faceAxis (fun _ => 2) (oNum (n + 3)) =
        (3 : ℂ) ^ n *
          (defectO12 3 θ faceAxis (fun _ => 2) (oNum 3) +
            defectO12_num_residual_constant θ / 2) -
          defectO12_num_residual_constant θ / 2 := by
  let D : ℕ → ℂ :=
    fun k => defectO12 (k + 3) θ faceAxis (fun _ => 2) (oNum (k + 3))
  have hrec : ∀ n, D (n + 1) = 3 * D n + defectO12_num_residual_constant θ := by
    intro n
    simpa [D, Nat.add_assoc] using
      defectO12_succ_num_level3_constant_boundary θ (n + 3) (by omega)
  intro n
  have hclosed :=
    affine_closed_form_aux D (defectO12_num_residual_constant θ) hrec n
  simpa [D] using hclosed

end EvgenyTheorem
