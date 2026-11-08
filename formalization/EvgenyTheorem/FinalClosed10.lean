import EvgenyTheorem.GlueRows10
import EvgenyTheorem.FinalOrient10

namespace EvgenyTheorem

/-- The diagonal transport needed for the tenth-moment boundary recurrence
for the flipped-corner orientation. The all-level radius-four statement
for both configurations is proved below as `H10TransportAll_proved`. -/
def H10Transport (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) : Prop :=
  ∀ (w : WSG (m + 1)) (hw : (sgGlue (m + 1)).g w), ∀ n, n ≤ 9 →
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ n) w w =
      (sgK m θ ax (oTil (m + 1)) ^ n)
        (sgK_root_pullback m w) (sgK_root_pullback m w) ∧
    (sgK (m + 1) θ ax (oTil (m + 2)) ^ n)
        ((sgGlue (m + 1)).σ w) ((sgGlue (m + 1)).σ w) =
      (sgK m θ ax (oTil (m + 1)) ^ n)
        ((sgGlue m).σ (sgK_root_pullback m w))
        ((sgGlue m).σ (sgK_root_pullback m w))

def H10TransportAll (θ : ℝ) : Prop :=
  ∀ m : ℕ, 4 ≤ m → H10Transport m θ faceAxis ∧ H10Transport m θ (fun _ => 2)

/-- Radius-four diagonal transport for both H10 axes at every level `m ≥ 4`. -/
theorem H10TransportAll_proved (θ : ℝ) : H10TransportAll θ := by
  intro m hm
  constructor
  · intro w hw n hn
    exact sgK_glued_state_diag_one_to_nine_transport
      m (by omega) θ faceAxis
      (faceAxis_pow1 m (by omega))
      (faceAxis_pow2 m (by omega)) hw n hn
  · intro w hw n hn
    exact sgK_glued_state_diag_one_to_nine_transport
      m (by omega) θ (fun _ => 2)
      (by intro k; rfl)
      (by intro k; rfl) hw n hn

theorem glueRHS10_pair_product_congr
    (m : ℕ) (K K' : Matrix (WSG m) (WSG m) ℂ)
    (h : ∀ x, (sgGlue m).g x → ∀ n, n ≤ 9 →
      (K ^ n) x x = (K' ^ n) x x ∧
      (K ^ n) ((sgGlue m).σ x) ((sgGlue m).σ x) =
        (K' ^ n) ((sgGlue m).σ x) ((sgGlue m).σ x))
    (x : WSG m) (hg : (sgGlue m).g x) :
    ∀ ps : List (ℕ × ℕ), (∀ p ∈ ps, p.1 ≤ 9 ∧ p.2 ≤ 9) →
      glueRHS8_pair_product m K x ps = glueRHS8_pair_product m K' x ps := by
  intro ps
  induction ps with
  | nil => intro _; rfl
  | cons p ps ih =>
      intro hb
      simp only [glueRHS8_pair_product, glueRHS8_pair_value]
      have hp := hb p (by simp)
      have e1 := (h x hg p.1 hp.1).1
      have e2 := (h x hg p.2 hp.2).2
      rw [e1, e2, ih (fun q hq => hb q (by simp [hq]))]

theorem glueRHS10_pair_sum_congr
    (m : ℕ) (K K' : Matrix (WSG m) (WSG m) ℂ)
    (h : ∀ x, (sgGlue m).g x → ∀ n, n ≤ 9 →
      (K ^ n) x x = (K' ^ n) x x ∧
      (K ^ n) ((sgGlue m).σ x) ((sgGlue m).σ x) =
        (K' ^ n) ((sgGlue m).σ x) ((sgGlue m).σ x))
    (ps : List (ℕ × ℕ)) (hb : ∀ p ∈ ps, p.1 ≤ 9 ∧ p.2 ≤ 9) :
    glueRHS8_pair_sum m K ps = glueRHS8_pair_sum m K' ps := by
  classical
  unfold glueRHS8_pair_sum
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : (sgGlue m).g x
  · simp only [if_pos hg]
    exact glueRHS10_pair_product_congr m K K' h x hg ps hb
  · simp only [if_neg hg]

/-- The complete H10 boundary correction depends only on the diagonal powers
`(K^n)_{xx}`, `(K^n)_{σx σx}` (n ≤ 9) at glued states. -/
theorem glueRHS10_congr_of_diag
    (m : ℕ) (K K' : Matrix (WSG m) (WSG m) ℂ)
    (h : ∀ x, (sgGlue m).g x → ∀ n, n ≤ 9 →
      (K ^ n) x x = (K' ^ n) x x ∧
      (K ^ n) ((sgGlue m).σ x) ((sgGlue m).σ x) =
        (K' ^ n) ((sgGlue m).σ x) ((sgGlue m).σ x)) :
    glueRHS10 m K = glueRHS10 m K' := by
  unfold glueRHS10 glueRHS10_two_N_diagonal_form glueRHS10_four_N_diagonal_form
    glueRHS10_six_N_diagonal_form glueRHS10_eight_N_diagonal_form
    glueRHS10_three_pair_sum glueRHS10_four_pair_sum
  rw [glueRHS10_ten_eq_pair_sum, glueRHS10_ten_eq_pair_sum]
  have hsum (ps : List (ℕ × ℕ)) (hb : ∀ p ∈ ps, p.1 ≤ 9 ∧ p.2 ≤ 9) :=
    glueRHS10_pair_sum_congr m K K' h ps hb
  rw [
    hsum [(1,9)] (by norm_num),
    hsum [(2,8)] (by norm_num),
    hsum [(3,7)] (by norm_num),
    hsum [(4,6)] (by norm_num),
    hsum [(5,5)] (by norm_num),
    hsum [(1,1), (1,7)] (by norm_num),
    hsum [(1,1), (2,6)] (by norm_num),
    hsum [(1,1), (3,5)] (by norm_num),
    hsum [(1,1), (4,4)] (by norm_num),
    hsum [(1,1), (5,3)] (by norm_num),
    hsum [(1,1), (6,2)] (by norm_num),
    hsum [(1,2), (1,6)] (by norm_num),
    hsum [(1,2), (2,5)] (by norm_num),
    hsum [(1,2), (3,4)] (by norm_num),
    hsum [(1,2), (4,3)] (by norm_num),
    hsum [(1,2), (5,2)] (by norm_num),
    hsum [(1,3), (1,5)] (by norm_num),
    hsum [(1,3), (2,4)] (by norm_num),
    hsum [(1,3), (3,3)] (by norm_num),
    hsum [(1,3), (4,2)] (by norm_num),
    hsum [(1,4), (1,4)] (by norm_num),
    hsum [(1,4), (2,3)] (by norm_num),
    hsum [(1,4), (3,2)] (by norm_num),
    hsum [(1,5), (2,2)] (by norm_num),
    hsum [(2,2), (2,4)] (by norm_num),
    hsum [(2,2), (3,3)] (by norm_num),
    hsum [(2,3), (2,3)] (by norm_num),
    hsum [(1,1), (1,1), (1,5)] (by norm_num),
    hsum [(1,1), (1,1), (2,4)] (by norm_num),
    hsum [(1,1), (1,1), (3,3)] (by norm_num),
    hsum [(1,1), (1,1), (4,2)] (by norm_num),
    hsum [(1,1), (1,2), (1,4)] (by norm_num),
    hsum [(1,1), (1,2), (2,3)] (by norm_num),
    hsum [(1,1), (1,2), (3,2)] (by norm_num),
    hsum [(1,1), (1,3), (1,3)] (by norm_num),
    hsum [(1,1), (1,3), (2,2)] (by norm_num),
    hsum [(1,1), (1,4), (1,2)] (by norm_num),
    hsum [(1,1), (2,1), (1,4)] (by norm_num),
    hsum [(1,1), (2,1), (2,3)] (by norm_num),
    hsum [(1,1), (2,1), (3,2)] (by norm_num),
    hsum [(1,1), (2,2), (1,3)] (by norm_num),
    hsum [(1,1), (2,2), (2,2)] (by norm_num),
    hsum [(1,1), (2,3), (1,2)] (by norm_num),
    hsum [(1,1), (3,1), (1,3)] (by norm_num),
    hsum [(1,1), (3,1), (2,2)] (by norm_num),
    hsum [(1,1), (3,2), (1,2)] (by norm_num),
    hsum [(1,2), (1,2), (1,3)] (by norm_num),
    hsum [(1,2), (1,2), (2,2)] (by norm_num),
    hsum [(1,2), (2,1), (2,2)] (by norm_num),
    hsum [(1,1), (1,1), (1,1), (1,3)] (by norm_num),
    hsum [(1,1), (1,1), (1,1), (2,2)] (by norm_num),
    hsum [(1,1), (1,1), (1,2), (1,2)] (by norm_num),
    hsum [(1,1), (1,1), (2,1), (1,2)] (by norm_num),
    hsum [(1,1), (1,2), (1,1), (1,2)] (by norm_num),
    hsum [(1, 1), (1, 1), (1, 1), (1, 1), (1, 1)] (by norm_num)
  ]

theorem glueRHS10_num_eq_til (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) (ax : ℕ → Axis) :
    glueRHS10 m (sgK m θ ax (oNum (m + 1))) =
      glueRHS10 m (sgK m θ ax (oTil (m + 1))) := by
  apply glueRHS10_congr_of_diag
  intro x hx n hn
  have hxs := (sgGlue m).g_σ x hx
  exact ⟨sgK_pow_row_eq_num_til_on_glue_up_to_nine m hm θ ax x hx n hn x,
    sgK_pow_row_eq_num_til_on_glue_up_to_nine m hm θ ax ((sgGlue m).σ x) hxs n hn
      ((sgGlue m).σ x)⟩

theorem glueRHS10_sgK_til_succ_of_transport
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (hT : H10Transport m θ ax) :
    glueRHS10 (m + 1) (sgK (m + 1) θ ax (oTil (m + 2))) =
      glueRHS10 m (sgK m θ ax (oTil (m + 1))) :=
  glueRHS10_adjacent_level_eq_of_diagonal_transport m θ ax (oTil (m + 2)) (oTil (m + 1))
    (sgK_glued_root_equiv m) (fun w hw n hn => hT w hw n hn)

theorem glueRHS10_sgK_til_eq_level5 (θ : ℝ) (ax : ℕ → Axis)
    (hT : ∀ m, 4 ≤ m → H10Transport m θ ax) :
    ∀ m, 4 ≤ m →
      glueRHS10 m (sgK m θ ax (oTil (m + 1))) =
        glueRHS10 5 (sgK 5 θ ax (oTil 6)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact (glueRHS10_sgK_til_succ_of_transport 4 θ ax (hT 4 le_rfl)).symm
  | succ n hn ih => rw [glueRHS10_sgK_til_succ_of_transport n θ ax (hT n hn), ih]

theorem defectO10_orientation_difference_succ_invariant
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) :
    (defectO10 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) -
      defectO10 (m + 1) θ faceAxis (fun _ => 2) (oTil (m + 1))) =
    (defectO10 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO10 m θ faceAxis (fun _ => 2) (oTil m)) := by
  rw [defectO10_orientation_difference_succ m hm θ,
    glueRHS10_num_eq_til m hm θ faceAxis,
    glueRHS10_num_eq_til m hm θ (fun _ => 2)]
  ring

theorem defectO10_orientation_difference_eq_level5
    (m : ℕ) (hm : 4 ≤ m) (θ : ℝ) :
    (defectO10 m θ faceAxis (fun _ => 2) (oNum m) -
      defectO10 m θ faceAxis (fun _ => 2) (oTil m)) =
    (defectO10 5 θ faceAxis (fun _ => 2) (oNum 5) -
      defectO10 5 θ faceAxis (fun _ => 2) (oTil 5)) := by
  induction m, hm using Nat.le_induction with
  | base => exact (defectO10_orientation_difference_succ_invariant 4 le_rfl θ).symm
  | succ n hn ih => rw [defectO10_orientation_difference_succ_invariant n hn θ, ih]

noncomputable def defectO10_num_residual_constant (θ : ℝ) : ℂ :=
  (glueRHS10 5 (sgK 5 θ faceAxis (oTil 6)) -
    glueRHS10 5 (sgK 5 θ (fun _ => 2) (oTil 6))) -
  (defectO10 5 θ faceAxis (fun _ => 2) (oNum 5) -
    defectO10 5 θ faceAxis (fun _ => 2) (oTil 5))

theorem defectO10_succ_num_level5_constant_boundary
    (θ : ℝ) (hT : H10TransportAll θ) (m : ℕ) (hm : 4 ≤ m) :
    defectO10 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      3 * defectO10 m θ faceAxis (fun _ => 2) (oNum m) +
        defectO10_num_residual_constant θ := by
  rw [defectO10_succ_num m hm θ,
    glueRHS10_num_eq_til m hm θ faceAxis,
    glueRHS10_num_eq_til m hm θ (fun _ => 2),
    glueRHS10_sgK_til_eq_level5 θ faceAxis (fun k hk => (hT k hk).1) m hm,
    glueRHS10_sgK_til_eq_level5 θ (fun _ => 2) (fun k hk => (hT k hk).2) m hm]
  have hgap := defectO10_orientation_difference_eq_level5 m hm θ
  unfold defectO10_num_residual_constant
  linear_combination -hgap

theorem affine_closed_form_aux (D : ℕ → ℂ) (c : ℂ)
    (h : ∀ n, D (n + 1) = 3 * D n + c) :
    ∀ n, D n = (3 : ℂ) ^ n * (D 0 + c / 2) - c / 2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [h n, ih]; ring

/-- Conditional closed affine form of the tenth-moment defect for levels `n + 5`.
The hypothesis `H10TransportAll θ` (radius-4 corner diagonal transport) is explicit. -/
theorem defectO10_num_affine_closed_form_from_level5
    (θ : ℝ) (hT : H10TransportAll θ) :
    ∀ n : ℕ,
      defectO10 (n + 5) θ faceAxis (fun _ => 2) (oNum (n + 5)) =
        (3 : ℂ) ^ n *
          (defectO10 5 θ faceAxis (fun _ => 2) (oNum 5) +
            defectO10_num_residual_constant θ / 2) -
          defectO10_num_residual_constant θ / 2 := by
  let D : ℕ → ℂ := fun k => defectO10 (k + 5) θ faceAxis (fun _ => 2) (oNum (k + 5))
  have hrec : ∀ n, D (n + 1) = 3 * D n + defectO10_num_residual_constant θ := by
    intro n
    exact defectO10_succ_num_level5_constant_boundary θ hT (n + 5) (by omega)
  intro n
  have := affine_closed_form_aux D (defectO10_num_residual_constant θ) hrec n
  simpa [D] using this

/-- Unconditional H10 recurrence using the proved radius-four transport. -/
theorem defectO10_succ_num_level5_constant_boundary_unconditional
    (θ : ℝ) (m : ℕ) (hm : 4 ≤ m) :
    defectO10 (m + 1) θ faceAxis (fun _ => 2) (oNum (m + 1)) =
      3 * defectO10 m θ faceAxis (fun _ => 2) (oNum m) +
        defectO10_num_residual_constant θ := by
  exact defectO10_succ_num_level5_constant_boundary
    θ (H10TransportAll_proved θ) m hm

/-- Unconditional closed affine form for the H10 numbering-orientation defect. -/
theorem defectO10_num_affine_closed_form_from_level5_unconditional
    (θ : ℝ) :
    ∀ n : ℕ,
      defectO10 (n + 5) θ faceAxis (fun _ => 2) (oNum (n + 5)) =
        (3 : ℂ) ^ n *
          (defectO10 5 θ faceAxis (fun _ => 2) (oNum 5) +
            defectO10_num_residual_constant θ / 2) -
          defectO10_num_residual_constant θ / 2 := by
  exact defectO10_num_affine_closed_form_from_level5
    θ (H10TransportAll_proved θ)

end EvgenyTheorem
