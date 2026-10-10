import EvgenyTheorem.PairUnit

namespace EvgenyTheorem

open Matrix

open Classical in
/-- `pHeO` depends on the orientation only through its values on flux edges. -/
theorem pHeO_orient_congr (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o o' : Point → Point → Prop)
    [DecidableRel o] [DecidableRel o']
    (h : ∀ p q : Point, p ≠ q → EdgeB m p.1 p.2 q.1 q.2 = true →
      (if p ≤ q then (p, q) else (q, p)) ∈ fluxEdges m → (o p q ↔ o' p q))
    (p q : Point) (i j : C2) :
    pHeO m θ ax o p q i j = pHeO m θ ax o' p q i j := by
  by_cases hpq : p = q
  · subst hpq
    rw [pHeO_diag, pHeO_diag]
  · by_cases hE : EdgeB m p.1 p.2 q.1 q.2 = true
    · rw [pHeO_edge_eq m θ ax o hpq hE, pHeO_edge_eq m θ ax o' hpq hE]
      by_cases hf : (if p ≤ q then (p, q) else (q, p)) ∈ fluxEdges m
      · have ho := h p q hpq hE hf
        by_cases hp : o p q
        · rw [if_pos hp, if_pos (ho.mp hp)]
        · rw [if_neg hp, if_neg (fun h' => hp (ho.mpr h'))]
      · have hU : edgeUnitaryWithAxis m θ ax (if p ≤ q then (p, q) else (q, p)) = 1 := by
          unfold edgeUnitaryWithAxis
          rw [if_neg hf]
        rw [hU, Matrix.conjTranspose_one, ite_self, ite_self]
    · rw [pHeO_zero_of_not_edge m θ ax o hpq hE, pHeO_zero_of_not_edge m θ ax o' hpq hE]

/-- The point-level operator with an arbitrary orientation. -/
noncomputable def pOpO (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] : Matrix (Pt m × C2) (Pt m × C2) ℂ :=
  fun x y => pHeO m θ ax o x.1.1 y.1.1 x.2 y.2

theorem pOp_eq_pOpO (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) :
    pOp m θ ax = pOpO m θ ax (fun p q => vIdx m p ≤ vIdx m q) := by
  funext x y
  exact pHe_eq_pHeO m θ ax _ _ _ _

/-- Antisymmetry of an orientation on the points of `SG(m)`. -/
def OAnti (m : ℕ) (o : Point → Point → Prop) : Prop :=
  ∀ p q : Point, p ∈ vertexOrder m → q ∈ vertexOrder m → p ≠ q → (o p q ↔ ¬ o q p)

theorem pHeO_edge_mul' (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (hanti : OAnti m o) {p q : Point} (hpq : p ≠ q)
    (hE : EdgeB m p.1 p.2 q.1 q.2 = true) (i j : C2) :
    ∑ k : C2, pHeO m θ ax o p q i k * pHeO m θ ax o q p k j = if i = j then 1 else 0 := by
  have hm := EdgeB_mem m _ _ _ _ hE
  have hp : p ∈ vertexOrder m := (mem_vertexOrder_iff m p).mpr hm.1
  have hq : q ∈ vertexOrder m := (mem_vertexOrder_iff m q).mpr hm.2
  exact pHeO_edge_mul m θ ax o hpq (hanti p q hp hq hpq) hE i j

theorem diag_mul (d : ℂ) (i j : C2) :
    ∑ k : C2, (if i = k then d else 0) * (if k = j then d else 0) =
      d ^ 2 * (if i = j then 1 else 0) := by
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · simp [pow_two]
    · intro k _ hk
      simp [Ne.symm hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hij, mul_zero]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases hik : i = k
    · subst hik
      simp [hij]
    · simp [hik]

/-- Diagonal block of `K²` at a point: `(d² + d) · 1`. -/
theorem pOpO_sq_diag (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (hanti : OAnti m o) (c : Pt m) (i j : C2) :
    (pOpO m θ ax o * pOpO m θ ax o) (c, i) (c, j) =
      (((pdeg m c.1 : ℕ) : ℂ) ^ 2 + ((pdeg m c.1 : ℕ) : ℂ)) * (if i = j then 1 else 0) := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  have hrow : ∀ r : Pt m,
      ∑ k : C2, pOpO m θ ax o (c, i) (r, k) * pOpO m θ ax o (r, k) (c, j) =
      ((if r.1 = c.1 then ((pdeg m c.1 : ℕ) : ℂ) ^ 2 else 0) +
        (if EdgeB m c.1.1 c.1.2 r.1.1 r.1.2 = true then 1 else 0)) *
        (if i = j then 1 else 0) := by
    intro r
    simp only [pOpO]
    by_cases hr : r.1 = c.1
    · have e1 : ∀ k : C2, pHeO m θ ax o c.1 r.1 i k = if i = k then ((pdeg m c.1 : ℕ) : ℂ) else 0 :=
        fun k => by rw [hr, pHeO_diag]
      have e2 : ∀ k : C2, pHeO m θ ax o r.1 c.1 k j = if k = j then ((pdeg m c.1 : ℕ) : ℂ) else 0 :=
        fun k => by rw [hr, pHeO_diag]
      simp only [e1, e2]
      rw [diag_mul]
      have hf : ¬ (EdgeB m c.1.1 c.1.2 r.1.1 r.1.2 = true) := by
        rw [hr]
        simp [EdgeB_irrefl]
      rw [if_pos hr, if_neg hf, add_zero]
    · have hne : c.1 ≠ r.1 := fun h => hr h.symm
      by_cases hE : EdgeB m c.1.1 c.1.2 r.1.1 r.1.2 = true
      · rw [if_neg hr, if_pos hE, zero_add, one_mul]
        exact pHeO_edge_mul' m θ ax o hanti hne hE i j
      · rw [if_neg hr, if_neg hE, add_zero, zero_mul]
        refine Finset.sum_eq_zero (fun k _ => ?_)
        rw [pHeO_zero_of_not_edge m θ ax o hne hE, zero_mul]
  have hsingle : ∑ r : Pt m, (if r.1 = c.1 then ((pdeg m c.1 : ℕ) : ℂ) ^ 2 else 0) =
      ((pdeg m c.1 : ℕ) : ℂ) ^ 2 := by
    have h1 : ∀ r : Pt m, (if r.1 = c.1 then ((pdeg m c.1 : ℕ) : ℂ) ^ 2 else 0) =
        if r = c then ((pdeg m c.1 : ℕ) : ℂ) ^ 2 else 0 := by
      intro r
      by_cases h : r = c
      · subst h
        simp
      · have h' : r.1 ≠ c.1 := fun h'' => h (Subtype.ext h'')
        simp [h, h']
    rw [Finset.sum_congr rfl (fun r _ => h1 r), Finset.sum_ite_eq']
    simp
  have hdeg : ∑ r : Pt m, (if EdgeB m c.1.1 c.1.2 r.1.1 r.1.2 = true then (1 : ℂ) else 0) =
      ((pdeg m c.1 : ℕ) : ℂ) := by
    rw [pdeg_eq_sum, Nat.cast_sum, ← Finset.sum_coe_sort ((vertexOrder m).toFinset)]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun r _ => hrow r), ← Finset.sum_mul, Finset.sum_add_distrib,
    hsingle, hdeg]

end EvgenyTheorem
