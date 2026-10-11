import EvgenyTheorem.GlueCornerU
import EvgenyTheorem.PairUnit

namespace EvgenyTheorem

open Matrix

/-- Point-level 2×2 block of `pHeO`. -/
noncomputable def Bk (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (p q : Point) : Matrix C2 C2 ℂ :=
  Matrix.of fun i j => pHeO m θ ax o p q i j

theorem Bk_diag (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (p : Point) :
    Bk m θ ax o p p = ((pdeg m p : ℕ) : ℂ) • (1 : Matrix C2 C2 ℂ) := by
  ext i j
  simp only [Bk, Matrix.of_apply, pHeO_diag, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

theorem Bk_zero (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] {p q : Point} (hpq : p ≠ q)
    (hE : ¬ (EdgeB m p.1 p.2 q.1 q.2 = true)) :
    Bk m θ ax o p q = 0 := by
  ext i j
  simp [Bk, pHeO_zero_of_not_edge m θ ax o hpq hE]

open Classical in
theorem Bk_edge (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] {p q : Point} (hpq : p ≠ q)
    (hE : EdgeB m p.1 p.2 q.1 q.2 = true) :
    Bk m θ ax o p q =
      if o p q then -(edgeUnitaryWithAxis m θ ax (if p ≤ q then (p, q) else (q, p)))
      else -((edgeUnitaryWithAxis m θ ax (if p ≤ q then (p, q) else (q, p)))ᴴ) := by
  ext i j
  by_cases h : o p q
  · simp [Bk, pHeO_edge_eq m θ ax o hpq hE, h]
  · simp [Bk, pHeO_edge_eq m θ ax o hpq hE, h]

open Classical in
theorem Bk_swap (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] {p q : Point} (hpq : p ≠ q) (hanti : o p q ↔ ¬ o q p)
    (hE : EdgeB m p.1 p.2 q.1 q.2 = true) :
    Bk m θ ax o q p = (Bk m θ ax o p q)ᴴ := by
  have hqp : q ≠ p := hpq.symm
  have hE' : EdgeB m q.1 q.2 p.1 p.2 = true := by
    rw [EdgeB_symm m]
    exact hE
  rw [Bk_edge m θ ax o hqp hE', Bk_edge m θ ax o hpq hE, edgeU_swap m θ ax p q]
  generalize edgeUnitaryWithAxis m θ ax (if p ≤ q then (p, q) else (q, p)) = U
  by_cases h : o p q
  · have h' : ¬ o q p := hanti.mp h
    simp [h, h']
  · have h' : o q p := by
      by_contra hc
      exact h (hanti.mpr hc)
    simp [h, h']

open Classical in
theorem Bk_mul (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] {p q : Point} (hpq : p ≠ q) (hanti : o p q ↔ ¬ o q p)
    (hE : EdgeB m p.1 p.2 q.1 q.2 = true) :
    Bk m θ ax o p q * Bk m θ ax o q p = 1 := by
  rw [Bk_swap m θ ax o hpq hanti hE, Bk_edge m θ ax o hpq hE]
  have h1 := edgeUnitaryWithAxis_mul_conjTranspose m θ ax (if p ≤ q then (p, q) else (q, p))
  have h2 := edgeUnitaryWithAxis_conjTranspose_mul m θ ax (if p ≤ q then (p, q) else (q, p))
  generalize edgeUnitaryWithAxis m θ ax (if p ≤ q then (p, q) else (q, p)) = U at h1 h2 ⊢
  by_cases h : o p q
  · simp [h, h1]
  · simp [h, h2]

open Classical in
theorem Bk_nonflux (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] {p q : Point} (hpq : p ≠ q)
    (hE : EdgeB m p.1 p.2 q.1 q.2 = true)
    (hf : (if p ≤ q then (p, q) else (q, p)) ∉ fluxEdges m) :
    Bk m θ ax o p q = -1 := by
  rw [Bk_edge m θ ax o hpq hE]
  unfold edgeUnitaryWithAxis
  rw [if_neg hf]
  by_cases h : o p q <;> simp [h]

open Classical in
theorem Bk_add_conj_flux (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] {p q : Point} (hpq : p ≠ q)
    (hE : EdgeB m p.1 p.2 q.1 q.2 = true)
    (hf : (if p ≤ q then (p, q) else (q, p)) ∈ fluxEdges m) :
    Bk m θ ax o p q + (Bk m θ ax o p q)ᴴ = (-(2 * cC θ)) • (1 : Matrix C2 C2 ℂ) := by
  rw [Bk_edge m θ ax o hpq hE]
  have h := edgeU_add_conj m θ ax (if p ≤ q then (p, q) else (q, p))
  rw [if_pos hf] at h
  generalize edgeUnitaryWithAxis m θ ax (if p ≤ q then (p, q) else (q, p)) = U at h ⊢
  by_cases hp : o p q
  · rw [if_pos hp, Matrix.conjTranspose_neg, ← neg_add, h, neg_smul]
  · rw [if_neg hp, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose,
      ← neg_add, add_comm, h, neg_smul]

open Classical in
/-- A triangle with exactly one flux edge: the two orientations of the loop sum to `-2cos(θ/2)`. -/
theorem tri_add_conj (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] {p q r : Point} (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hEpq : EdgeB m p.1 p.2 q.1 q.2 = true) (hEqr : EdgeB m q.1 q.2 r.1 r.2 = true)
    (hErp : EdgeB m r.1 r.2 p.1 p.2 = true)
    (hone :
      ((if p ≤ q then (p, q) else (q, p)) ∈ fluxEdges m ∧
        (if q ≤ r then (q, r) else (r, q)) ∉ fluxEdges m ∧
        (if r ≤ p then (r, p) else (p, r)) ∉ fluxEdges m) ∨
      ((if p ≤ q then (p, q) else (q, p)) ∉ fluxEdges m ∧
        (if q ≤ r then (q, r) else (r, q)) ∈ fluxEdges m ∧
        (if r ≤ p then (r, p) else (p, r)) ∉ fluxEdges m) ∨
      ((if p ≤ q then (p, q) else (q, p)) ∉ fluxEdges m ∧
        (if q ≤ r then (q, r) else (r, q)) ∉ fluxEdges m ∧
        (if r ≤ p then (r, p) else (p, r)) ∈ fluxEdges m)) :
    Bk m θ ax o p q * Bk m θ ax o q r * Bk m θ ax o r p +
      (Bk m θ ax o p q * Bk m θ ax o q r * Bk m θ ax o r p)ᴴ =
        (-(2 * cC θ)) • (1 : Matrix C2 C2 ℂ) := by
  rcases hone with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [Bk_nonflux m θ ax o hqr hEqr h2, Bk_nonflux m θ ax o hrp hErp h3]
    simpa using Bk_add_conj_flux m θ ax o hpq hEpq h1
  · rw [Bk_nonflux m θ ax o hpq hEpq h1, Bk_nonflux m θ ax o hrp hErp h3]
    simpa using Bk_add_conj_flux m θ ax o hqr hEqr h2
  · rw [Bk_nonflux m θ ax o hpq hEpq h1, Bk_nonflux m θ ax o hqr hEqr h2]
    simpa using Bk_add_conj_flux m θ ax o hrp hErp h3

end EvgenyTheorem
