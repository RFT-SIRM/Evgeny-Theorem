import EvgenyTheorem.GlueTrace

namespace EvgenyTheorem

open Matrix

/-- Diagonal of a block-diagonal product. -/
theorem blockK_mul_diag {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
    (H G : ι → Matrix X X ℂ) (c : ι) (x : X) :
    (blockK H * blockK G) (c, x) (c, x) = (H c * G c) x x := by
  simp only [Matrix.mul_apply, blockK, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single c]
  · simp [Matrix.mul_apply]
  · intro c' _ hne
    simp [Ne.symm hne]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- `K` on the diagonal is the degree, whatever the axis function and orientation. -/
theorem sgK_diag (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (a : WSG m) :
    sgK m θ ax o a a = ((pdeg m a.2.1.1 : ℕ) : ℂ) := by
  obtain ⟨c, x, i⟩ := a
  cases c <;> simp [sgK, blockK, Hc, pHeO_diag]

/-- `K²` on the diagonal is `d² + d`, whatever the axis function. -/
theorem sgK_sq_diag (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (o : Point → Point → Prop)
    [DecidableRel o] (hanti : OAnti (m + 1) o) (a : WSG m) :
    (sgK m θ ax o * sgK m θ ax o) a a =
      ((pdeg m a.2.1.1 : ℕ) : ℂ) ^ 2 + ((pdeg m a.2.1.1 : ℕ) : ℂ) := by
  obtain ⟨c, x, i⟩ := a
  unfold sgK
  rw [blockK_mul_diag]
  cases c
  · have e : Hc m θ ax o GCopy.A = pOpO m θ ax o := rfl
    have h := pOpO_sq_diag m θ ax o (oanti_A m o hanti) x i i
    rw [e]
    simpa using h
  · have e : Hc m θ ax o GCopy.B = pOpO m θ ax (oBo m o) := rfl
    have h := pOpO_sq_diag m θ ax (oBo m o) (oanti_B m o hanti) x i i
    rw [e]
    simpa using h
  · have e : Hc m θ ax o GCopy.C = pOpO m θ ax (oCo m o) := rfl
    have h := pOpO_sq_diag m θ ax (oCo m o) (oanti_C m o hanti) x i i
    rw [e]
    simpa using h

end EvgenyTheorem
