import EvgenyTheorem.GlueCornerTri

namespace EvgenyTheorem

open Matrix

/-- Nine-term expansion of the diagonal block of `B³` at a vertex `p` whose only
neighbours are `q` and `r`. -/
theorem cube_diag_abstract {V : Type*} [Fintype V] [DecidableEq V]
    (B : V → V → Matrix C2 C2 ℂ) (p q r : V) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hy : ∀ y, y ≠ p → y ≠ q → y ≠ r → B p y = 0)
    (hz : ∀ z, z ≠ p → z ≠ q → z ≠ r → B z p = 0)
    (dp dq dr : ℂ)
    (hpp : B p p = dp • (1 : Matrix C2 C2 ℂ))
    (hqq : B q q = dq • (1 : Matrix C2 C2 ℂ))
    (hrr : B r r = dr • (1 : Matrix C2 C2 ℂ))
    (hm1 : B p q * B q p = 1) (hm2 : B p r * B r p = 1)
    (hs1 : B q p = (B p q)ᴴ) (hs2 : B r q = (B q r)ᴴ) (hs3 : B p r = (B r p)ᴴ) :
    ∑ y, ∑ z, B p y * B y z * B z p =
      (dp ^ 3 + 4 * dp + dq + dr) • (1 : Matrix C2 C2 ℂ) +
        (B p q * B q r * B r p + (B p q * B q r * B r p)ᴴ) := by
  have key : ∀ f : V → Matrix C2 C2 ℂ,
      ∑ x ∈ ({p, q, r} : Finset V), f x = f p + f q + f r := by
    intro f
    rw [Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_pair hqr]
    abel
  have e1 : ∑ y, ∑ z, B p y * B y z * B z p =
      ∑ y ∈ ({p, q, r} : Finset V), ∑ z, B p y * B y z * B z p := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy'
    apply Finset.sum_eq_zero
    intro z _
    rw [hy y hy'.1 hy'.2.1 hy'.2.2, zero_mul, zero_mul]
  have e2 : ∀ y, ∑ z, B p y * B y z * B z p =
      ∑ z ∈ ({p, q, r} : Finset V), B p y * B y z * B z p := by
    intro y
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro z _ hz'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz'
    rw [hz z hz'.1 hz'.2.1 hz'.2.2, mul_zero]
  have hT : B p r * B r q * B q p = (B p q * B q r * B r p)ᴴ := by
    rw [hs3, hs2, hs1]
    simp [Matrix.conjTranspose_mul, mul_assoc]
  rw [e1, Finset.sum_congr rfl (fun y _ => e2 y)]
  simp only [key]
  rw [hT]
  simp only [hpp, hqq, hrr, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hm1, hm2,
    smul_smul]
  module

end EvgenyTheorem
