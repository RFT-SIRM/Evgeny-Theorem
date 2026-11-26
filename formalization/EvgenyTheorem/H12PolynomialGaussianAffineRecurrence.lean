import EvgenyTheorem.H12PolynomialGaussianCoefficientRecurrence

namespace EvgenyTheorem

def h12GaussianPsEntryFor
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (p q : Point) (i j : C2) : GaussianInt :=
  if p = q then 0
  else if EdgeB 3 p.1 p.2 q.1 q.2 = true then
    let e : Point × Point := if p ≤ q then (p, q) else (q, p)
    if e ∈ fluxEdges 3 then
      if o p q then
        -(h12GaussianAxisSForward
          (ax (h12GaussianFluxIndex 3 e)) i j)
      else
        -(h12GaussianAxisSAdjoint
          (ax (h12GaussianFluxIndex 3 e)) i j)
    else 0
  else 0

theorem h12GaussianPHeO_affine_entry_for
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (p q : Point) (i j : C2) :
    h12GaussianPHeO 3 ax o p q i j =
      MvPolynomial.C (h12GaussianP0Entry p q i j) +
        MvPolynomial.C (h12GaussianPcEntry p q i j) *
          h12GaussianC +
        MvPolynomial.C (h12GaussianPsEntryFor ax o p q i j) *
          h12GaussianS := by
  classical
  by_cases hp : p = q
  · subst q
    by_cases hij : i = j
    · simp [h12GaussianPHeO, h12GaussianP0Entry,
        h12GaussianPcEntry, h12GaussianPsEntryFor,
        h12GaussianC, h12GaussianS, hij]
    · simp [h12GaussianPHeO, h12GaussianP0Entry,
        h12GaussianPcEntry, h12GaussianPsEntryFor,
        h12GaussianC, h12GaussianS, hij]
  · by_cases he : EdgeB 3 p.1 p.2 q.1 q.2 = true
    · let e : Point × Point := if p ≤ q then (p, q) else (q, p)
      by_cases hf : e ∈ fluxEdges 3
      · by_cases ho : o p q
        · have haxis := h12GaussianAxisRotationPoly_entry
            (ax (h12GaussianFluxIndex 3 e)) i j
          simp [h12GaussianPHeO, h12GaussianP0Entry,
            h12GaussianPcEntry, h12GaussianPsEntryFor,
            h12GaussianEdgePoly, h12GaussianC, h12GaussianS,
            hp, he, hf, ho, e, haxis]
          by_cases hij : i = j <;> simp [hij] <;> ring
        · have haxis := h12GaussianAxisRotationPolyAdjoint_entry
            (ax (h12GaussianFluxIndex 3 e)) i j
          simp [h12GaussianPHeO, h12GaussianP0Entry,
            h12GaussianPcEntry, h12GaussianPsEntryFor,
            h12GaussianEdgePolyAdjoint, h12GaussianC,
            h12GaussianS, hp, he, hf, ho, e, haxis]
          by_cases hij : i = j <;> simp [hij] <;> ring
      · by_cases hij : i = j <;>
          simp [h12GaussianPHeO, h12GaussianP0Entry,
            h12GaussianPcEntry, h12GaussianPsEntryFor,
            h12GaussianEdgePoly, h12GaussianEdgePolyAdjoint,
            h12GaussianC, h12GaussianS, hp, he, hf, e, hij,
            Matrix.one_apply]
    · simp [h12GaussianPHeO, h12GaussianP0Entry,
        h12GaussianPcEntry, h12GaussianPsEntryFor,
        h12GaussianC, h12GaussianS, hp, he]

theorem h12GaussianPMatrixFor_affine
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    h12GaussianPMatrixFor ax o =
      (fun x y =>
        MvPolynomial.C
          (h12GaussianP0Entry x.1.1 y.1.1 x.2 y.2) +
        MvPolynomial.C
          (h12GaussianPcEntry x.1.1 y.1.1 x.2 y.2) *
          h12GaussianC +
        MvPolynomial.C
          (h12GaussianPsEntryFor ax o x.1.1 y.1.1 x.2 y.2) *
          h12GaussianS) := by
  apply Matrix.ext
  intro x y
  exact h12GaussianPHeO_affine_entry_for
    ax o x.1.1 y.1.1 x.2 y.2


def h12GaussianP0Matrix :
    Matrix H12GaussianIndex3 H12GaussianIndex3 GaussianInt :=
  fun x y => h12GaussianP0Entry x.1.1 y.1.1 x.2 y.2

def h12GaussianPcMatrix :
    Matrix H12GaussianIndex3 H12GaussianIndex3 GaussianInt :=
  fun x y => h12GaussianPcEntry x.1.1 y.1.1 x.2 y.2

def h12GaussianPsMatrixFor
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    Matrix H12GaussianIndex3 H12GaussianIndex3 GaussianInt :=
  fun x y => h12GaussianPsEntryFor ax o x.1.1 y.1.1 x.2 y.2

theorem h12GaussianPMatrixFor_affine_coeff_matrices
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    h12GaussianPMatrixFor ax o =
      (fun x y =>
        MvPolynomial.C (h12GaussianP0Matrix x y) +
        MvPolynomial.C (h12GaussianPcMatrix x y) *
          h12GaussianC +
        MvPolynomial.C (h12GaussianPsMatrixFor ax o x y) *
          h12GaussianS) := by
  apply Matrix.ext
  intro x y
  exact h12GaussianPHeO_affine_entry_for
    ax o x.1.1 y.1.1 x.2 y.2


theorem h12GaussianPHeO_coeff_three_monomials
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (p q : Point) (i j : C2) (e : H12Exponent) :
    MvPolynomial.coeff e (h12GaussianPHeO 3 ax o p q i j) =
      (if e = 0 then h12GaussianP0Entry p q i j else 0) +
      (if e = Finsupp.single (0 : Fin 2) 1
        then h12GaussianPcEntry p q i j else 0) +
      (if e = Finsupp.single (1 : Fin 2) 1
        then h12GaussianPsEntryFor ax o p q i j else 0) := by
  classical
  rw [h12GaussianPHeO_affine_entry_for]
  simp [h12GaussianC, h12GaussianS, MvPolynomial.coeff_X, eq_comm]

theorem h12GaussianPMatrixFor_coeff_three_monomials
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (e : H12Exponent) :
    h12GaussianCoefficientFamilyOf (h12GaussianPMatrixFor ax o) e =
      fun x y =>
        (if e = 0 then h12GaussianP0Entry x.1.1 y.1.1 x.2 y.2 else 0) +
        (if e = Finsupp.single (0 : Fin 2) 1
          then h12GaussianPcEntry x.1.1 y.1.1 x.2 y.2 else 0) +
        (if e = Finsupp.single (1 : Fin 2) 1
          then h12GaussianPsEntryFor ax o x.1.1 y.1.1 x.2 y.2 else 0) := by
  apply Matrix.ext
  intro x y
  change MvPolynomial.coeff e
      (h12GaussianPHeO 3 ax o x.1.1 y.1.1 x.2 y.2) = _
  exact h12GaussianPHeO_coeff_three_monomials
    ax o x.1.1 y.1.1 x.2 y.2 e


theorem h12GaussianCoeff_mul_affine
    (p : H12GaussianPoly) (a b c : GaussianInt)
    (e : H12Exponent) :
    MvPolynomial.coeff e
        (p * (MvPolynomial.C a +
          MvPolynomial.C b * h12GaussianC +
          MvPolynomial.C c * h12GaussianS)) =
      MvPolynomial.coeff e p * a +
      (if Finsupp.single (0 : Fin 2) 1 ≤ e then
        MvPolynomial.coeff
          (e - Finsupp.single (0 : Fin 2) 1) p * b else 0) +
      (if Finsupp.single (1 : Fin 2) 1 ≤ e then
        MvPolynomial.coeff
          (e - Finsupp.single (1 : Fin 2) 1) p * c else 0) := by
  have hconst :
      MvPolynomial.coeff e (p * MvPolynomial.C a) =
        MvPolynomial.coeff e p * a := by
    rw [mul_comm p (MvPolynomial.C a),
      MvPolynomial.coeff_C_mul]
    ring
  have hc :
      MvPolynomial.coeff e
          (p * (MvPolynomial.C b * h12GaussianC)) =
        (if Finsupp.single (0 : Fin 2) 1 ≤ e then
          MvPolynomial.coeff
            (e - Finsupp.single (0 : Fin 2) 1) p * b else 0) := by
    rw [h12GaussianC, MvPolynomial.C_mul_X_eq_monomial]
    exact MvPolynomial.coeff_mul_monomial' e
      (Finsupp.single (0 : Fin 2) 1) b p
  have hs :
      MvPolynomial.coeff e
          (p * (MvPolynomial.C c * h12GaussianS)) =
        (if Finsupp.single (1 : Fin 2) 1 ≤ e then
          MvPolynomial.coeff
            (e - Finsupp.single (1 : Fin 2) 1) p * c else 0) := by
    rw [h12GaussianS, MvPolynomial.C_mul_X_eq_monomial]
    exact MvPolynomial.coeff_mul_monomial' e
      (Finsupp.single (1 : Fin 2) 1) c p
  calc
    MvPolynomial.coeff e
        (p * (MvPolynomial.C a +
          MvPolynomial.C b * h12GaussianC +
          MvPolynomial.C c * h12GaussianS)) =
      MvPolynomial.coeff e (p * MvPolynomial.C a) +
      MvPolynomial.coeff e (p * (MvPolynomial.C b * h12GaussianC)) +
      MvPolynomial.coeff e (p * (MvPolynomial.C c * h12GaussianS)) := by
        rw [mul_add, mul_add, MvPolynomial.coeff_add,
          MvPolynomial.coeff_add]
    _ = _ := by rw [hconst, hc, hs]


noncomputable def h12GaussianAffineCoefficientConvolution
    (A : H12GaussianCoefficientFamily)
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (e : H12Exponent) :
    Matrix H12GaussianIndex3 H12GaussianIndex3 GaussianInt :=
  fun i j =>
    ∑ k : H12GaussianIndex3,
      (A e i k * h12GaussianP0Matrix k j +
        (if Finsupp.single (0 : Fin 2) 1 ≤ e then
          A (e - Finsupp.single (0 : Fin 2) 1) i k *
            h12GaussianPcMatrix k j else 0) +
        (if Finsupp.single (1 : Fin 2) 1 ≤ e then
          A (e - Finsupp.single (1 : Fin 2) 1) i k *
            h12GaussianPsMatrixFor ax o k j else 0))

theorem h12GaussianCoefficientFamily_mul_affine
    (M : Matrix H12GaussianIndex3 H12GaussianIndex3 H12GaussianPoly)
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (e : H12Exponent) :
    h12GaussianCoefficientFamilyOf
        (M * h12GaussianPMatrixFor ax o) e =
      h12GaussianAffineCoefficientConvolution
        (h12GaussianCoefficientFamilyOf M) ax o e := by
  classical
  apply Matrix.ext
  intro i j
  simp only [h12GaussianCoefficientFamilyOf,
    h12GaussianAffineCoefficientConvolution,
    Matrix.mul_apply, MvPolynomial.coeff_sum,
    h12GaussianPMatrixFor]
  apply Finset.sum_congr rfl
  intro k hk
  rw [h12GaussianPHeO_affine_entry_for ax o
    k.1.1 j.1.1 k.2 j.2]
  exact h12GaussianCoeff_mul_affine
    (M i k)
    (h12GaussianP0Matrix k j)
    (h12GaussianPcMatrix k j)
    (h12GaussianPsMatrixFor ax o k j)
    e


noncomputable def h12GaussianAffineCoefficientPower
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o] :
    ℕ → H12GaussianCoefficientFamily
  | 0 => fun e => if e = 0 then 1 else 0
  | n + 1 => fun e =>
      h12GaussianAffineCoefficientConvolution
        (h12GaussianAffineCoefficientPower ax o n) ax o e

theorem h12GaussianAffineCoefficientPower_correct
    (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (n : ℕ) :
    h12GaussianAffineCoefficientPower ax o n =
      h12GaussianCoefficientFamilyOf
        (h12GaussianPMatrixFor ax o ^ n) := by
  classical
  induction n with
  | zero =>
      simpa [h12GaussianAffineCoefficientPower,
        h12GaussianCoefficientPower] using
        (h12GaussianCoefficientPower_correct
          (h12GaussianPMatrixFor ax o) 0)
  | succ n ih =>
      funext e
      change h12GaussianAffineCoefficientConvolution
          (h12GaussianAffineCoefficientPower ax o n) ax o e =
        h12GaussianCoefficientFamilyOf
          (h12GaussianPMatrixFor ax o ^ (n + 1)) e
      rw [pow_succ, h12GaussianCoefficientFamily_mul_affine]
      rw [← ih]

end EvgenyTheorem
