import EvgenyTheorem.H12PolynomialTargets
import Mathlib.Algebra.MvPolynomial.Eval

namespace EvgenyTheorem

abbrev H12ComplexPoly := MvPolynomial (Fin 2) ℂ

noncomputable def h12ComplexC : H12ComplexPoly :=
  MvPolynomial.X 0

noncomputable def h12ComplexS : H12ComplexPoly :=
  MvPolynomial.X 1

noncomputable def h12ComplexEval (θ : ℝ) :
    H12ComplexPoly →+* ℂ :=
  MvPolynomial.eval₂Hom (RingHom.id ℂ)
    (fun i : Fin 2 =>
      if i = 0 then Complex.ofReal (Real.cos (θ / 2))
      else Complex.ofReal (Real.sin (θ / 2)))

@[simp]
theorem h12ComplexEval_c (θ : ℝ) :
    h12ComplexEval θ h12ComplexC =
      Complex.ofReal (Real.cos (θ / 2)) := by
  simp [h12ComplexEval, h12ComplexC]

@[simp]
theorem h12ComplexEval_s (θ : ℝ) :
    h12ComplexEval θ h12ComplexS =
      Complex.ofReal (Real.sin (θ / 2)) := by
  simp [h12ComplexEval, h12ComplexS]

noncomputable def h12AxisRotationPoly :
    Axis → Matrix C2 C2 H12ComplexPoly
  | 0 =>
      !![h12ComplexC, -(MvPolynomial.C Complex.I * h12ComplexS);
         -(MvPolynomial.C Complex.I * h12ComplexS), h12ComplexC]
  | 1 =>
      !![h12ComplexC, -h12ComplexS;
         h12ComplexS, h12ComplexC]
  | 2 =>
      !![h12ComplexC - MvPolynomial.C Complex.I * h12ComplexS, 0;
         0, h12ComplexC + MvPolynomial.C Complex.I * h12ComplexS]

noncomputable def h12AxisRotationPolyAdjoint :
    Axis → Matrix C2 C2 H12ComplexPoly
  | 0 =>
      !![h12ComplexC, MvPolynomial.C Complex.I * h12ComplexS;
         MvPolynomial.C Complex.I * h12ComplexS, h12ComplexC]
  | 1 =>
      !![h12ComplexC, h12ComplexS;
         -h12ComplexS, h12ComplexC]
  | 2 =>
      !![h12ComplexC + MvPolynomial.C Complex.I * h12ComplexS, 0;
         0, h12ComplexC - MvPolynomial.C Complex.I * h12ComplexS]

private theorem h12_neg_sin_I_mul_sin_I (x : ℂ) :
    -Complex.sin x = Complex.I * Complex.sin x * Complex.I := by
  calc
    -Complex.sin x =
        (Complex.I * Complex.I) * Complex.sin x := by
      rw [Complex.I_mul_I]
      ring
    _ = Complex.I * Complex.sin x * Complex.I := by ring

private theorem h12_sin_eq_neg_I_mul_sin_I (x : ℂ) :
    Complex.sin x = -(Complex.I * Complex.sin x * Complex.I) := by
  calc
    Complex.sin x =
        -((Complex.I * Complex.I) * Complex.sin x) := by
      rw [Complex.I_mul_I]
      ring
    _ = -(Complex.I * Complex.sin x * Complex.I) := by ring

theorem h12_eval_axisRotationPoly (θ : ℝ) (a : Axis) :
    (h12AxisRotationPoly a).map (h12ComplexEval θ) =
      axisRotation a θ := by
  fin_cases a <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [h12AxisRotationPoly, h12ComplexEval, h12ComplexC, h12ComplexS,
      axisRotation, su2Rotation, axisPauli, pauliX, pauliY, pauliZ]
  all_goals
    first
    | exact h12_neg_sin_I_mul_sin_I _
    | exact h12_sin_eq_neg_I_mul_sin_I _

theorem h12_axisRotation_conjTranspose (θ : ℝ) (a : Axis) :
    Matrix.conjTranspose (axisRotation a θ) =
      axisRotation a (-θ) := by
  fin_cases a
  · simpa [axisRotation, axisPauli] using
      su2Rotation_pauliX_conjTranspose θ
  · simpa [axisRotation, axisPauli] using
      su2Rotation_pauliY_conjTranspose θ
  · simpa [axisRotation, axisPauli] using
      su2Rotation_pauliZ_conjTranspose θ

theorem h12_eval_axisRotationPolyAdjoint (θ : ℝ) (a : Axis) :
    (h12AxisRotationPolyAdjoint a).map (h12ComplexEval θ) =
      Matrix.conjTranspose (axisRotation a θ) := by
  have harg : (-θ) / 2 = -(θ / 2) := by ring
  have heval :
      (h12AxisRotationPolyAdjoint a).map (h12ComplexEval θ) =
        axisRotation a (-θ) := by
    fin_cases a <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [h12AxisRotationPolyAdjoint, h12ComplexEval,
        h12ComplexC, h12ComplexS, axisRotation, su2Rotation,
        axisPauli, pauliX, pauliY, pauliZ, harg,
        Real.cos_neg, Real.sin_neg]
    all_goals
      first
      | exact h12_neg_sin_I_mul_sin_I _
      | exact h12_sin_eq_neg_I_mul_sin_I _
  exact heval.trans (h12_axisRotation_conjTranspose θ a).symm

noncomputable def h12EdgePoly
    (m : ℕ) (ax : ℕ → Axis) (e : Point × Point) :
    Matrix C2 C2 H12ComplexPoly :=
  if e ∈ fluxEdges m then
    h12AxisRotationPoly (ax (fluxIndex m e))
  else 1

noncomputable def h12EdgePolyAdjoint
    (m : ℕ) (ax : ℕ → Axis) (e : Point × Point) :
    Matrix C2 C2 H12ComplexPoly :=
  if e ∈ fluxEdges m then
    h12AxisRotationPolyAdjoint (ax (fluxIndex m e))
  else 1

theorem h12_eval_edgePoly
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (e : Point × Point) :
    (h12EdgePoly m ax e).map (h12ComplexEval θ) =
      edgeUnitaryWithAxis m θ ax e := by
  by_cases he : e ∈ fluxEdges m
  · simp [h12EdgePoly, edgeUnitaryWithAxis, he,
      h12_eval_axisRotationPoly]
  · simp [h12EdgePoly, edgeUnitaryWithAxis, he]

theorem h12_eval_edgePolyAdjoint
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis) (e : Point × Point) :
    (h12EdgePolyAdjoint m ax e).map (h12ComplexEval θ) =
      Matrix.conjTranspose (edgeUnitaryWithAxis m θ ax e) := by
  by_cases he : e ∈ fluxEdges m
  · simp [h12EdgePolyAdjoint, edgeUnitaryWithAxis, he,
      h12_eval_axisRotationPolyAdjoint]
  · simp [h12EdgePolyAdjoint, edgeUnitaryWithAxis, he]

theorem h12_eval_edgePoly_apply
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (e : Point × Point) (i j : C2) :
    h12ComplexEval θ (h12EdgePoly m ax e i j) =
      edgeUnitaryWithAxis m θ ax e i j := by
  have h := congrArg (fun M : Matrix C2 C2 ℂ => M i j)
    (h12_eval_edgePoly m θ ax e)
  exact h

theorem h12_eval_edgePolyAdjoint_apply
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (e : Point × Point) (i j : C2) :
    h12ComplexEval θ (h12EdgePolyAdjoint m ax e i j) =
      Matrix.conjTranspose (edgeUnitaryWithAxis m θ ax e) i j := by
  have h := congrArg (fun M : Matrix C2 C2 ℂ => M i j)
    (h12_eval_edgePolyAdjoint m θ ax e)
  exact h

noncomputable def h12PHeO
    (m : ℕ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (p q : Point) (i j : C2) : H12ComplexPoly :=
  if p = q then
    if i = j then MvPolynomial.C ((pdeg m p : ℕ) : ℂ) else 0
  else if EdgeB m p.1 p.2 q.1 q.2 = true then
    let e : Point × Point :=
      if p ≤ q then (p, q) else (q, p)
    if o p q then
      -(h12EdgePoly m ax e i j)
    else
      -(h12EdgePolyAdjoint m ax e i j)
  else 0

theorem h12_eval_pHeO
    (m : ℕ) (θ : ℝ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (p q : Point) (i j : C2) :
    h12ComplexEval θ (h12PHeO m ax o p q i j) =
      pHeO m θ ax o p q i j := by
  classical
  by_cases hp : p = q
  · subst q
    by_cases hij : i = j <;>
      simp [h12PHeO, pHeO, h12ComplexEval, hij]
  · by_cases he : EdgeB m p.1 p.2 q.1 q.2 = true
    · by_cases ho : o p q
      · simp [h12PHeO, pHeO, hp, he, ho,
          h12_eval_edgePoly_apply]
      · simp [h12PHeO, pHeO, hp, he, ho,
          h12_eval_edgePolyAdjoint_apply]
    · simp [h12PHeO, pHeO, hp, he]

end EvgenyTheorem
