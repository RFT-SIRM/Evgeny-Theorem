import EvgenyTheorem.H12PolynomialGaussianBase

namespace EvgenyTheorem

noncomputable def h12GaussianPolyToComplex : H12GaussianPoly →+* H12ComplexPoly :=
  MvPolynomial.map GaussianInt.toComplex

@[simp] theorem h12GaussianI_toComplex :
    GaussianInt.toComplex h12GaussianI = Complex.I := by
  norm_num [h12GaussianI, GaussianInt.toComplex]

theorem h12GaussianAxisRotationPoly_map (a : Axis) :
    (h12GaussianAxisRotationPoly a).map h12GaussianPolyToComplex =
      h12AxisRotationPoly a := by
  fin_cases a
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h12GaussianAxisRotationPoly, h12AxisRotationPoly,
        h12GaussianPolyToComplex, h12GaussianC, h12ComplexC,
        h12GaussianS, h12ComplexS, h12GaussianI_toComplex]

theorem h12GaussianAxisRotationPolyAdjoint_map (a : Axis) :
    (h12GaussianAxisRotationPolyAdjoint a).map h12GaussianPolyToComplex =
      h12AxisRotationPolyAdjoint a := by
  fin_cases a
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h12GaussianAxisRotationPolyAdjoint,
        h12AxisRotationPolyAdjoint, h12GaussianPolyToComplex,
        h12GaussianC, h12ComplexC, h12GaussianS, h12ComplexS,
        h12GaussianI_toComplex]

theorem h12GaussianEdgePoly_map
    (m : ℕ) (ax : ℕ → Axis) (e : Point × Point) :
    (h12GaussianEdgePoly m ax e).map h12GaussianPolyToComplex =
      h12EdgePoly m ax e := by
  by_cases he : e ∈ fluxEdges m
  · simp [h12GaussianEdgePoly, h12EdgePoly, he,
      h12GaussianAxisRotationPoly_map, h12GaussianFluxIndex_eq]
  · simp [h12GaussianEdgePoly, h12EdgePoly, he]

theorem h12GaussianEdgePolyAdjoint_map
    (m : ℕ) (ax : ℕ → Axis) (e : Point × Point) :
    (h12GaussianEdgePolyAdjoint m ax e).map h12GaussianPolyToComplex =
      h12EdgePolyAdjoint m ax e := by
  by_cases he : e ∈ fluxEdges m
  · simp [h12GaussianEdgePolyAdjoint, h12EdgePolyAdjoint, he,
      h12GaussianAxisRotationPolyAdjoint_map, h12GaussianFluxIndex_eq]
  · simp [h12GaussianEdgePolyAdjoint, h12EdgePolyAdjoint, he]

theorem h12GaussianEdgePoly_apply_map
    (m : ℕ) (ax : ℕ → Axis) (e : Point × Point) (i j : C2) :
    h12GaussianPolyToComplex (h12GaussianEdgePoly m ax e i j) =
      h12EdgePoly m ax e i j := by
  have h := congrArg
    (fun M : Matrix C2 C2 H12ComplexPoly => M i j)
    (h12GaussianEdgePoly_map m ax e)
  simpa only [Matrix.map_apply] using h

theorem h12GaussianEdgePolyAdjoint_apply_map
    (m : ℕ) (ax : ℕ → Axis) (e : Point × Point) (i j : C2) :
    h12GaussianPolyToComplex (h12GaussianEdgePolyAdjoint m ax e i j) =
      h12EdgePolyAdjoint m ax e i j := by
  have h := congrArg
    (fun M : Matrix C2 C2 H12ComplexPoly => M i j)
    (h12GaussianEdgePolyAdjoint_map m ax e)
  simpa only [Matrix.map_apply] using h

theorem h12GaussianPHeO_map
    (m : ℕ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (p q : Point) (i j : C2) :
    h12GaussianPolyToComplex (h12GaussianPHeO m ax o p q i j) =
      h12PHeO m ax o p q i j := by
  classical
  by_cases hp : p = q
  · subst q
    by_cases hij : i = j
    · simp [h12GaussianPHeO, h12PHeO, h12GaussianPolyToComplex, hij]
    · simp [h12GaussianPHeO, h12PHeO, h12GaussianPolyToComplex, hij]
  · by_cases he : EdgeB m p.1 p.2 q.1 q.2 = true
    · by_cases ho : o p q
      · simp [h12GaussianPHeO, h12PHeO, hp, he, ho,
          h12GaussianEdgePoly_apply_map]
      · simp [h12GaussianPHeO, h12PHeO, hp, he, ho,
          h12GaussianEdgePolyAdjoint_apply_map]
    · simp [h12GaussianPHeO, h12PHeO, h12GaussianPolyToComplex,
        hp, he]

theorem h12GaussianPMatrix_map :
    h12GaussianPMatrix.map h12GaussianPolyToComplex =
      h12PMatrix 3 faceAxis (oNum 3) := by
  apply Matrix.ext
  intro x y
  change h12GaussianPolyToComplex (h12GaussianPMatrix x y) =
    h12PMatrix 3 faceAxis (oNum 3) x y
  exact h12GaussianPHeO_map 3 faceAxis (oNum 3)
    x.1.1 y.1.1 x.2 y.2

end EvgenyTheorem
