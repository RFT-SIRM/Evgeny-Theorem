import EvgenyTheorem.H12PolynomialTrace
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

namespace EvgenyTheorem

/-!
The level-three polynomial operator is affine in c and s.
We split it into three exact matrices over Gaussian integers. This is the
computable representation used by the coefficient recurrence; no evaluation
or multiplication in MvPolynomial is executed.
-/

abbrev H12GaussianPoly := MvPolynomial (Fin 2) GaussianInt

def h12GaussianC : H12GaussianPoly := MvPolynomial.X 0
def h12GaussianS : H12GaussianPoly := MvPolynomial.X 1
def h12GaussianI : GaussianInt := ⟨0, 1⟩

def h12GaussianMap : H12GaussianPoly →+* H12ComplexPoly :=
  MvPolynomial.map GaussianInt.toComplex

def h12GaussianFluxIndex (m : ℕ) (e : Point × Point) : ℕ :=
  (fluxEdges m).findIdx (fun f => decide (f = e))

theorem h12GaussianFluxIndex_eq (m : ℕ) (e : Point × Point) :
    h12GaussianFluxIndex m e = fluxIndex m e := by
  rfl

def h12GaussianAxisRotationPoly :
    Axis → Matrix C2 C2 H12GaussianPoly
  | 0 =>
      !![h12GaussianC, -(MvPolynomial.C h12GaussianI * h12GaussianS);
         -(MvPolynomial.C h12GaussianI * h12GaussianS), h12GaussianC]
  | 1 =>
      !![h12GaussianC, -h12GaussianS;
         h12GaussianS, h12GaussianC]
  | 2 =>
      !![h12GaussianC - MvPolynomial.C h12GaussianI * h12GaussianS, 0;
         0, h12GaussianC + MvPolynomial.C h12GaussianI * h12GaussianS]

def h12GaussianAxisRotationPolyAdjoint :
    Axis → Matrix C2 C2 H12GaussianPoly
  | 0 =>
      !![h12GaussianC, MvPolynomial.C h12GaussianI * h12GaussianS;
         MvPolynomial.C h12GaussianI * h12GaussianS, h12GaussianC]
  | 1 =>
      !![h12GaussianC, h12GaussianS;
         -h12GaussianS, h12GaussianC]
  | 2 =>
      !![h12GaussianC + MvPolynomial.C h12GaussianI * h12GaussianS, 0;
         0, h12GaussianC - MvPolynomial.C h12GaussianI * h12GaussianS]

/-- Coefficient of s in the forward SU(2) rotation matrix. -/
def h12GaussianAxisSForward : Axis → Matrix C2 C2 GaussianInt
  | 0 => !![0, -h12GaussianI; -h12GaussianI, 0]
  | 1 => !![0, -1; 1, 0]
  | 2 => !![-h12GaussianI, 0; 0, h12GaussianI]

/-- Coefficient of s in the adjoint SU(2) rotation matrix. -/
def h12GaussianAxisSAdjoint : Axis → Matrix C2 C2 GaussianInt
  | 0 => !![0, h12GaussianI; h12GaussianI, 0]
  | 1 => !![0, 1; -1, 0]
  | 2 => !![h12GaussianI, 0; 0, -h12GaussianI]

theorem h12GaussianAxisRotationPoly_entry (a : Axis) (i j : C2) :
    h12GaussianAxisRotationPoly a i j =
      (if i = j then h12GaussianC else 0) +
        MvPolynomial.C (h12GaussianAxisSForward a i j) * h12GaussianS := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [h12GaussianAxisRotationPoly, h12GaussianAxisSForward,
      h12GaussianC, h12GaussianS, h12GaussianI] <;> ring

theorem h12GaussianAxisRotationPolyAdjoint_entry (a : Axis) (i j : C2) :
    h12GaussianAxisRotationPolyAdjoint a i j =
      (if i = j then h12GaussianC else 0) +
        MvPolynomial.C (h12GaussianAxisSAdjoint a i j) * h12GaussianS := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [h12GaussianAxisRotationPolyAdjoint, h12GaussianAxisSAdjoint,
      h12GaussianC, h12GaussianS, h12GaussianI] <;> ring

noncomputable def h12GaussianEdgePoly
    (m : ℕ) (ax : ℕ → Axis) (e : Point × Point) :
    Matrix C2 C2 H12GaussianPoly :=
  if e ∈ fluxEdges m then
    h12GaussianAxisRotationPoly (ax (h12GaussianFluxIndex m e))
  else 1

noncomputable def h12GaussianEdgePolyAdjoint
    (m : ℕ) (ax : ℕ → Axis) (e : Point × Point) :
    Matrix C2 C2 H12GaussianPoly :=
  if e ∈ fluxEdges m then
    h12GaussianAxisRotationPolyAdjoint (ax (h12GaussianFluxIndex m e))
  else 1

/-- Constant coefficient of an entry of the level-three number-oriented
Gaussian polynomial operator. -/
def h12GaussianP0Entry (p q : Point) (i j : C2) : GaussianInt :=
  if p = q then
    if i = j then (pdeg 3 p : GaussianInt) else 0
  else if EdgeB 3 p.1 p.2 q.1 q.2 = true then
    let e := if p ≤ q then (p, q) else (q, p)
    if e ∈ fluxEdges 3 then 0 else if i = j then -1 else 0
  else 0

/-- Coefficient of c in an entry of the level-three number-oriented
Gaussian polynomial operator. -/
def h12GaussianPcEntry (p q : Point) (i j : C2) : GaussianInt :=
  if p = q then 0
  else if EdgeB 3 p.1 p.2 q.1 q.2 = true then
    let e := if p ≤ q then (p, q) else (q, p)
    if e ∈ fluxEdges 3 then if i = j then -1 else 0 else 0
  else 0

/-- Coefficient of s in an entry of the level-three number-oriented
Gaussian polynomial operator. -/
def h12GaussianPsEntry (p q : Point) (i j : C2) : GaussianInt :=
  if p = q then 0
  else if EdgeB 3 p.1 p.2 q.1 q.2 = true then
    let e := if p ≤ q then (p, q) else (q, p)
    if e ∈ fluxEdges 3 then
      if oNum 3 p q then
        -(h12GaussianAxisSForward (faceAxis (h12GaussianFluxIndex 3 e)) i j)
      else
        -(h12GaussianAxisSAdjoint (faceAxis (h12GaussianFluxIndex 3 e)) i j)
    else 0
  else 0

theorem h12GaussianPHeO_affine_entry
    (p q : Point) (i j : C2) :
    h12GaussianPHeO 3 faceAxis (oNum 3) p q i j =
      MvPolynomial.C (h12GaussianP0Entry p q i j) +
        MvPolynomial.C (h12GaussianPcEntry p q i j) * h12GaussianC +
        MvPolynomial.C (h12GaussianPsEntry p q i j) * h12GaussianS := by
  classical
  by_cases hp : p = q
  · subst q
    by_cases hij : i = j
    · simp [h12GaussianPHeO, h12GaussianP0Entry, h12GaussianPcEntry,
        h12GaussianPsEntry, h12GaussianC, h12GaussianS, hij]
    · simp [h12GaussianPHeO, h12GaussianP0Entry, h12GaussianPcEntry,
        h12GaussianPsEntry, h12GaussianC, h12GaussianS, hij]
  · by_cases he : EdgeB 3 p.1 p.2 q.1 q.2 = true
    · let e : Point × Point := if p ≤ q then (p, q) else (q, p)
      by_cases hf : e ∈ fluxEdges 3
      · by_cases ho : oNum 3 p q
        · have haxis := h12GaussianAxisRotationPoly_entry
            (faceAxis (h12GaussianFluxIndex 3 e)) i j
          simp [h12GaussianPHeO, h12GaussianP0Entry, h12GaussianPcEntry,
            h12GaussianPsEntry, h12GaussianEdgePoly, h12GaussianFluxIndex_eq,
            h12GaussianC, h12GaussianS, hp, he, hf, ho, e, haxis]
          <;> ring
        · have haxis := h12GaussianAxisRotationPolyAdjoint_entry
            (faceAxis (h12GaussianFluxIndex 3 e)) i j
          simp [h12GaussianPHeO, h12GaussianP0Entry, h12GaussianPcEntry,
            h12GaussianPsEntry, h12GaussianEdgePolyAdjoint,
            h12GaussianFluxIndex_eq, h12GaussianC, h12GaussianS,
            hp, he, hf, ho, e, haxis]
          <;> ring
      · simp [h12GaussianPHeO, h12GaussianP0Entry, h12GaussianPcEntry,
          h12GaussianPsEntry, h12GaussianEdgePoly, h12GaussianEdgePolyAdjoint,
          h12GaussianC, h12GaussianS, hp, he, hf, e]
    · simp [h12GaussianPHeO, h12GaussianP0Entry, h12GaussianPcEntry,
        h12GaussianPsEntry, h12GaussianC, h12GaussianS, hp, he]

abbrev H12GaussianIndex3 := Pt 3 × C2

def h12GaussianP0Matrix :
    Matrix H12GaussianIndex3 H12GaussianIndex3 GaussianInt :=
  fun x y => h12GaussianP0Entry x.1.1 y.1.1 x.2 y.2

def h12GaussianPcMatrix :
    Matrix H12GaussianIndex3 H12GaussianIndex3 GaussianInt :=
  fun x y => h12GaussianPcEntry x.1.1 y.1.1 x.2 y.2

def h12GaussianPsMatrix :
    Matrix H12GaussianIndex3 H12GaussianIndex3 GaussianInt :=
  fun x y => h12GaussianPsEntry x.1.1 y.1.1 x.2 y.2

theorem h12GaussianPMatrix_affine :
    ∀ x y : H12GaussianIndex3,
      h12GaussianPMatrix 3 faceAxis (oNum 3) x y =
        MvPolynomial.C (h12GaussianP0Matrix x y) +
          MvPolynomial.C (h12GaussianPcMatrix x y) * h12GaussianC +
          MvPolynomial.C (h12GaussianPsMatrix x y) * h12GaussianS := by
  intro x y
  exact h12GaussianPHeO_affine_entry x.1.1 y.1.1 x.2 y.2

end EvgenyTheorem
