import EvgenyTheorem.H12PolynomialTrace
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

namespace EvgenyTheorem

abbrev H12GaussianPoly := MvPolynomial (Fin 2) GaussianInt

noncomputable def h12GaussianC : H12GaussianPoly := MvPolynomial.X 0
noncomputable def h12GaussianS : H12GaussianPoly := MvPolynomial.X 1

def h12GaussianI : GaussianInt := ⟨0, 1⟩

def h12GaussianFluxIndex (m : ℕ) (e : Point × Point) : ℕ :=
  List.idxOf e (fluxEdges m)

theorem h12GaussianFluxIndex_eq (m : ℕ) (e : Point × Point) :
    h12GaussianFluxIndex m e = fluxIndex m e := by
  exact (fluxIndex_eq_idxOf m e).symm

noncomputable def h12GaussianAxisRotationPoly :
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

noncomputable def h12GaussianAxisRotationPolyAdjoint :
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

def h12GaussianAxisSForward : Axis → Matrix C2 C2 GaussianInt
  | 0 => !![0, -h12GaussianI; -h12GaussianI, 0]
  | 1 => !![0, -1; 1, 0]
  | 2 => !![-h12GaussianI, 0; 0, h12GaussianI]

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
      h12GaussianC, h12GaussianS, h12GaussianI] <;> ring_nf

theorem h12GaussianAxisRotationPolyAdjoint_entry (a : Axis) (i j : C2) :
    h12GaussianAxisRotationPolyAdjoint a i j =
      (if i = j then h12GaussianC else 0) +
        MvPolynomial.C (h12GaussianAxisSAdjoint a i j) * h12GaussianS := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [h12GaussianAxisRotationPolyAdjoint, h12GaussianAxisSAdjoint,
      h12GaussianC, h12GaussianS, h12GaussianI] <;> ring_nf

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

noncomputable def h12GaussianPHeO
    (m : ℕ) (ax : ℕ → Axis)
    (o : Point → Point → Prop) [DecidableRel o]
    (p q : Point) (i j : C2) : H12GaussianPoly :=
  if p = q then
    if i = j then MvPolynomial.C ((pdeg m p : ℕ) : GaussianInt) else 0
  else if EdgeB m p.1 p.2 q.1 q.2 = true then
    let e : Point × Point := if p ≤ q then (p, q) else (q, p)
    if o p q then
      -(h12GaussianEdgePoly m ax e i j)
    else
      -(h12GaussianEdgePolyAdjoint m ax e i j)
  else 0

def h12GaussianP0Entry (p q : Point) (i j : C2) : GaussianInt :=
  if p = q then
    if i = j then (pdeg 3 p : GaussianInt) else 0
  else if EdgeB 3 p.1 p.2 q.1 q.2 = true then
    let e := if p ≤ q then (p, q) else (q, p)
    if e ∈ fluxEdges 3 then 0 else if i = j then -1 else 0
  else 0

def h12GaussianPcEntry (p q : Point) (i j : C2) : GaussianInt :=
  if p = q then 0
  else if EdgeB 3 p.1 p.2 q.1 q.2 = true then
    let e := if p ≤ q then (p, q) else (q, p)
    if e ∈ fluxEdges 3 then if i = j then -1 else 0 else 0
  else 0

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
          by_cases hij : i = j
          · subst i
            have hrot :
                h12GaussianAxisRotationPoly
                    (faceAxis (h12GaussianFluxIndex 3
                      (if p ≤ q then (p, q) else (q, p)))) j j =
                  MvPolynomial.X 0 +
                    MvPolynomial.C
                      (h12GaussianAxisSForward
                        (faceAxis (h12GaussianFluxIndex 3
                          (if p ≤ q then (p, q) else (q, p)))) j j) *
                      MvPolynomial.X 1 := by
              simpa [e, h12GaussianC, h12GaussianS] using haxis
            simp [h12GaussianPHeO, h12GaussianP0Entry,
              h12GaussianPcEntry, h12GaussianPsEntry,
              h12GaussianEdgePoly, h12GaussianC, h12GaussianS,
              hp, he, hf, ho, e]
            rw [hrot]
            ring
          · simp [h12GaussianPHeO, h12GaussianP0Entry,
              h12GaussianPcEntry, h12GaussianPsEntry,
              h12GaussianEdgePoly, h12GaussianC, h12GaussianS,
              hp, he, hf, ho, e, haxis, hij]
            <;> ring_nf
        · have haxis := h12GaussianAxisRotationPolyAdjoint_entry
            (faceAxis (h12GaussianFluxIndex 3 e)) i j
          by_cases hij : i = j
          · subst i
            have hrot :
                h12GaussianAxisRotationPolyAdjoint
                    (faceAxis (h12GaussianFluxIndex 3
                      (if p ≤ q then (p, q) else (q, p)))) j j =
                  MvPolynomial.X 0 +
                    MvPolynomial.C
                      (h12GaussianAxisSAdjoint
                        (faceAxis (h12GaussianFluxIndex 3
                          (if p ≤ q then (p, q) else (q, p)))) j j) *
                      MvPolynomial.X 1 := by
              simpa [e, h12GaussianC, h12GaussianS] using haxis
            simp [h12GaussianPHeO, h12GaussianP0Entry,
              h12GaussianPcEntry, h12GaussianPsEntry,
              h12GaussianEdgePolyAdjoint, h12GaussianC, h12GaussianS,
              hp, he, hf, ho, e]
            rw [hrot]
            ring
          · simp [h12GaussianPHeO, h12GaussianP0Entry,
              h12GaussianPcEntry, h12GaussianPsEntry,
              h12GaussianEdgePolyAdjoint, h12GaussianC, h12GaussianS,
              hp, he, hf, ho, e, haxis, hij]
            <;> ring_nf
      · by_cases hij : i = j
        · simp [h12GaussianPHeO, h12GaussianP0Entry,
            h12GaussianPcEntry, h12GaussianPsEntry,
            h12GaussianEdgePoly, h12GaussianEdgePolyAdjoint,
            h12GaussianC, h12GaussianS, hp, he, hf, e, hij,
            Matrix.one_apply]
        · simp [h12GaussianPHeO, h12GaussianP0Entry,
            h12GaussianPcEntry, h12GaussianPsEntry,
            h12GaussianEdgePoly, h12GaussianEdgePolyAdjoint,
            h12GaussianC, h12GaussianS, hp, he, hf, e, hij,
            Matrix.one_apply]
    · simp [h12GaussianPHeO, h12GaussianP0Entry, h12GaussianPcEntry,
        h12GaussianPsEntry, h12GaussianC, h12GaussianS, hp, he]

abbrev H12GaussianIndex3 := Pt 3 × C2

noncomputable def h12GaussianPMatrix :
    Matrix H12GaussianIndex3 H12GaussianIndex3 H12GaussianPoly :=
  fun x y =>
    h12GaussianPHeO 3 faceAxis (oNum 3) x.1.1 y.1.1 x.2 y.2

theorem h12GaussianPMatrix_affine :
    ∀ x y : H12GaussianIndex3,
      h12GaussianPMatrix x y =
        MvPolynomial.C (h12GaussianP0Entry x.1.1 y.1.1 x.2 y.2) +
          MvPolynomial.C (h12GaussianPcEntry x.1.1 y.1.1 x.2 y.2) *
            h12GaussianC +
          MvPolynomial.C (h12GaussianPsEntry x.1.1 y.1.1 x.2 y.2) *
            h12GaussianS := by
  intro x y
  exact h12GaussianPHeO_affine_entry x.1.1 y.1.1 x.2 y.2

end EvgenyTheorem
