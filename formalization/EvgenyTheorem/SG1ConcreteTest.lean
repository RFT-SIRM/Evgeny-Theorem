import EvgenyTheorem.Operator

namespace EvgenyTheorem

/-
  Concrete facts for the first Sierpiński graph (m = 1).
  These are deliberately kept separate from the main development.
-/

example :
    fluxEdges 1 =
      [((0, 0), (1, 0)),
       ((1, 0), (2, 0)),
       ((0, 1), (1, 1))] := by
  rfl

example :
    (fluxEdges 1).length = 3 := by
  rfl

example :
    ((0, 0), (1, 0)) ∈ fluxEdges 1 := by
  native_decide

example :
    fluxIndex 1 ((0, 0), (1, 0)) = 0 := by
  classical
  simp [fluxIndex, fluxEdges, facesExact, shiftFace, shiftPoint, fluxEdge] <;>
    native_decide

example :
    fluxIndex 1 ((1, 0), (2, 0)) = 1 := by
  classical
  simp [fluxIndex, fluxEdges, facesExact, shiftFace, shiftPoint, fluxEdge] <;>
    native_decide

example :
    fluxIndex 1 ((0, 1), (1, 1)) = 2 := by
  classical
  simp [fluxIndex, fluxEdges, facesExact, shiftFace, shiftPoint, fluxEdge] <;>
    native_decide

example :
    faceAxis (fluxIndex 1 ((0, 0), (1, 0))) = 0 := by
  rw [show fluxIndex 1 ((0, 0), (1, 0)) = 0 by
    classical
    simp [fluxIndex, fluxEdges, facesExact, shiftFace, shiftPoint, fluxEdge] <;>
      native_decide]
  exact faceAxis_zero

example :
    faceAxis (fluxIndex 1 ((1, 0), (2, 0))) = 1 := by
  rw [show fluxIndex 1 ((1, 0), (2, 0)) = 1 by
    classical
    simp [fluxIndex, fluxEdges, facesExact, shiftFace, shiftPoint, fluxEdge] <;>
      native_decide]
  exact faceAxis_one

example :
    faceAxis (fluxIndex 1 ((0, 1), (1, 1))) = 2 := by
  rw [show fluxIndex 1 ((0, 1), (1, 1)) = 2 by
    classical
    simp [fluxIndex, fluxEdges, facesExact, shiftFace, shiftPoint, fluxEdge] <;>
      native_decide]
  exact faceAxis_two

example :
    edgeUnitaryWithAxis 1 Real.pi faceAxis ((0, 0), (1, 0))
      = axisRotation 0 Real.pi := by
  have hmem : ((0, 0), (1, 0)) ∈ fluxEdges 1 := by
    native_decide
  have hidx : fluxIndex 1 ((0, 0), (1, 0)) = 0 := by
    classical
    simp [fluxIndex, fluxEdges, facesExact, shiftFace, shiftPoint, fluxEdge] <;>
      native_decide
  simp [edgeUnitaryWithAxis, hmem, hidx, faceAxis_zero]

example :
    edgeUnitaryWithAxis 1 Real.pi faceAxis ((1, 0), (2, 0))
      = axisRotation 1 Real.pi := by
  have hmem : ((1, 0), (2, 0)) ∈ fluxEdges 1 := by
    native_decide
  have hidx : fluxIndex 1 ((1, 0), (2, 0)) = 1 := by
    classical
    simp [fluxIndex, fluxEdges, facesExact, shiftFace, shiftPoint, fluxEdge] <;>
      native_decide
  simp [edgeUnitaryWithAxis, hmem, hidx, faceAxis_one]

example :
    edgeUnitaryWithAxis 1 Real.pi faceAxis ((0, 1), (1, 1))
      = axisRotation 2 Real.pi := by
  have hmem : ((0, 1), (1, 1)) ∈ fluxEdges 1 := by
    native_decide
  have hidx : fluxIndex 1 ((0, 1), (1, 1)) = 2 := by
    classical
    simp [fluxIndex, fluxEdges, facesExact, shiftFace, shiftPoint, fluxEdge] <;>
      native_decide
  simp [edgeUnitaryWithAxis, hmem, hidx, faceAxis_two]

end EvgenyTheorem
