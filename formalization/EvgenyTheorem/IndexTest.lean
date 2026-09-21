import EvgenyTheorem.Operator

namespace EvgenyTheorem

theorem fluxIndex_face0 :
    fluxIndex 1 ((fluxEdges 1).get ⟨0, by simp [fluxEdges, facesExact]⟩) = 0 := by
  classical
  simp [fluxIndex, fluxEdges, facesExact, List.findIdx, shiftFace, shiftPoint, fluxEdge] <;> decide

theorem fluxIndex_face1 :
    fluxIndex 1 ((fluxEdges 1).get ⟨1, by simp [fluxEdges, facesExact]⟩) = 1 := by
  classical
  simp [fluxIndex, fluxEdges, facesExact, List.findIdx, shiftFace, shiftPoint, fluxEdge] <;> decide

theorem fluxIndex_face2 :
    fluxIndex 1 ((fluxEdges 1).get ⟨2, by simp [fluxEdges, facesExact]⟩) = 2 := by
  classical
  simp [fluxIndex, fluxEdges, facesExact, List.findIdx, shiftFace, shiftPoint, fluxEdge] <;> decide

end EvgenyTheorem
