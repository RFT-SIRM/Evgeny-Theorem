import EvgenyTheorem.Locality

namespace EvgenyTheorem

theorem fluxEdges_one :
    fluxEdges 1 = [((0, 0), (1, 0)), ((1, 0), (2, 0)), ((0, 1), (1, 1))] := by
  first
    | decide
    | rfl
    | simp [fluxEdges, facesExact, fluxEdge, shiftFace, shiftPoint]

theorem fluxIndex_one_0 : fluxIndex 1 ((0, 0), (1, 0)) = 0 := by
  first | decide | rfl | simp [fluxIndex, fluxEdges_one]

theorem fluxIndex_one_1 : fluxIndex 1 ((1, 0), (2, 0)) = 1 := by
  first | decide | rfl | simp [fluxIndex, fluxEdges_one]

theorem fluxIndex_one_2 : fluxIndex 1 ((0, 1), (1, 1)) = 2 := by
  first | decide | rfl | simp [fluxIndex, fluxEdges_one]

theorem edgeAxis_one_0 : edgeAxis 1 ((0, 0), (1, 0)) = 0 := by
  first | decide | rfl | simp [edgeAxis, fluxIndex_one_0, faceAxis_zero]

theorem edgeAxis_one_1 : edgeAxis 1 ((1, 0), (2, 0)) = 1 := by
  first | decide | rfl | simp [edgeAxis, fluxIndex_one_1, faceAxis_one]

theorem edgeAxis_one_2 : edgeAxis 1 ((0, 1), (1, 1)) = 2 := by
  first | decide | rfl | simp [edgeAxis, fluxIndex_one_2, faceAxis_two]

def v00 : Vertex 1 := ⟨(0, 0), by decide⟩
def v10 : Vertex 1 := ⟨(1, 0), by decide⟩
def v20 : Vertex 1 := ⟨(2, 0), by decide⟩
def v01 : Vertex 1 := ⟨(0, 1), by decide⟩
def v11 : Vertex 1 := ⟨(1, 1), by decide⟩
def v02 : Vertex 1 := ⟨(0, 2), by decide⟩

theorem univ_one :
    (Finset.univ : Finset (Vertex 1)) = {v00, v10, v20, v01, v11, v02} := by
  decide

end EvgenyTheorem
