import EvgenyTheorem.Operator

namespace EvgenyTheorem

noncomputable section

instance finiteVertexSG1Entry : Finite (Vertex 1) :=
  Finite.of_injective
    (fun v : Vertex 1 => v.1)
    (by
      intro a b h
      exact Subtype.ext h)

instance fintypeVertexSG1Entry : Fintype (Vertex 1) :=
  Fintype.ofFinite (Vertex 1)

def v00 : Vertex 1 := ⟨(0, 0), by decide⟩
def v10 : Vertex 1 := ⟨(1, 0), by decide⟩
def v01 : Vertex 1 := ⟨(0, 1), by decide⟩

example :
    HC 1 Real.pi (v00, (0 : C2)) (v00, (0 : C2)) = 2 := by
  norm_num [HC, connectionOperatorWithAxis, degree]

example :
    HC 1 Real.pi (v00, (0 : C2)) (v10, (0 : C2)) = Complex.I := by
  norm_num [HC, connectionOperatorWithAxis, edgeUnitaryWithAxis,
    axisRotation, su2Rotation, axisPauli, fluxIndex, fluxEdges,
    facesExact, faceAxis]

end
end EvgenyTheorem

example :
    (HC 1 Real.pi ^ 2) (v00, (0 : C2)) (v00, (0 : C2)) = 5 := by
  norm_num [pow_two, Matrix.mul_apply, Finset.sum_apply, HC,
    connectionOperatorWithAxis, edgeUnitaryWithAxis, axisRotation,
    su2Rotation, axisPauli, fluxIndex, fluxEdges, facesExact,
    faceAxis, degree]
