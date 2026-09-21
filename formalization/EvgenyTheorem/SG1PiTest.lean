import EvgenyTheorem.Operator

namespace EvgenyTheorem

noncomputable section

instance finiteVertexSG1Pi : Finite (Vertex 1) :=
  Finite.of_injective
    (fun v : Vertex 1 => v.1)
    (by
      intro a b h
      exact Subtype.ext h)

instance fintypeVertexSG1Pi : Fintype (Vertex 1) :=
  Fintype.ofFinite (Vertex 1)

example : traceDefect 1 Real.pi = (-32 : ℂ) := by
  norm_num [traceDefect, HC, HCprime, connectionOperatorWithAxis,
    edgeUnitaryWithAxis, axisRotation, su2Rotation, axisPauli,
    fluxIndex, fluxEdges, facesExact, faceAxis, Matrix.trace, Matrix.mul_apply, Finset.sum_apply, Finset.univ]

end
end EvgenyTheorem
