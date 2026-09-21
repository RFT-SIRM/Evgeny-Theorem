import EvgenyTheorem.Graph.Faces

namespace EvgenyTheorem

#eval (facesExact 1).length
#eval (fluxEdges 1).length
#eval (fluxIndex 1 (fluxEdges 1).get! 0)
#eval (fluxIndex 1 (fluxEdges 1).get! 1)
#eval (fluxIndex 1 (fluxEdges 1).get! 2)
#eval ((faceAxis 0).val, (faceAxis 1).val, (faceAxis 2).val)

end EvgenyTheorem
