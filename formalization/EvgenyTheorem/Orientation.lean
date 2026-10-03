import EvgenyTheorem.Graph.Faces

namespace EvgenyTheorem

/-- Vertex creation order of `sg_graph.py` (`one_step`), in coordinates scaled by `2^m`:
first occurrences in `A ++ B ++ C`. -/
def vertexOrder : ℕ → List Point
  | 0 => [(0, 0), (1, 0), (0, 1)]
  | m + 1 =>
      let p := vertexOrder m
      let s := 2 ^ m
      (p ++ p.map (shiftPoint s 1 0) ++ p.map (shiftPoint s 0 1)).eraseDups

/-- Python's vertex index: edges are directed from the smaller index. -/
def vIdx (m : ℕ) (p : Point) : ℕ := (vertexOrder m).idxOf p

end EvgenyTheorem
