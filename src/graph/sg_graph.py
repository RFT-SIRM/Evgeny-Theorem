"""
Standard Sierpinski-gasket (SG) combinatorial graph, built by recursive
triangle subdivision (the "tree of triangles" construction used in the
harmonic-analysis-on-fractals literature; Kigami, Strichartz).

This is the graph on which the operators in src/operators are defined.
It is NOT the 6-connected triangular-lattice variant used elsewhere in
this research program to reproduce an external CSV spectrum; that is a
separate, distinct object and is out of scope for this repository.
"""
from typing import List, Tuple

Point = Tuple[float, float]


def sg_tree_graph_with_faces(
    level: int,
) -> Tuple[List[Point], List[Tuple[int, int]], List[Tuple[int, int, int]]]:
    """
    Build the level-`level` SG approximation graph.

    Returns
    -------
    V : list of (x, y) vertex coordinates
    E : list of (i, j) undirected edges (i < j), as vertex-index pairs
    faces : list of (a, b, c) vertex-index triples, one per elementary
            (leaf) triangle, in a fixed traversal order. Elementary
            triangles have pairwise-disjoint edge sets in this graph.

    Known closed-form checks (used in tests/test_levels.py):
        n_vertices(level) = (3**(level+1) + 3) // 2
        n_edges(level)    = 3**(level+1)
        n_faces(level)    = 3**level
    """
    V0: List[Point] = [(0.0, 0.0), (1.0, 0.0), (0.0, 1.0)]
    E0: List[Tuple[int, int]] = [(0, 1), (1, 2), (0, 2)]

    def one_step(V, E, faces_prev):
        offsets = [(0.0, 0.0), (0.5, 0.0), (0.0, 0.5)]
        new_V: List[Point] = []
        vertex_index = {}
        new_E = set()
        maps = []

        for ox, oy in offsets:
            m = {}
            for i, (x, y) in enumerate(V):
                p = (round(x * 0.5 + ox, 10), round(y * 0.5 + oy, 10))
                if p not in vertex_index:
                    vertex_index[p] = len(new_V)
                    new_V.append(p)
                m[i] = vertex_index[p]
            maps.append(m)

        new_faces = []
        for m in maps:
            for a, b in E:
                new_E.add(tuple(sorted((m[a], m[b]))))
            if faces_prev is not None:
                for f in faces_prev:
                    new_faces.append(tuple(m[v] for v in f))
            else:
                new_faces.append((m[0], m[1], m[2]))

        return new_V, list(new_E), new_faces

    V, E, faces = V0, E0, None
    for _ in range(level):
        V, E, faces = one_step(V, E, faces)

    return V, E, faces


def expected_counts(level: int) -> Tuple[int, int, int]:
    """Closed-form (n_vertices, n_edges, n_faces) for the standard SG graph."""
    n_vertices = (3 ** (level + 1) + 3) // 2
    n_edges = 3 ** (level + 1)
    n_faces = 3 ** level
    return n_vertices, n_edges, n_faces
