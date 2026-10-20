"""Cross-check Python graph ordering against the Lean recursive definitions.

This test independently encodes the mathematical recursion in integer
coordinates: Lean's vertexOrder/facesExact use coordinates scaled by 2**level.
It checks vertex first-occurrence order, ordered face triples, edge support,
and the face-index-mod-3 axis convention used by the SU(2) builder.
"""
from graph.sg_graph import sg_tree_graph_with_faces


Point = tuple[int, int]
Face = tuple[Point, Point, Point]


def shift(p: Point, s: int, dx: int, dy: int) -> Point:
    return p[0] + dx * s, p[1] + dy * s


def lean_vertex_order(level: int) -> list[Point]:
    points: list[Point] = [(0, 0), (1, 0), (0, 1)]
    for m in range(level):
        s = 2**m
        expanded = (
            points
            + [shift(p, s, 1, 0) for p in points]
            + [shift(p, s, 0, 1) for p in points]
        )
        seen: set[Point] = set()
        points = [p for p in expanded if not (p in seen or seen.add(p))]
    return points


def lean_faces_exact(level: int) -> list[Face]:
    faces: list[Face] = [((0, 0), (1, 0), (0, 1))]
    for m in range(level):
        s = 2**m
        faces = (
            [tuple(shift(p, s, 0, 0) for p in f) for f in faces]
            + [tuple(shift(p, s, 1, 0) for p in f) for f in faces]
            + [tuple(shift(p, s, 0, 1) for p in f) for f in faces]
        )
    return faces


def test_python_vertex_order_matches_lean_recursion():
    for level in range(3):
        vertices, _, _ = sg_tree_graph_with_faces(level)
        scaled_python = [
            (round(x * (2**level)), round(y * (2**level)))
            for x, y in vertices
        ]
        assert scaled_python == lean_vertex_order(level), f"vertex order mismatch at level {level}"


def test_python_ordered_faces_match_lean_faces_exact():
    for level in range(3):
        vertices, _, faces = sg_tree_graph_with_faces(level)
        index = {
            (round(x * (2**level)), round(y * (2**level)): i
            for i, (x, y) in enumerate(vertices)
        }
        expected = [
            tuple(index[p] for p in face)
            for face in lean_faces_exact(level)
        ]
        assert faces == expected, f"ordered faces mismatch at level {level}"


def test_face_flux_edges_and_axes_match_index_convention():
    for level in range(3):
        vertices, edges, faces = sg_tree_graph_with_faces(level)
        edge_set = {tuple(sorted(e)) for e in edges}
        assigned_edges: dict[tuple[int, int], int] = {}
        for i, (a, b, _c) in enumerate(faces):
            edge = tuple(sorted((a, b)))
            assert edge in edge_set, f"face {i} flux edge is not a graph edge"
            assert edge not in assigned_edges, (
                f"flux edge assigned by faces {assigned_edges.get(edge)} and {i}"
            )
            assigned_edges[edge] = i % 3
        assert len(assigned_edges) == 3**level
        assert len(vertices) == (3 ** (level + 1) + 3) // 2
