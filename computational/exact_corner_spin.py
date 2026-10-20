"""Exact Gaussian-integer check of same-vertex spin-flip corner entries.

At theta=pi, every SU(2) edge block has Gaussian-integer entries. This
calculator uses exact integer pairs (real, imaginary), not floating point.
It checks physical SG vertex corners only; it is not a Lean proof of the
stronger glued-state/copy-index hypothesis.
"""
from __future__ import annotations

from graph.sg_graph import sg_tree_graph_with_faces

Gaussian = tuple[int, int]
ZERO: Gaussian = (0, 0)
ONE: Gaussian = (1, 0)
NEG_ONE: Gaussian = (-1, 0)
I: Gaussian = (0, 1)
NEG_I: Gaussian = (0, -1)


def _add(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0] + b[0], a[1] + b[1])


def _mul(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def _neg(a: Gaussian) -> Gaussian:
    return (-a[0], -a[1])


def _conj(a: Gaussian) -> Gaussian:
    return (a[0], -a[1])


def _dagger(block: list[list[Gaussian]]) -> list[list[Gaussian]]:
    return [[_conj(block[j][i]) for j in range(2)] for i in range(2)]


def _mat_vec(
    block: list[list[Gaussian]], vector: list[Gaussian]
) -> list[Gaussian]:
    return [
        _add(_mul(block[i][0], vector[0]), _mul(block[i][1], vector[1]))
        for i in range(2)
    ]


def _edge_rotation(axis: int) -> list[list[Gaussian]]:
    # exp(-i*pi/2*sigma_axis) = -i*sigma_axis, exactly.
    rotations = [
        [[ZERO, NEG_I], [NEG_I, ZERO]],
        [[ZERO, NEG_ONE], [ONE, ZERO]],
        [[NEG_I, ZERO], [ZERO, I]],
    ]
    return rotations[axis]


def corner_spin_flip_entries(
    level: int = 3, commuting: bool = False, max_power: int = 5
) -> dict[tuple[tuple[float, float], int, int], Gaussian]:
    """Return exact corner entries (source corner, source spin, power)."""
    vertices, edges, faces = sg_tree_graph_with_faces(level)
    degree = [0] * len(vertices)
    for a, b in edges:
        degree[a] += 1
        degree[b] += 1

    identity = [[ONE, ZERO], [ZERO, ONE]]
    edge_blocks = {tuple(sorted(edge)): identity for edge in edges}
    for face_index, (a, b, _c) in enumerate(faces):
        axis = 2 if commuting else face_index % 3
        edge_blocks[tuple(sorted((a, b)))] = _edge_rotation(axis)

    # Each row entry stores H[x,y], so H is applied to a column vector below.
    rows: list[list[tuple[int, list[list[Gaussian]]]]] = [[] for _ in vertices]
    for vertex, deg in enumerate(degree):
        rows[vertex].append(
            (vertex, [[(deg, 0), ZERO], [ZERO, (deg, 0)]])
        )
    for a, b in edges:
        rotation = edge_blocks[tuple(sorted((a, b)))]
        neg_rotation = [[_neg(x) for x in row] for row in rotation]
        neg_dagger = [[_neg(x) for x in row] for row in _dagger(rotation)]
        rows[a].append((b, neg_rotation))
        rows[b].append((a, neg_dagger))

    corners = ((0.0, 0.0), (1.0, 0.0), (0.0, 1.0))
    corner_indices = [vertices.index(point) for point in corners]
    results: dict[tuple[tuple[float, float], int, int], Gaussian] = {}

    for corner, source in zip(corners, corner_indices):
        for source_spin in (0, 1):
            vector = [[ZERO, ZERO] for _ in vertices]
            vector[source][source_spin] = ONE
            for power in range(1, max_power + 1):
                next_vector = [[ZERO, ZERO] for _ in vertices]
                for x, row in enumerate(rows):
                    total = [ZERO, ZERO]
                    for y, block in row:
                        contribution = _mat_vec(block, vector[y])
                        total[0] = _add(total[0], contribution[0])
                        total[1] = _add(total[1], contribution[1])
                    next_vector[x] = total
                vector = next_vector
                results[(corner, source_spin, power)] = vector[source][1 - source_spin]

    return results
