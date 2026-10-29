#!/usr/bin/env python3
"""Exact finite-level trace-defect regression at theta=pi.

All matrix entries are Gaussian integers, represented as pairs of Python
integers. Sparse row dictionaries therefore perform every multiplication and
addition exactly; no floating-point arithmetic is used. This is a finite
certificate, not an all-level proof.
"""
from __future__ import annotations

from graph.sg_graph import sg_tree_graph_with_faces

Gaussian = tuple[int, int]
ZERO: Gaussian = (0, 0)
ONE: Gaussian = (1, 0)


def add(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0] + b[0], a[1] + b[1])


def neg(a: Gaussian) -> Gaussian:
    return (-a[0], -a[1])


def mul(a: Gaussian, b: Gaussian) -> Gaussian:
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0])


def dagger2(u: tuple[tuple[Gaussian, Gaussian],
                     tuple[Gaussian, Gaussian]]):
    return (( (u[0][0][0], -u[0][0][1]),
              (u[1][0][0], -u[1][0][1]) ),
            ( (u[0][1][0], -u[0][1][1]),
              (u[1][1][0], -u[1][1][1]) ))


def edge_rotation(axis: int):
    """Return -i sigma_axis as a 2x2 Gaussian-integer matrix."""
    if axis == 0:
        return ((ZERO, (0, -1)), ((0, -1), ZERO))
    if axis == 1:
        return ((ZERO, (-1, 0)), (ONE, ZERO))
    return (((0, -1), ZERO), (ZERO, (0, 1)))


def operator_at_pi(level: int, commuting: bool) -> list[dict[int, Gaussian]]:
    """Build the exact sparse 2|V| by 2|V| operator."""
    vertices, edges, faces = sg_tree_graph_with_faces(level)
    n = len(vertices)
    degree = [0] * n
    for a, b in edges:
        degree[a] += 1
        degree[b] += 1

    rotations = {tuple(sorted(e)): ((ONE, ZERO), (ZERO, ONE)) for e in edges}
    for i, (a, b, _c) in enumerate(faces):
        rotations[tuple(sorted((a, b)))] = edge_rotation(2 if commuting else i % 3)

    size = 2 * n
    rows: list[dict[int, Gaussian]] = [dict() for _ in range(size)]

    def put(r: int, c: int, z: Gaussian) -> None:
        if z == ZERO:
            return
        value = add(rows[r].get(c, ZERO), z)
        if value == ZERO:
            rows[r].pop(c, None)
        else:
            rows[r][c] = value

    for v, d in enumerate(degree):
        put(2 * v, 2 * v, (d, 0))
        put(2 * v + 1, 2 * v + 1, (d, 0))

    for a, b in edges:
        a, b = sorted((a, b))
        u = rotations[(a, b)]
        # H_ab = -U; H_ba = -U^*.
        for i in range(2):
            for j in range(2):
                put(2 * a + i, 2 * b + j, neg(u[i][j]))
                z = u[j][i]
                put(2 * b + i, 2 * a + j, (-z[0], z[1]))
    return rows


def sparse_product(a: list[dict[int, Gaussian]],
                   b: list[dict[int, Gaussian]]) -> list[dict[int, Gaussian]]:
    """Exact sparse matrix product over Z[i]."""
    out: list[dict[int, Gaussian]] = []
    for row in a:
        accum: dict[int, Gaussian] = {}
        for k, x in row.items():
            for j, y in b[k].items():
                z = mul(x, y)
                value = add(accum.get(j, ZERO), z)
                if value == ZERO:
                    accum.pop(j, None)
                else:
                    accum[j] = value
        out.append(accum)
    return out


def raw_trace_at_pi(level: int, power: int, commuting: bool) -> int:
    """Return Tr(H^power) using exact Gaussian-integer sparse arithmetic."""
    if power < 1:
        raise ValueError("power must be positive")
    h = operator_at_pi(level, commuting)
    hp = h
    for _ in range(1, power):
        hp = sparse_product(hp, h)
    real = 0
    imag = 0
    for i, row in enumerate(hp):
        z = row.get(i, ZERO)
        real += z[0]
        imag += z[1]
    if imag != 0:
        raise ArithmeticError(
            f"trace has nonzero imaginary part at level={level}, p={power}: {imag}"
        )
    return real


def delta_at_pi(level: int, power: int) -> int:
    return raw_trace_at_pi(level, power, False) - raw_trace_at_pi(level, power, True)


def residual_at_pi(level: int, power: int) -> int:
    if level < 2:
        raise ValueError("residual requires level >= 2")
    return delta_at_pi(level, power) - 3 * delta_at_pi(level - 1, power)


def certificate() -> dict[int, dict[str, list[int]]]:
    """Exact finite-level regression for p=6,8,10 and levels 1..6."""
    result = {}
    for p in (6, 8, 10):
        deltas = [delta_at_pi(m, p) for m in range(1, 7)]
        residuals = [deltas[m - 1] - 3 * deltas[m - 2] for m in range(2, 7)]
        result[p] = {
            "delta_levels_1_to_6": deltas,
            "residual_levels_2_to_6": residuals,
        }
    return result


if __name__ == "__main__":
    import json
    print(json.dumps(certificate(), indent=2))
