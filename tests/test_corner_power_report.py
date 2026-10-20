"""Regression tests for the corner-power diagnostic output schema.

These tests validate the report's bookkeeping only; they do not assert
universal corner cancellation or replace the Lean proof obligations.
"""
import numpy as np

from computational.corner_power_report import report


def test_corner_report_includes_same_corner_spin_blocks():
    result = report(level=1, theta=float(np.pi / 2), commuting=False, max_power=3)

    assert result["purpose"].startswith("Python vertex-corner diagnostic only")
    assert len(result["powers"]) == 3
    for power_number, power in enumerate(result["powers"], start=1):
        assert power["power"] == power_number
        blocks = power["same_corner_spin_offdiag"]
        assert len(blocks) == 3
        assert [block["corner"] for block in blocks] == [
            [0.0, 0.0], [1.0, 0.0], [0.0, 1.0]
        ]
        for block in blocks:
            value = block["spin_offdiag"]
            assert set(value) == {"re", "im"}
            assert np.isfinite(value["re"])
            assert np.isfinite(value["im"])
            assert np.isfinite(block["spin_offdiag_abs"])
            assert block["spin_offdiag_abs"] >= 0.0


def test_corner_report_has_six_ordered_distinct_corner_blocks_per_power():
    result = report(level=1, theta=0.37, commuting=True, max_power=2)
    for power in result["powers"]:
        assert len(power["corner_blocks"]) == 6
        for block in power["corner_blocks"]:
            assert block["from"] != block["to"]
            assert len(block["entries"]) == 2
            assert all(len(row) == 2 for row in block["entries"])

def test_corner_report_values_match_direct_matrix_powers():
    from graph.sg_graph import sg_tree_graph_with_faces
    from operators.operators import build_su2_bundle

    level, theta, max_power = 2, 0.73, 4
    vertices, _, _ = sg_tree_graph_with_faces(level)
    corners = [(0.0, 0.0), (1.0, 0.0), (0.0, 1.0)]
    indices = [vertices.index(point) for point in corners]
    H, _ = build_su2_bundle(level, theta, commuting=False)
    result = report(level, theta, commuting=False, max_power=max_power)

    direct_power = np.eye(H.shape[0], dtype=complex)
    for p, item in enumerate(result["powers"], start=1):
        direct_power = direct_power @ H
        assert item["power"] == p
        for i, vertex_index in enumerate(indices):
            block = direct_power[
                2 * vertex_index : 2 * vertex_index + 2,
                2 * vertex_index : 2 * vertex_index + 2,
            ]
            recorded = item["same_corner_spin_offdiag"][i]
            assert np.isclose(
                recorded["spin_offdiag"]["re"], block[0, 1].real,
                rtol=1e-11, atol=1e-10,
            )
            assert np.isclose(
                recorded["spin_offdiag"]["im"], block[0, 1].imag,
                rtol=1e-11, atol=1e-10,
            )
            assert np.isclose(
                recorded["spin_offdiag_abs"], abs(block[0, 1]),
                rtol=1e-11, atol=1e-10,
            )

        for block in item["corner_blocks"]:
            i = corners.index(tuple(block["from"]))
            j = corners.index(tuple(block["to"]))
            direct = direct_power[
                2 * indices[i] : 2 * indices[i] + 2,
                2 * indices[j] : 2 * indices[j] + 2,
            ]
            assert np.allclose(
                np.asarray([
                    [complex(value["re"], value["im"]) for value in row]
                    for row in block["entries"]
                ], dtype=complex), direct,
                rtol=1e-11, atol=1e-10,
            )

