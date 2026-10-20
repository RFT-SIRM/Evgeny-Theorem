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
