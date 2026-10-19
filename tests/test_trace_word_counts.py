from computational.trace_word_counts import canonical_rotation, word_inventory


def test_exact_binary_word_and_cyclic_class_counts():
    expected = {
        6: (64, 63, 14, 13),
        8: (256, 255, 36, 35),
        10: (1024, 1023, 108, 107),
    }
    for p, row in expected.items():
        got = word_inventory(p)
        assert (
            got["all_factor_words"],
            got["words_with_at_least_one_KN_factor"],
            got["cyclic_classes"],
            got["cyclic_classes_with_KN_factor"],
        ) == row


def test_word_inventory_preserves_orbit_multiplicities():
    for p in (6, 8, 10):
        got = word_inventory(p)
        assert sum(int(v) for v in got["factor_words_by_KN_count"].values()) == 2**p
        assert got["factor_words_by_KN_count"]["0"] == 1
        assert got["factor_words_by_KN_count"][str(p)] == 1
        assert sum(int(v) for v in got["class_orbit_size_counts"].values()) == got["cyclic_classes"]
        assert sum(int(row["orbit_size"]) for row in got["classes"]) == 2**p
        assert len({tuple(row["representative"]) for row in got["classes"]}) == got["cyclic_classes"]


def test_canonical_rotation_and_reject_empty_word():
    assert canonical_rotation(("K", "K*N", "K")) == ("K", "K", "K*N")
    try:
        canonical_rotation(())
    except ValueError as exc:
        assert "nonempty" in str(exc)
    else:
        raise AssertionError("empty words must be rejected")

def test_committed_inventory_certificate_matches_generator():
    import json
    from pathlib import Path

    certificate_path = (
        Path(__file__).resolve().parents[1]
        / "computational"
        / "trace_word_inventory_p6_p8_p10.json"
    )
    committed = json.loads(certificate_path.read_text(encoding="utf-8"))
    generated = [word_inventory(p) for p in (6, 8, 10)]
    assert committed == generated

