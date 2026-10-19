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



def test_cyclic_gap_encoding_is_a_bijection_on_necklace_classes():
    for p in (6, 8, 10):
        got = word_inventory(p)
        for k in range(p + 1):
            rows = [row for row in got["classes"] if row["kn_factor_count"] == k]
            gap_reps = [tuple(row["cyclic_gap_representative"]) for row in rows]
            assert len(gap_reps) == len(set(gap_reps))
            assert len(set(gap_reps)) == got["cyclic_gap_classes_by_KN_count"][str(k)]
            assert got["cyclic_gap_classes_by_KN_count"][str(k)] == got["cyclic_classes_by_KN_count"][str(k)]
            for row in rows:
                gaps = row["cyclic_gap_representative"]
                if k == 0:
                    assert gaps == []
                else:
                    assert len(gaps) == k
                    assert sum(gaps) == p - k


def test_cyclic_gap_representative_is_rotation_invariant():
    from computational.trace_word_counts import cyclic_gap_representative

    word = ("K", "K*N", "K", "K*N", "K", "K")
    for i in range(len(word)):
        assert cyclic_gap_representative(word[i:] + word[:i]) == cyclic_gap_representative(word)
    try:
        cyclic_gap_representative(())
    except ValueError as exc:
        assert "nonempty" in str(exc)
    else:
        raise AssertionError("empty words must be rejected")


def test_reduction_ledger_matches_inventory_and_marks_unresolved_strata():
    import json
    from pathlib import Path

    root = Path(__file__).resolve().parents[1]
    ledger = json.loads(
        (root / "computational" / "trace_word_reduction_ledger_p6_p8_p10.json")
        .read_text(encoding="utf-8")
    )
    for entry in ledger:
        p = entry["p"]
        inventory = word_inventory(p)
        assert entry["total_words"] == inventory["all_factor_words"]
        assert entry["total_cyclic_classes"] == inventory["cyclic_classes"]
        assert sum(row["word_count"] for row in entry["strata"]) == entry["total_words"]
        assert sum(row["cyclic_class_count"] for row in entry["strata"]) == entry["total_cyclic_classes"]
        statuses = {row["kn_factor_count"]: row["reduction_status"] for row in entry["strata"]}
        assert statuses[0] == "base_K_power"
        assert statuses[1] == "vanishes_by_existing_one_N_lemma"
        assert statuses[2] == "two_N_formula_with_corner_hypothesis"
        assert all(
            statuses[r] == "not_covered_by_current_generic_reductions"
            for r in range(3, p + 1)
        )
