from computational.trace_word_counts import (
    canonical_rotation,
    cyclic_gap_representative,
    word_inventory,
)


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
        assert statuses[3] == "vanishes_by_three_N_corner_lemma_under_OAnti"
        assert statuses[4] == "explicit_four_N_boundary_formula_under_OAnti"
        assert statuses[5] == "vanishes_by_five_N_corner_lemma_under_OAnti"
        assert statuses[6] == "explicit_six_N_boundary_formula_under_OAnti"
        if p >= 8:
            assert statuses[7] == "vanishes_by_seven_N_corner_lemma_under_OAnti"
        if p >= 8:
            assert statuses[8] == "explicit_eight_N_boundary_formula_under_OAnti"
        if p == 10:
            assert statuses[9] == "vanishes_by_nine_N_corner_lemma_under_OAnti"
            assert statuses[10] == "explicit_ten_N_boundary_formula_under_OAnti"
        for row in entry["strata"]:
            r = row["kn_factor_count"]
            inventory_rows = [
                item for item in inventory["classes"]
                if item["kn_factor_count"] == r
            ]
            assert len(inventory_rows) == row["cyclic_class_count"]
            assert sum(int(item["orbit_size"]) for item in inventory_rows) == row["word_count"]
            if r == 6:
                note = row["reduction_note"]
                assert "trace_six_N_powers_boundary" in note
                assert "does not prove cancellation or vanishing" in note
                assert "Do not infer the p-moment identity" in note
            if r == 7:
                note = row["reduction_note"]
                assert "trace_seven_N_powers_zero" in note
                assert "conditional vanishing of the r=7 stratum" in note
                assert "do not infer the all-level p-moment identity" in note
            if r == 8:
                note = row["reduction_note"]
                assert "trace_eight_N_powers_boundary" in note
                assert "not a vanishing claim" in note
                assert "Do not infer the p-moment identity" in note
            if r == 9:
                note = row["reduction_note"]
                assert "trace_nine_N_powers_zero" in note
                assert "conditional vanishing of the r=9 stratum" in note
                assert "Do not infer the all-level p-moment identity" in note
            if r == 10:
                note = row["reduction_note"]
                assert "trace_ten_N_powers_boundary" in note
                assert "not a vanishing claim" in note
                assert "Do not infer the p-moment identity" in note

def test_three_pairing_classes_split_by_unit_gap_and_positive_gap_cases():
    """A zero K-gap means a K**N factor pair with middle power K^1."""
    # The positive-gap tuples were formerly unresolved; the conditional Lean
    # corner lemma now covers them after cyclic rotation.
    expected = {
        6: (3, [(1, 1, 1)]),
        8: (5, [(1, 1, 3), (1, 2, 2)]),
        10: (7, [(1, 1, 5), (1, 4, 2), (1, 2, 4), (1, 3, 3), (2, 2, 3)]),
    }
    for p, (covered_count, positive_gap_classes) in expected.items():
        rows = [
            row for row in word_inventory(p)["classes"]
            if row["kn_factor_count"] == 3
        ]
        covered = [
            row for row in rows
            if 0 in row["cyclic_gap_representative"]
        ]
        positive_gap = sorted(
            tuple(row["cyclic_gap_representative"])
            for row in rows
            if 0 not in row["cyclic_gap_representative"]
        )
        assert len(covered) == covered_count
        assert positive_gap == sorted(positive_gap_classes)
        assert len(covered) + len(positive_gap) == len(rows)

def test_three_pairing_gap_tuple_maps_to_middle_power_and_orbit_multiplicity():
    """Each K*N contributes its own leading K, so power exponents are gap + 1."""
    expected = {
        6: {
            (1, 1, 1): (2, 2, 2, 2),
        },
        8: {
            (1, 1, 3): (2, 2, 4, 8),
            (1, 2, 2): (2, 3, 3, 8),
        },
        10: {
            (1, 1, 5): (2, 2, 6, 10),
            (1, 4, 2): (2, 5, 3, 10),
            (1, 2, 4): (2, 3, 5, 10),
            (1, 3, 3): (2, 4, 4, 10),
            (2, 2, 3): (3, 3, 4, 10),
        },
    }
    for p, classes in expected.items():
        rows = [
            row for row in word_inventory(p)["classes"]
            if row["kn_factor_count"] == 3
        ]
        by_gap = {
            tuple(row["cyclic_gap_representative"]): row
            for row in rows
        }
        for gaps, (a, b, c, orbit_size) in classes.items():
            row = by_gap[gaps]
            representative = tuple(row["representative"])
            # Tie each gap class to the actual ordered word representative,
            # not only to a tuple generated by the inventory.
            assert canonical_rotation(representative) == representative
            assert cyclic_gap_representative(representative) == gaps
            assert representative.count("K*N") == 3
            assert (gaps[0] + 1, gaps[1] + 1, gaps[2] + 1) == (a, b, c)
            assert row["orbit_size"] == orbit_size
            assert len(row["representative"]) == p
            assert row["representative"].count("K*N") == 3
            # The corner lemma is available for n < 2**m. Every middle
            # power required by these unresolved classes is at most 6,
            # so the geometric bound is valid already at the smallest
            # relevant level m = 3.
            assert max(a, b, c) <= 6
            assert max(a, b, c) < 2**3
        assert sum(by_gap[g]["orbit_size"] for g in classes) == sum(
            value[3] for value in classes.values()
        )


def test_three_pairing_stratum_is_covered_by_conditional_lean_corner_lemma():
    """The smallest cyclic gap can be placed in the middle by rotation."""
    for p in (6, 8, 10):
        rows = [
            row for row in word_inventory(p)["classes"]
            if row["kn_factor_count"] == 3
        ]
        assert rows
        for row in rows:
            gaps = row["cyclic_gap_representative"]
            assert len(gaps) == 3
            assert sum(gaps) == p - 3
            middle_exponent = min(gaps) + 1
            assert middle_exponent <= 3
            assert middle_exponent < 2**3


def test_four_pairing_stratum_fits_explicit_boundary_formula_bounds():
    """For p<=10 and m>=3, every four-N cyclic word has admissible b,d."""
    for p in (6, 8, 10):
        rows = [
            row for row in word_inventory(p)["classes"]
            if row["kn_factor_count"] == 4
        ]
        for row in rows:
            gaps = row["cyclic_gap_representative"]
            assert len(gaps) == 4
            assert sum(gaps) == p - 4
            exponents = [gap + 1 for gap in gaps]
            assert all(1 <= exponent <= p - 3 for exponent in exponents)
            # The explicit Lean theorem needs two selected exponents below 2**m;
            # here all four satisfy this for the minimal relevant m=3.
            assert all(exponent < 2**3 for exponent in exponents)
            assert row["representative"].count("K*N") == 4


def test_five_pairing_words_have_two_admissible_middle_power_bounds():
    """For p<=10, any two gap exponents in the five-N stratum are < 2**3."""
    for p in (6, 8, 10):
        rows = [
            row for row in word_inventory(p)["classes"]
            if row["kn_factor_count"] == 5
        ]
        for row in rows:
            gaps = row["cyclic_gap_representative"]
            assert len(gaps) == 5
            assert sum(gaps) == p - 5
            exponents = [gap + 1 for gap in gaps]
            assert all(1 <= exponent <= p - 4 for exponent in exponents)
            assert sum(exponent < 2**3 for exponent in exponents) == 5
            assert row["representative"].count("K*N") == 5
        # Preserve the ordered-word orbit multiplicities when classifying
        # the complete r=5 stratum, not just its canonical representatives.
        assert sum(row["orbit_size"] for row in rows) == {
            6: 6, 8: 56, 10: 252
        }[p]


def test_unresolved_high_pairing_strata_keep_exact_gap_classes_and_orbit_weights():
    """Keep unresolved r>=6 classes tied to ordered representatives and multiplicities."""
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
        for stratum in entry["strata"]:
            r = stratum["kn_factor_count"]
            if r < 6:
                continue
            rows = [
                row for row in inventory["classes"]
                if row["kn_factor_count"] == r
            ]
            assert len(rows) == stratum["cyclic_class_count"]
            assert sum(int(row["orbit_size"]) for row in rows) == stratum["word_count"]
            for row in rows:
                representative = tuple(row["representative"])
                gaps = tuple(row["cyclic_gap_representative"])
                assert len(representative) == p
                assert canonical_rotation(representative) == representative
                assert representative.count("K*N") == r
                assert cyclic_gap_representative(representative) == gaps
                assert len(gaps) == r
                assert sum(gaps) == p - r
                assert row["orbit_size"] > 0


def test_full_ledger_strata_match_binomial_word_counts_and_total_expansion():
    """Every r-stratum must account for exactly binomial(p, r) ordered words."""
    import json
    from math import comb
    from pathlib import Path

    root = Path(__file__).resolve().parents[1]
    ledger = json.loads(
        (root / "computational" / "trace_word_reduction_ledger_p6_p8_p10.json")
        .read_text(encoding="utf-8")
    )
    for entry in ledger:
        p = entry["p"]
        inventory = word_inventory(p)
        assert inventory["all_factor_words"] == 2**p
        assert sum(int(row["orbit_size"]) for row in inventory["classes"]) == 2**p
        strata = {row["kn_factor_count"]: row for row in entry["strata"]}
        assert set(strata) == set(range(p + 1))
        for r in range(p + 1):
            class_rows = [
                row for row in inventory["classes"]
                if row["kn_factor_count"] == r
            ]
            assert len(class_rows) == strata[r]["cyclic_class_count"]
            assert sum(int(row["orbit_size"]) for row in class_rows) == comb(p, r)
            assert strata[r]["word_count"] == comb(p, r)
        assert sum(row["word_count"] for row in entry["strata"]) == 2**p
        assert sum(row["cyclic_class_count"] for row in entry["strata"]) == (
            inventory["cyclic_classes"]
        )


def test_six_pairing_stratum_has_explicit_conditional_boundary_formula():
    """Six N factors have a formula, not an asserted cancellation."""
    import json
    from pathlib import Path

    root = Path(__file__).resolve().parents[1]
    ledger = json.loads(
        (root / "computational" / "trace_word_reduction_ledger_p6_p8_p10.json")
        .read_text(encoding="utf-8")
    )
    expected = {6: (1, 1), 8: (28, 4), 10: (210, 22)}
    for entry in ledger:
        p = entry["p"]
        row = next(s for s in entry["strata"] if s["kn_factor_count"] == 6)
        assert (row["word_count"], row["cyclic_class_count"]) == expected[p]
        assert row["reduction_status"] == "explicit_six_N_boundary_formula_under_OAnti"
        assert "does not prove cancellation or vanishing" in row["reduction_note"]
        rows = [x for x in word_inventory(p)["classes"] if x["kn_factor_count"] == 6]
        assert len(rows) == row["cyclic_class_count"]
        assert sum(int(x["orbit_size"]) for x in rows) == row["word_count"]
        for item in rows:
            exponents = [gap + 1 for gap in item["cyclic_gap_representative"]]
            assert len(exponents) == 6
            assert max(exponents) <= 5
            assert max(exponents) < 2**3


def test_seven_pairing_stratum_has_conditional_vanishing_reduction():
    """The seven-N trace reduction is conditional and preserves orbit weights."""
    import json
    from pathlib import Path

    root = Path(__file__).resolve().parents[1]
    ledger = json.loads(
        (root / "computational" / "trace_word_reduction_ledger_p6_p8_p10.json")
        .read_text(encoding="utf-8")
    )
    expected = {8: (8, 1), 10: (120, 12)}
    for entry in ledger:
        p = entry["p"]
        if p < 7:
            continue
        row = next(s for s in entry["strata"] if s["kn_factor_count"] == 7)
        assert (row["word_count"], row["cyclic_class_count"]) == expected[p]
        assert row["reduction_status"] == "vanishes_by_seven_N_corner_lemma_under_OAnti"
        rows = [x for x in word_inventory(p)["classes"] if x["kn_factor_count"] == 7]
        assert len(rows) == row["cyclic_class_count"]
        assert sum(int(x["orbit_size"]) for x in rows) == row["word_count"]
        for item in rows:
            exponents = [gap + 1 for gap in item["cyclic_gap_representative"]]
            assert len(exponents) == 7
            assert max(exponents) <= 4
            assert max(exponents) < 2**3


def test_eight_to_ten_pairing_strata_have_explicit_conditional_reductions():
    """Check exact word weights without overstating boundary formulas."""
    import json
    from pathlib import Path

    root = Path(__file__).resolve().parents[1]
    ledger = json.loads(
        (root / "computational" / "trace_word_reduction_ledger_p6_p8_p10.json")
        .read_text(encoding="utf-8")
    )
    expected = {
        (8, 8): (1, 1, "explicit_eight_N_boundary_formula_under_OAnti"),
        (10, 8): (45, 5, "explicit_eight_N_boundary_formula_under_OAnti"),
        (10, 9): (10, 1, "vanishes_by_nine_N_corner_lemma_under_OAnti"),
        (10, 10): (1, 1, "explicit_ten_N_boundary_formula_under_OAnti"),
    }
    for entry in ledger:
        p = entry["p"]
        inventory = word_inventory(p)
        for row in entry["strata"]:
            r = row["kn_factor_count"]
            if (p, r) not in expected:
                continue
            words, classes, status = expected[(p, r)]
            assert (row["word_count"], row["cyclic_class_count"]) == (words, classes)
            assert row["reduction_status"] == status
            rows = [x for x in inventory["classes"] if x["kn_factor_count"] == r]
            assert len(rows) == classes
            assert sum(int(x["orbit_size"]) for x in rows) == words
            for item in rows:
                exponents = [gap + 1 for gap in item["cyclic_gap_representative"]]
                assert len(exponents) == r
                assert max(exponents) <= p-r+1
                assert max(exponents) < 2**3


def test_r3_ledger_records_conditional_corner_proof_not_block_diagonality_guess():
    """All r=3 classes are conditionally covered by the formal all-power corner lemma."""
    import json
    from pathlib import Path

    root = Path(__file__).resolve().parents[1]
    ledger = json.loads(
        (root / "computational" / "trace_word_reduction_ledger_p6_p8_p10.json")
        .read_text(encoding="utf-8")
    )
    for entry in ledger:
        row = next(s for s in entry["strata"] if s["kn_factor_count"] == 3)
        assert row["reduction_status"] == "vanishes_by_three_N_corner_lemma_under_OAnti"
        note = row["reduction_note"]
        assert "OAnti (m + 1) o" in note
        assert "sgK_pow_GlueDiag_of_OAnti" in note
        assert "every natural power" in note or "block diagonality alone" in note
        p = entry["p"]
        rows = [x for x in word_inventory(p)["classes"] if x["kn_factor_count"] == 3]
        for item in rows:
            gaps = item["cyclic_gap_representative"]
            assert len(gaps) == 3 and sum(gaps) == p - 3
            assert min(gaps) + 1 <= 3 < 2**3


def test_even_pairing_boundary_strata_are_not_mislabeled_as_zero():
    """Boundary reduction is not a proof of cancellation for even r strata."""
    import json
    from pathlib import Path

    root = Path(__file__).resolve().parents[1]
    ledger = json.loads(
        (root / "computational" / "trace_word_reduction_ledger_p6_p8_p10.json")
        .read_text(encoding="utf-8")
    )
    expected_status = {
        6: "explicit_six_N_boundary_formula_under_OAnti",
        8: "explicit_eight_N_boundary_formula_under_OAnti",
        10: "explicit_ten_N_boundary_formula_under_OAnti",
    }
    for entry in ledger:
        for r, status in expected_status.items():
            if r > entry["p"]:
                continue
            row = next(s for s in entry["strata"] if s["kn_factor_count"] == r)
            assert row["reduction_status"] == status
            note = row["reduction_note"]
            assert (
                "does not prove cancellation" in note
                or "not a vanishing claim" in note
            )
            inventory_rows = [
                x for x in word_inventory(entry["p"])["classes"]
                if x["kn_factor_count"] == r
            ]
            assert len(inventory_rows) == row["cyclic_class_count"]
            assert sum(int(x["orbit_size"]) for x in inventory_rows) == row["word_count"]
