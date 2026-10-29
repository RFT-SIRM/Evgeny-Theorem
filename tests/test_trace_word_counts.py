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


def test_top_even_stratum_boundary_arithmetic_is_explicitly_conditional():
    """Check conditional top-stratum arithmetic, not the full residual identity.

    Given 12 support states and the stated degree-2 assumptions, the boundary
    expression has p scalar factors of value 2 per state. This test checks
    arithmetic and ledger metadata only; it does not prove those geometric
    premises in Lean or assert that the full p-moment residual vanishes.
    """
    import json
    from pathlib import Path

    expected = {6: 768, 8: 3072, 10: 12288}
    root = Path(__file__).resolve().parents[1]
    log = (root / "formalization" / "HIGHER_MOMENT_RESEARCH_LOG.md").read_text(
        encoding="utf-8"
    )
    ledger = json.loads(
        (root / "computational" / "trace_word_reduction_ledger_p6_p8_p10.json")
        .read_text(encoding="utf-8")
    )
    for p, value in expected.items():
        # There are p scalar factors total: p/2 intervening K factors and
        # p/2 corner-diagonal factors. Under the stated assumptions each
        # equals 2, so one support state contributes 2**p.
        assert 12 * (2**p) == value
        entry = next(row for row in ledger if row["p"] == p)
        top = next(row for row in entry["strata"] if row["kn_factor_count"] == p)
        assert top["word_count"] == 1
        assert top["cyclic_class_count"] == 1
        assert top["reduction_status"] == (
            "explicit_six_N_boundary_formula_under_OAnti"
            if p == 6
            else "explicit_eight_N_boundary_formula_under_OAnti"
            if p == 8
            else "explicit_ten_N_boundary_formula_under_OAnti"
        )
        assert "not a vanishing claim" in log or "not zero" in log


def test_even_pairing_strata_unresolved_word_totals_are_pinned():
    """The remaining even-r strata retain these ordered-word multiplicities."""
    import json
    from pathlib import Path

    expected = {
        6: {2: 15, 4: 15, 6: 1},
        8: {2: 28, 4: 70, 6: 28, 8: 1},
        10: {2: 45, 4: 210, 6: 210, 8: 45, 10: 1},
    }
    root = Path(__file__).resolve().parents[1]
    ledger = json.loads(
        (root / "computational" / "trace_word_reduction_ledger_p6_p8_p10.json")
        .read_text(encoding="utf-8")
    )
    for p, expected_by_r in expected.items():
        entry = next(row for row in ledger if row["p"] == p)
        actual = {
            row["kn_factor_count"]: row["word_count"]
            for row in entry["strata"]
            if row["kn_factor_count"] % 2 == 0 and row["kn_factor_count"] > 0
        }
        assert actual == expected_by_r
        assert sum(actual.values()) == {6: 31, 8: 127, 10: 511}[p]


def test_even_pairing_cyclic_class_counts_are_pinned():
    """Pin class counts separately from ordered-word multiplicities."""
    import json
    from pathlib import Path

    expected = {
        6: {2: (3, 15), 4: (3, 15), 6: (1, 1)},
        8: {2: (4, 28), 4: (10, 70), 6: (4, 28), 8: (1, 1)},
        10: {2: (5, 45), 4: (22, 210), 6: (22, 210), 8: (5, 45), 10: (1, 1)},
    }
    root = Path(__file__).resolve().parents[1]
    ledger = json.loads(
        (root / "computational" / "trace_word_reduction_ledger_p6_p8_p10.json")
        .read_text(encoding="utf-8")
    )
    inventories = json.loads(
        (root / "computational" / "trace_word_inventory_p6_p8_p10.json")
        .read_text(encoding="utf-8")
    )
    for p, expected_by_r in expected.items():
        entry = next(row for row in ledger if row["p"] == p)
        inventory = next(row for row in inventories if row["p"] == p)
        ledger_by_r = {row["kn_factor_count"]: row for row in entry["strata"]}
        for r, (class_count, word_count) in expected_by_r.items():
            classes = [
                row for row in inventory["classes"]
                if row["kn_factor_count"] == r
            ]
            assert len(classes) == class_count
            assert sum(int(row["orbit_size"]) for row in classes) == word_count
            assert ledger_by_r[r]["cyclic_class_count"] == class_count
            assert ledger_by_r[r]["word_count"] == word_count



def test_two_pairing_gap_classes_match_boundary_power_exponents():
    """The r=2 necklace gaps determine the middle power in trace_two_N_powers."""
    expected = {
        6: {
            (0, 4): (1, 5, 6),
            (1, 3): (2, 4, 6),
            (2, 2): (3, 3, 3),
        },
        8: {
            (0, 6): (1, 7, 8),
            (1, 5): (2, 6, 8),
            (2, 4): (3, 5, 8),
            (3, 3): (4, 4, 4),
        },
        10: {
            (0, 8): (1, 9, 10),
            (1, 7): (2, 8, 10),
            (2, 6): (3, 7, 10),
            (3, 5): (4, 6, 10),
            (4, 4): (5, 5, 5),
        },
    }
    for p, expected_rows in expected.items():
        rows = [
            row for row in word_inventory(p)["classes"]
            if row["kn_factor_count"] == 2
        ]
        actual = {}
        for row in rows:
            gaps = tuple(row["cyclic_gap_representative"])
            assert len(gaps) == 2 and sum(gaps) == p - 2
            a, b = (gaps[0] + 1, gaps[1] + 1)
            actual[gaps] = (a, b, row["orbit_size"])
            assert a + b == p
            assert row["representative"].count("K*N") == 2
        assert actual == expected_rows
        assert sum(weight for _a, _b, weight in actual.values()) == p * (p - 1) // 2


def test_gap_composition_inventory_matches_even_stratum_multiplicities():
    from math import comb
    from computational.trace_word_counts import gap_composition_inventory

    expected = {
        (6, 2): (5, 3, 15),
        (6, 4): (10, 3, 15),
        (6, 6): (1, 1, 1),
        (8, 2): (7, 4, 28),
        (8, 4): (35, 10, 70),
        (8, 6): (21, 4, 28),
        (8, 8): (1, 1, 1),
        (10, 2): (9, 5, 45),
        (10, 4): (84, 22, 210),
        (10, 6): (126, 22, 210),
        (10, 8): (36, 5, 45),
        (10, 10): (1, 1, 1),
    }
    for (p, r), (ordered, classes, total) in expected.items():
        got = gap_composition_inventory(p, r)
        assert got["ordered_gap_tuples"] == ordered
        assert got["cyclic_gap_classes"] == classes
        assert got["word_weight_total"] == total == comb(p, r)
        assert all(row["word_orbit_weight"] > 0 for row in got["classes"])


def test_gap_orbit_weights_match_binary_necklace_orbits_class_by_class():
    from computational.trace_word_counts import gap_composition_inventory

    for p in (6, 8, 10):
        words = word_inventory(p)["classes"]
        for r in range(1, p + 1):
            binary_weights = sorted(
                int(row["orbit_size"])
                for row in words
                if int(row["kn_factor_count"]) == r
            )
            gap_weights = sorted(
                int(row["word_orbit_weight"])
                for row in gap_composition_inventory(p, r)["classes"]
            )
            assert gap_weights == binary_weights, (
                f"p={p}, r={r}: gap-orbit weights {gap_weights} "
                f"do not match binary-word orbit weights {binary_weights}"
            )


def test_reversal_gap_inventory_preserves_exact_even_stratum_weights():
    from math import comb
    from computational.trace_word_counts import reversal_gap_inventory

    expected = {
        (6, 2): (3, 15),
        (6, 4): (3, 15),
        (6, 6): (1, 1),
        (8, 2): (4, 28),
        (8, 4): (8, 70),
        (8, 6): (4, 28),
        (8, 8): (1, 1),
        (10, 2): (5, 45),
        (10, 4): (16, 210),
        (10, 6): (16, 210),
        (10, 8): (5, 45),
        (10, 10): (1, 1),
    }
    for (p, r), (classes, total) in expected.items():
        got = reversal_gap_inventory(p, r)
        assert got["reversal_class_count"] == classes
        assert got["word_weight_total"] == total == comb(p, r)
        assert got["cyclic_gap_class_count"] >= got["reversal_class_count"]
        assert all(row["cyclic_class_count"] in (1, 2) for row in got["classes"])


def test_reversal_pairing_report_pins_fixed_and_paired_weights():
    from math import comb
    from computational.trace_word_counts import reversal_gap_pairing_report

    expected = {
        (6, 2): (3, 0, 15, 0),
        (6, 4): (3, 0, 15, 0),
        (6, 6): (1, 0, 1, 0),
        (8, 2): (4, 0, 28, 0),
        (8, 4): (6, 2, 38, 32),
        (8, 6): (4, 0, 28, 0),
        (8, 8): (1, 0, 1, 0),
        (10, 2): (5, 0, 45, 0),
        (10, 4): (10, 6, 90, 120),
        (10, 6): (10, 6, 90, 120),
        (10, 8): (5, 0, 45, 0),
        (10, 10): (1, 0, 1, 0),
    }
    for (p, r), (fixed_n, paired_n, fixed_w, paired_w) in expected.items():
        report = reversal_gap_pairing_report(p, r)
        assert report["fixed_cyclic_class_count"] == fixed_n
        assert report["paired_orbit_count"] == paired_n
        assert report["fixed_word_weight"] == fixed_w
        assert report["paired_word_weight"] == paired_w
        assert report["total_word_weight"] == fixed_w + paired_w == comb(p, r)


def test_full_word_reversal_inventory_preserves_necklace_weights():
    from computational.trace_word_counts import reversal_word_inventory

    expected = {
        6: (14, 13, 64),
        8: (36, 30, 256),
        10: (108, 78, 1024),
    }
    for p, (cyclic_count, reversal_count, total_words) in expected.items():
        report = reversal_word_inventory(p)
        assert report["cyclic_class_count"] == cyclic_count
        assert report["reversal_class_count"] == reversal_count
        assert report["word_weight_total"] == total_words == 2**p
        assert all(
            row["cyclic_class_count"] in (1, 2)
            for row in report["classes"]
        )
        for row in report["classes"]:
            assert row["word_weight"] > 0
            assert row["kn_factor_count"] == sum(
                factor == "K*N" for factor in row["representative"]
            )


def test_full_word_reversal_strata_inventory_matches_binomial_weights():
    from math import comb
    from computational.trace_word_counts import reversal_word_strata_inventory

    expected = {
        6: {
            2: (3, 3, 0, 15, 0),
            3: (4, 3, 1, 8, 12),
            4: (3, 3, 0, 15, 0),
        },
        8: {
            2: (4, 4, 0, 28, 0),
            3: (7, 5, 2, 24, 32),
            4: (10, 8, 2, 38, 32),
            5: (7, 5, 2, 24, 32),
            6: (4, 4, 0, 28, 0),
        },
        10: {
            2: (5, 5, 0, 45, 0),
            3: (12, 8, 4, 40, 80),
            4: (22, 16, 6, 90, 120),
            5: (26, 16, 10, 52, 200),
            6: (22, 16, 6, 90, 120),
            7: (12, 8, 4, 40, 80),
            8: (5, 5, 0, 45, 0),
        },
    }
    for p, strata_expected in expected.items():
        report = reversal_word_strata_inventory(p)
        by_r = {row["kn_factor_count"]: row for row in report["strata"]}
        assert report["word_weight_total"] == 2**p
        for r, (cyclic, reversal, pairs, fixed_weight, paired_weight) in strata_expected.items():
            row = by_r[r]
            assert row["cyclic_class_count"] == cyclic
            assert row["reversal_class_count"] == reversal
            assert row["paired_orbit_count"] == pairs
            assert row["fixed_word_weight"] == fixed_weight
            assert row["paired_word_weight"] == paired_weight
            assert row["word_weight_total"] == comb(p, r)


def test_expanded_operator_word_inventory_preserves_stratum_weights():
    from math import comb
    from computational.trace_word_counts import expanded_operator_word_inventory

    expected_classes = {
        6: {1: 1, 2: 3, 3: 3, 4: 3, 5: 1},
        8: {1: 1, 2: 4, 3: 5, 4: 8, 5: 5, 6: 4, 7: 1},
        10: {1: 1, 2: 5, 3: 8, 4: 16, 5: 16, 6: 16, 7: 8, 8: 5, 9: 1},
    }
    for p, strata_expected in expected_classes.items():
        report = expanded_operator_word_inventory(p)
        assert report["factor_word_count"] == report["expected_factor_word_count"] == 2**p
        by_r = {row["r"]: row for row in report["strata"]}
        for r, class_count in strata_expected.items():
            row = by_r[r]
            assert row["expanded_length"] == p + r
            assert row["expanded_K_count"] == p
            assert row["expanded_N_count"] == r
            assert row["reversal_class_count"] == class_count
            assert row["factor_word_weight"] == comb(p, r)
            assert row["expected_factor_word_count"] == comb(p, r)


def test_adjoint_factor_word_inventory_is_stratumwise_involution():
    from math import comb
    from computational.trace_word_counts import adjoint_factor_word_inventory

    expected = {
        6: {
            0: (1, 1, 0, 1), 1: (1, 1, 0, 6), 2: (3, 3, 0, 15),
            3: (4, 2, 1, 8), 4: (3, 3, 0, 15), 5: (1, 1, 0, 6), 6: (1, 1, 0, 1),
        },
        8: {
            0: (1, 1, 0, 1), 1: (1, 1, 0, 8), 2: (4, 4, 0, 28),
            3: (7, 3, 2, 24), 4: (10, 6, 2, 38), 5: (7, 3, 2, 24),
            6: (4, 4, 0, 28), 7: (1, 1, 0, 8), 8: (1, 1, 0, 1),
        },
        10: {
            0: (1, 1, 0, 1), 1: (1, 1, 0, 10), 2: (5, 5, 0, 45),
            3: (12, 4, 4, 40), 4: (22, 10, 6, 90), 5: (26, 6, 10, 52),
            6: (22, 10, 6, 90), 7: (12, 4, 4, 40), 8: (5, 5, 0, 45),
            9: (1, 1, 0, 10), 10: (1, 1, 0, 1),
        },
    }
    for p, strata_expected in expected.items():
        report = adjoint_factor_word_inventory(p)
        assert report["is_combinatorial_involution"]
        for row in report["strata"]:
            r = row["r"]
            cyclic, fixed_classes, paired_orbits, fixed_weight = strata_expected[r]
            assert row["word_count"] == comb(p, r)
            assert row["image_word_count"] == cyclic
            assert row["cyclic_class_count"] == cyclic
            assert row["fixed_cyclic_class_count"] == fixed_classes
            assert row["paired_orbit_count"] == paired_orbits
            assert row["fixed_word_weight"] == fixed_weight
            assert row["paired_word_weight"] == comb(p, r) - fixed_weight
            assert row["preserves_stratum"]
            assert row["involution_on_cyclic_classes"]
            assert row["fixed_canonical_word_count"] == fixed_weight

def test_p10_eight_pairing_gap_classes_pin_exact_representatives_and_weights():
    """Pin the five r=8 cyclic gap classes before any Lean boundary assembly."""
    from computational.trace_word_counts import gap_composition_inventory

    got = gap_composition_inventory(10, 8)
    actual = {
        tuple(row["gaps"]): int(row["word_orbit_weight"])
        for row in got["classes"]
    }
    expected = {
        (0, 0, 0, 0, 0, 0, 0, 2): 10,
        (0, 0, 0, 0, 0, 0, 1, 1): 10,
        (0, 0, 0, 0, 0, 1, 0, 1): 10,
        (0, 0, 0, 0, 1, 0, 0, 1): 10,
        (0, 0, 0, 1, 0, 0, 0, 1): 5,
    }
    assert actual == expected
    assert got["ordered_gap_tuples"] == 36
    assert got["cyclic_gap_classes"] == 5
    assert got["word_weight_total"] == 45
    assert got["word_weight_total"] == got["expected_word_count"]


def test_p10_six_pairing_gap_classes_pin_distinct_weights():
    """The 111313 class has weight 10; periodic 113113 has weight 5."""
    from computational.trace_word_counts import gap_composition_inventory

    got = gap_composition_inventory(10, 6)
    by_powers = {
        tuple(int(gap) + 1 for gap in row["gaps"]): int(row["word_orbit_weight"])
        for row in got["classes"]
    }
    assert by_powers[(1, 1, 1, 3, 1, 3)] == 10
    assert by_powers[(1, 1, 3, 1, 1, 3)] == 5
    assert by_powers[(1, 1, 1, 3, 2, 2)] == 10
    assert by_powers[(1, 1, 1, 4, 1, 2)] == 10
    assert by_powers[(1, 1, 2, 1, 1, 4)] == 10
    assert got["ordered_gap_tuples"] == 126
    assert got["cyclic_gap_classes"] == 22
    assert got["word_weight_total"] == 210 == got["expected_word_count"]
