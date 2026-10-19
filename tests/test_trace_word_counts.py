from computational.trace_word_counts import word_inventory


def test_exact_binary_word_and_cyclic_class_counts():
    expected = {
        6: (64, 63, 14, 13),
        8: (256, 255, 36, 35),
        10: (1024, 1023, 108, 107),
    }
    for p, row in expected.items():
        got = word_inventory(p)
        assert (
            got["all_words"],
            got["words_with_at_least_one_N"],
            got["cyclic_classes"],
            got["cyclic_classes_with_N"],
        ) == row


def test_word_inventory_counts_each_N_multiplicity():
    for p in (6, 8, 10):
        got = word_inventory(p)
        assert sum(int(v) for v in got["words_by_N_count"].values()) == 2**p
        assert got["words_by_N_count"]["0"] == 1
        assert got["words_by_N_count"][str(p)] == 1
