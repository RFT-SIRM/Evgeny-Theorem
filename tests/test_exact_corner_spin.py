from computational.exact_corner_spin import corner_spin_flip_entries


def test_level_three_corner_spin_flip_entries_vanish_exactly_through_power_five():
    for commuting in (False, True):
        entries = corner_spin_flip_entries(
            level=3, commuting=commuting, max_power=5
        )
        assert len(entries) == 3 * 2 * 5
        assert set(entries.values()) == {(0, 0)}


def test_exact_corner_spin_check_preserves_requested_power_range():
    entries = corner_spin_flip_entries(level=3, commuting=False, max_power=3)
    assert len(entries) == 3 * 2 * 3
    assert {power for _, _, power in entries} == {1, 2, 3}
