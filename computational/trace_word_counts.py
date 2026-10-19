#!/usr/bin/env python3
"""Exact combinatorial counts for ordered words in K and K*N.

This is a bookkeeping/certificate utility only. It does not assert that cyclically
equivalent words have equal matrix contributions unless the trace-cyclicity
hypotheses are separately proved.
"""
from __future__ import annotations

from itertools import product
import json


def canonical_rotation(word: tuple[str, ...]) -> tuple[str, ...]:
    """Lexicographically least cyclic rotation of a nonempty word."""
    return min(word[i:] + word[:i] for i in range(len(word)))


def word_inventory(p: int) -> dict[str, object]:
    if p < 1:
        raise ValueError("word length p must be positive")
    words = list(product(("K", "N"), repeat=p))
    classes: dict[tuple[str, ...], set[tuple[str, ...]]] = {}
    for word in words:
        classes.setdefault(canonical_rotation(word), set()).add(word)

    nonempty_n_classes = [
        representative for representative in classes if "N" in representative
    ]
    by_n_count = {
        str(k): sum(word.count("N") == k for word in words)
        for k in range(p + 1)
    }
    return {
        "p": p,
        "all_words": len(words),
        "words_with_at_least_one_N": len(words) - 1,
        "cyclic_classes": len(classes),
        "cyclic_classes_with_N": len(nonempty_n_classes),
        "words_by_N_count": by_n_count,
    }


def main() -> None:
    result = [word_inventory(p) for p in (6, 8, 10)]
    expected = {
        6: (64, 14, 13),
        8: (256, 36, 35),
        10: (1024, 108, 107),
    }
    for row in result:
        p = int(row["p"])
        actual = (
            row["all_words"],
            row["cyclic_classes"],
            row["cyclic_classes_with_N"],
        )
        assert actual == expected[p], (p, actual, expected[p])
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
