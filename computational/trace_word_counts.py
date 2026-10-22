#!/usr/bin/env python3
"""Exact cyclic-class inventory for factor choices K and K*N.

Each position chooses one factor, either K or K*N. Rotating the factor
sequence preserves the trace by cyclicity, when the matrix dimensions match.
This utility only counts the combinatorics; it does not prove any matrix
term vanishes or that distinct classes have equal contributions.
"""
from __future__ import annotations

from itertools import product
from math import comb
import json

FACTOR_CHOICES = ("K", "K*N")


def canonical_rotation(word: tuple[str, ...]) -> tuple[str, ...]:
    """Return the lexicographically least cyclic rotation of a nonempty word."""
    if not word:
        raise ValueError("word must be nonempty")
    return min(word[i:] + word[:i] for i in range(len(word)))


def cyclic_gap_representative(word: tuple[str, ...]) -> tuple[int, ...]:
    """Encode a cyclic word by K-gap lengths between successive K*N factors."""
    if not word:
        raise ValueError("word must be nonempty")
    marked = [i for i, factor in enumerate(word) if factor == "K*N"]
    if not marked:
        return ()
    n = len(word)
    gaps = tuple((marked[(j + 1) % len(marked)] - pos - 1) % n for j, pos in enumerate(marked))
    return min(gaps[i:] + gaps[:i] for i in range(len(gaps)))


def word_inventory(p: int) -> dict[str, object]:
    """Count factor-choice words and cyclic classes, retaining representatives."""
    if p < 1:
        raise ValueError("word length p must be positive")
    words = list(product(FACTOR_CHOICES, repeat=p))
    classes: dict[tuple[str, ...], set[tuple[str, ...]]] = {}
    for word in words:
        classes.setdefault(canonical_rotation(word), set()).add(word)

    class_rows = [
        {
            "representative": list(rep),
            "kn_factor_count": rep.count("K*N"),
            "orbit_size": len(members),
            "cyclic_gap_representative": list(cyclic_gap_representative(rep)),
        }
        for rep, members in sorted(classes.items())
    ]
    classes_with_kn = [row for row in class_rows if row["kn_factor_count"] > 0]
    by_kn_count = {
        str(k): sum(word.count("K*N") == k for word in words)
        for k in range(p + 1)
    }
    class_counts_by_kn = {
        str(k): sum(row["kn_factor_count"] == k for row in class_rows)
        for k in range(p + 1)
    }
    gap_classes_by_kn_count = {
        str(k): len({tuple(row["cyclic_gap_representative"]) for row in class_rows if row["kn_factor_count"] == k})
        for k in range(p + 1)
    }
    orbit_size_counts = {
        str(size): sum(row["orbit_size"] == size for row in class_rows)
        for size in sorted({int(row["orbit_size"]) for row in class_rows})
    }
    return {
        "p": p,
        "all_factor_words": len(words),
        "words_with_at_least_one_KN_factor": len(words) - 1,
        "cyclic_classes": len(class_rows),
        "cyclic_classes_with_KN_factor": len(classes_with_kn),
        "factor_words_by_KN_count": by_kn_count,
        "cyclic_classes_by_KN_count": class_counts_by_kn,
        "cyclic_gap_classes_by_KN_count": gap_classes_by_kn_count,
        "class_orbit_size_counts": orbit_size_counts,
        "classes": class_rows,
    }


def main() -> None:
    result = [word_inventory(p) for p in (6, 8, 10)]
    expected = {6: (64, 14, 13), 8: (256, 36, 35), 10: (1024, 108, 107)}
    for row in result:
        p = int(row["p"])
        actual = (
            row["all_factor_words"],
            row["cyclic_classes"],
            row["cyclic_classes_with_KN_factor"],
        )
        assert actual == expected[p], (p, actual, expected[p])
        assert sum(int(v) for v in row["factor_words_by_KN_count"].values()) == 2**p
        assert sum(int(v) for v in row["class_orbit_size_counts"].values()) == row["cyclic_classes"]
        assert sum(int(r["orbit_size"]) for r in row["classes"]) == 2**p

        # Check the multiplicity identity stratum by stratum, not only globally:
        # each cyclic class contributes its number of distinct rotations, so
        # periodic words are weighted correctly rather than by a blanket factor p.
        for r in range(p + 1):
            classes_r = [
                item for item in row["classes"]
                if int(item["kn_factor_count"]) == r
            ]
            weighted_count = sum(int(item["orbit_size"]) for item in classes_r)
            assert weighted_count == comb(p, r), (
                f"p={p}, r={r}: orbit-weighted count {weighted_count} "
                f"does not equal binomial({p}, {r})={comb(p, r)}"
            )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()


def weak_compositions(total: int, parts: int) -> list[tuple[int, ...]]:
    """Return all ordered weak compositions of total into a positive parts count."""
    if total < 0 or parts < 1:
        raise ValueError("total must be nonnegative and parts must be positive")
    if parts == 1:
        return [(total,)]
    out: list[tuple[int, ...]] = []
    for first in range(total + 1):
        out.extend((first,) + rest for rest in weak_compositions(total - first, parts - 1))
    return out


def gap_composition_inventory(p: int, r: int) -> dict[str, object]:
    """Index r-marked cyclic words by ordered K-gaps, with exact rotation weights."""
    if not (1 <= r <= p):
        raise ValueError("require 1 <= r <= p")
    gaps = weak_compositions(p - r, r)
    canonical = lambda g: min(g[i:] + g[:i] for i in range(r))
    classes: dict[tuple[int, ...], set[tuple[int, ...]]] = {}
    for g in gaps:
        classes.setdefault(canonical(g), set()).add(g)
    rows = [
        {"gaps": list(rep), "gap_orbit_size": len(members),
         "word_orbit_weight": (p * len(members)) // r}
        for rep, members in sorted(classes.items())
    ]
    return {
        "p": p,
        "r": r,
        "ordered_gap_tuples": len(gaps),
        "cyclic_gap_classes": len(rows),
        "word_weight_total": sum(int(row["word_orbit_weight"]) for row in rows),
        "expected_word_count": comb(p, r),
        "classes": rows,
    }


def reversal_gap_inventory(p: int, r: int) -> dict[str, object]:
    """Group cyclic gap classes with their reversals as a candidate symmetry quotient.

    This is combinatorial bookkeeping only. It does not assert that the corresponding
    matrix traces are equal; that requires a separate algebraic argument.
    """
    inventory = gap_composition_inventory(p, r)
    rows = inventory["classes"]
    grouped: dict[tuple[int, ...], list[dict[str, object]]] = {}
    for row in rows:
        gaps = tuple(int(x) for x in row["gaps"])
        reverse = tuple(reversed(gaps))
        reverse_canonical = min(
            reverse[i:] + reverse[:i] for i in range(len(reverse))
        )
        key = min(gaps, reverse_canonical)
        grouped.setdefault(key, []).append(row)
    reversal_classes = [
        {
            "representative": list(key),
            "cyclic_gap_representatives": [
                list(tuple(int(x) for x in row["gaps"]))
                for row in sorted(group, key=lambda item: tuple(item["gaps"]))
            ],
            "cyclic_class_count": len(group),
            "word_weight": sum(int(row["word_orbit_weight"]) for row in group),
        }
        for key, group in sorted(grouped.items())
    ]
    return {
        "p": p,
        "r": r,
        "cyclic_gap_class_count": int(inventory["cyclic_gap_classes"]),
        "reversal_class_count": len(reversal_classes),
        "word_weight_total": sum(int(row["word_weight"]) for row in reversal_classes),
        "expected_word_count": comb(p, r),
        "classes": reversal_classes,
    }


def reversal_gap_pairing_report(p: int, r: int) -> dict[str, object]:
    """Separate reversal-fixed cyclic gap classes from two-class reversal pairs."""
    inventory = reversal_gap_inventory(p, r)
    fixed = [row for row in inventory["classes"] if int(row["cyclic_class_count"]) == 1]
    paired = [row for row in inventory["classes"] if int(row["cyclic_class_count"]) == 2]
    return {
        "p": p,
        "r": r,
        "fixed_cyclic_class_count": len(fixed),
        "paired_orbit_count": len(paired),
        "fixed_word_weight": sum(int(row["word_weight"]) for row in fixed),
        "paired_word_weight": sum(int(row["word_weight"]) for row in paired),
        "total_word_weight": int(inventory["word_weight_total"]),
        "expected_word_count": int(inventory["expected_word_count"]),
    }

