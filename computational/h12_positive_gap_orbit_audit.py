#!/usr/bin/env python3
"""Exact finite inventory of cyclic positive-gap compositions of 12.

This is a combinatorial audit only; it is not a Lean proof of the H12
operator recurrence or of the boundary contraction.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import argparse


def compositions(total: int, length: int):
    if length < 1 or length > total:
        return
    for cuts in combinations(range(1, total), length - 1):
        bounds = (0,) + cuts + (total,)
        yield tuple(bounds[i + 1] - bounds[i] for i in range(length))


def cyclic_rotations(word):
    return {word[i:] + word[:i] for i in range(len(word))}


def canonical_rotation(word):
    return min(cyclic_rotations(word))


def build_inventory(total: int = 12):
    strata = []
    for r in range(1, total + 1):
        words = list(compositions(total, r))
        reps = sorted({canonical_rotation(w) for w in words})
        orbit_sizes = [len(cyclic_rotations(rep)) for rep in reps]
        histogram = Counter(orbit_sizes)

        # Exact partition checks: every word belongs to exactly one orbit.
        covered = set()
        for rep in reps:
            orbit = cyclic_rotations(rep)
            assert not (covered & orbit), (r, rep, "overlapping orbits")
            covered.update(orbit)
        assert covered == set(words), (r, len(covered), len(words))

        # Exact marked-cut/gap identity coefficient: total * |compositions| / r.
        weighted_count = Fraction(total, r) * len(words)
        strata.append({
            "r": r,
            "ordered_compositions": len(words),
            "cyclic_orbits": len(reps),
            "orbit_size_histogram": {
                str(k): histogram[k] for k in sorted(histogram)
            },
            "orbit_size_sum": sum(orbit_sizes),
            "weighted_word_count": str(weighted_count),
            "representatives": [
                {"gaps": list(rep), "orbit_size": len(cyclic_rotations(rep))}
                for rep in reps
            ],
        })

    even = [s for s in strata if s["r"] % 2 == 0]
    odd = [s for s in strata if s["r"] % 2 == 1]
    summary = {
        "degree": total,
        "ordered_positive_compositions": sum(
            s["ordered_compositions"] for s in strata
        ),
        "even_r_compositions": sum(s["ordered_compositions"] for s in even),
        "odd_r_compositions": sum(s["ordered_compositions"] for s in odd),
        "even_r_cyclic_orbits": sum(s["cyclic_orbits"] for s in even),
        "odd_r_cyclic_orbits": sum(s["cyclic_orbits"] for s in odd),
        "even_r_weighted_total": str(sum(
            Fraction(s["weighted_word_count"]) for s in even
        )),
        "odd_r_weighted_total": str(sum(
            Fraction(s["weighted_word_count"]) for s in odd
        )),
    }
    assert summary["ordered_positive_compositions"] == 2 ** (total - 1)
    assert summary["even_r_compositions"] == 2 ** (total - 2)
    assert summary["odd_r_compositions"] == 2 ** (total - 2)
    assert summary["even_r_cyclic_orbits"] == 179
    assert summary["even_r_weighted_total"] == "2047"
    assert summary["odd_r_weighted_total"] == "2048"
    return {"summary": summary, "strata": strata}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="h12_positive_gap_cyclic_orbit_inventory.json")
    args = parser.parse_args()
    inventory = build_inventory()
    Path(args.output).write_text(
        json.dumps(inventory, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(inventory["summary"], indent=2))


if __name__ == "__main__":
    main()
