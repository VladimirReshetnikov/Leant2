#!/usr/bin/env python3
"""Finite-model checks accompanying the Leant2 expert-questions article.

These are independent Python reference checks, not a Lean formalization or a
benchmark of Leant2. Requires Python 3.10+ and only the standard library.
Run: python3 sanity_checks.py --output sanity_results.json
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Callable, Iterable

ALPHABET = "ab"


def words(max_length: int) -> Iterable[str]:
    for length in range(max_length + 1):
        for letters in itertools.product(ALPHABET, repeat=length):
            yield "".join(letters)


def contains_both(word: str) -> bool:
    return "a" in word and "b" in word


def state_of(word: str, seed: int, transitions: tuple[int, ...], k: int) -> int:
    """A right fold: each letter prepends to an already processed suffix."""
    state = seed
    for letter in reversed(word):
        state = transitions[ALPHABET.index(letter) * k + state]
    return state


def finite_carrier_check() -> dict:
    suffixes = ("", "a", "b", "ab")
    contexts = ("", "a", "b")
    samples = sorted({u + x for u in contexts for x in suffixes}, key=lambda w: (len(w), w))
    expected = {w: contains_both(w) for w in samples}
    rows = {x: [contains_both(u + x) for u in contexts] for x in suffixes}
    edges = [
        (x, y)
        for x, y in itertools.combinations(suffixes, 2)
        if any(contains_both(u + x) != contains_both(u + y) for u in contexts)
    ]
    assert len(edges) == 6, "The incompatibility graph should be K4."

    counts = []
    for k in (1, 2, 3):
        transition_seed_pairs = 0
        satisfying_full_machines = 0
        # Each seed/transition pair determines reachable states. Count all
        # Boolean finishing maps consistent with those states exactly.
        for transitions in itertools.product(range(k), repeat=2 * k):
            for seed in range(k):
                transition_seed_pairs += 1
                requirements: dict[int, bool] = {}
                consistent = True
                for w in samples:
                    s = state_of(w, seed, transitions, k)
                    v = expected[w]
                    if s in requirements and requirements[s] != v:
                        consistent = False
                        break
                    requirements[s] = v
                if consistent:
                    satisfying_full_machines += 2 ** (k - len(requirements))
        total_machines = transition_seed_pairs * 2 ** k
        assert total_machines == k * (k ** (2 * k)) * (2 ** k)
        assert satisfying_full_machines == 0
        counts.append({
            "carrier_cardinality": k,
            "transition_seed_pairs_checked": transition_seed_pairs,
            "full_machines_accounted_for": total_machines,
            "sample_consistent_machines": satisfying_full_machines,
        })

    # State encoding: bit 0 = seen a, bit 1 = seen b.
    k = 4
    seed = 0
    transitions = tuple(s | 1 for s in range(k)) + tuple(s | 2 for s in range(k))
    tests = list(words(8))
    assert all((state_of(w, seed, transitions, k) == 3) == contains_both(w) for w in tests)

    feature_functions: dict[str, Callable[[str], bool]] = {
        "seen_a": lambda w: "a" in w,
        "seen_b": lambda w: "b" in w,
    }
    covers: list[list[str]] = []
    names = tuple(feature_functions)
    for n in range(len(names) + 1):
        for chosen in itertools.combinations(names, n):
            if all(any(feature_functions[f](x) != feature_functions[f](y) for f in chosen)
                   for x, y in edges):
                covers.append(list(chosen))
    assert covers == [["seen_a", "seen_b"]]
    return {
        "contexts": list(contexts), "suffixes": list(suffixes),
        "unique_samples": expected, "observation_rows": rows,
        "incompatibility_edges": edges, "clique_lower_bound": 4,
        "exhaustive_counts": counts,
        "four_state_witness": {"seed": seed, "transitions": transitions,
                                "finish_true_states": [3]},
        "witness_tested_words_through_length_8": len(tests),
        "feature_covers_in_declared_two_feature_library": covers,
    }


def other_checks() -> dict:
    # Partial-table compatibility is not transitive: unknown is not a value.
    rows = ({"c": 0}, {}, {"c": 1})
    compatible = lambda a, b: all(a[k] == b[k] for k in a.keys() & b.keys())
    assert compatible(rows[0], rows[1]) and compatible(rows[1], rows[2])
    assert not compatible(rows[0], rows[2])

    # Two obligations closed by a single shared metavariable assignment.
    actual_cost, individual_bounds = 1, [1, 1]
    assert max(individual_bounds) <= actual_cost < sum(individual_bounds)

    # Reverse is both an ordinary (append-using) right fold and a
    # continuation-carrier right fold. This tests reference implementations.
    def reverse_plain(word: str) -> str:
        result = ""
        for a in reversed(word):
            result = result + a
        return result

    def reverse_continuation(word: str) -> str:
        continuation: Callable[[str], str] = lambda acc: acc
        for a in reversed(word):
            previous = continuation
            continuation = lambda acc, a=a, previous=previous: previous(a + acc)
        return continuation("")

    tests = list(words(8))
    assert all(reverse_plain(w) == reverse_continuation(w) == w[::-1] for w in tests)

    # Independent angels can give contradictory answers to the same call.
    independent_angel_choices = [(a, b) for a, b in itertools.product((False, True), repeat=2)
                                 if a != b]
    consistent_angel_choices = [(a, b) for a, b in independent_angel_choices if a == b]
    assert len(independent_angel_choices) == 2 and not consistent_angel_choices

    # Equality on a single probe does not license arbitrary higher-order use.
    f = lambda n: 0
    g = lambda n: 0 if n == 0 else 1
    assert f(0) == g(0) and f(1) != g(1)
    return {
        "partial_row_compatibility_nontransitive": True,
        "shared_goal_true_cost": actual_cost,
        "sum_of_individual_bounds": sum(individual_bounds),
        "max_of_individual_bounds": max(individual_bounds),
        "reverse_implementations_agree_on_words_through_length_8": len(tests),
        "independent_angel_satisfying_choices": len(independent_angel_choices),
        "same_call_consistent_satisfying_choices": len(consistent_angel_choices),
        "probe_equivalence_not_arbitrary_contextual_equivalence": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("sanity_results.json"))
    args = parser.parse_args()
    results = {
        "scope": "Independent finite Python checks; not Lean verification or Leant2 benchmarking.",
        "carrier_check": finite_carrier_check(),
        "other_checks": other_checks(),
        "all_assertions_passed": True,
    }
    args.output.write_text(json.dumps(results, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"All finite checks passed. Results: {args.output}")


if __name__ == "__main__":
    main()
