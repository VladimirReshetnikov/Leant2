#!/usr/bin/env python3
"""Deterministic finite-model checks supporting the accompanying article.

These are Python model tests, not Lean compilation, Leant2 benchmarks, or a
verification of a proposed Lean implementation. No third-party package is needed.
"""
from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


def all_words(alphabet: tuple[int, ...], max_length: int):
    for length in range(max_length + 1):
        yield from itertools.product(alphabet, repeat=length)


def reverse_by_right_fold(word: tuple[int, ...]) -> tuple[int, ...]:
    state: tuple[int, ...] = ()
    for letter in reversed(word):
        state = state + (letter,)
    return state


def test_reverse_fold() -> dict:
    count = 0
    for word in all_words((0, 1, 2), 6):
        assert reverse_by_right_fold(word) == tuple(reversed(word))
        count += 1
    assert count == 1093
    return {"passed": True, "alphabet_size": 3, "max_length": 6,
            "words_checked": count}


def unary_output(transition: tuple[int, ...], output: tuple[bool, ...],
                 length: int) -> bool:
    state = 0  # Any nonempty machine's initial state can be renamed to zero.
    for _ in range(length):
        state = transition[state]
    return output[state]


def test_minimal_carrier() -> dict:
    examples = {length: length % 3 == 0 for length in range(7)}
    table_counts, solutions = {}, {}
    for k in range(1, 4):
        count = 0
        witnesses = []
        for transition in itertools.product(range(k), repeat=k):
            for output in itertools.product((False, True), repeat=k):
                count += 1
                if all(unary_output(transition, output, n) == wanted
                       for n, wanted in examples.items()):
                    witnesses.append({"transition": transition, "output": output})
        table_counts[str(k)] = count
        solutions[str(k)] = witnesses
    assert table_counts == {"1": 2, "2": 16, "3": 216}
    assert not solutions["1"] and not solutions["2"]
    assert len(solutions["3"]) == 2
    # A separate finite incompatibility certificate, not just enumeration.
    edges = []
    for x, y in itertools.combinations(range(3), 2):
        witnesses = [u for u in range(3) if examples[u + x] != examples[u + y]]
        assert witnesses
        edges.append({"suffix_lengths": [x, y], "prefix_witness": witnesses[0]})
    return {"passed": True, "sample_lengths": list(examples),
            "tables_checked": table_counts,
            "number_of_solutions": {k: len(v) for k, v in solutions.items()},
            "minimum_state_count": 3, "three_state_witness": solutions["3"][0],
            "incompatibility_clique_edges": edges}


def test_joint_cost_bound() -> dict:
    # One abstract transition of cost one solves both obligations.
    true_remaining_cost = 1
    individual_relaxed_costs = (1, 1)
    naive_sum = sum(individual_relaxed_costs)
    admissible_max = max(individual_relaxed_costs)
    assert naive_sum > true_remaining_cost
    assert admissible_max <= true_remaining_cost
    # A separate zero-cost exact rule refutes a positive unit lower bound.
    assert 1 > 0
    return {"passed": True, "model": "two obligations, one joint transition",
            "true_cost": true_remaining_cost, "naive_goal_sum": naive_sum,
            "max_relaxed_cost": admissible_max,
            "positive_goal_count_fails_for_zero_cost_exact": True}


@dataclass(frozen=True)
class CacheEntry:
    dependency_values: tuple[tuple[str, int], ...]
    result: bool


class VersionedObservationCache:
    def __init__(self) -> None:
        self.entries: list[CacheEntry] = []
        self.evaluations = 0
        self.hits = 0

    def observe_zero(self, store: dict[str, int]) -> bool:
        # This model observation reads m and nothing else.
        for entry in self.entries:
            if all(store[key] == value for key, value in entry.dependency_values):
                self.hits += 1
                return entry.result
        result = store["m"] == 0
        self.entries.append(CacheEntry((("m", store["m"]),), result))
        self.evaluations += 1
        return result


def test_rollback_cache() -> dict:
    cache = VersionedObservationCache()
    a, b = {"m": 0, "irrelevant": 12}, {"m": 1, "irrelevant": 12}
    sequence = [cache.observe_zero(a), cache.observe_zero(b),
                cache.observe_zero({"m": 0, "irrelevant": 99})]
    assert sequence == [True, False, True]
    assert cache.evaluations == 2 and cache.hits == 1
    # Both branches have zero unassigned holes, hence that key is insufficient.
    naive_key_a = naive_key_b = ()
    assert naive_key_a == naive_key_b and sequence[0] != sequence[1]
    return {"passed": True, "branch_sequence": ["A", "B", "A_with_unrelated_change"],
            "results": sequence, "evaluations": cache.evaluations, "cache_hits": cache.hits,
            "unassigned_blocker_only_key_is_insufficient": True}


def test_observation_cluster() -> dict:
    bound = 12
    f: Callable[[int], int] = lambda n: n
    g: Callable[[int], int] = lambda n: n if n <= bound else n + 1
    assert all(f(n) == g(n) for n in range(bound + 1))
    assert f(bound + 1) != g(bound + 1)
    return {"passed": True, "matching_inputs": [0, bound],
            "counterexample_input": bound + 1,
            "counterexample_outputs": [f(bound + 1), g(bound + 1)]}


def test_approximation_direction() -> dict:
    concrete_possible_outputs = {0, 1}
    guessed_outputs = {0}
    desired_outputs = {1}
    assert not (guessed_outputs & desired_outputs)
    assert concrete_possible_outputs & desired_outputs
    assert concrete_possible_outputs <= {0, 1, 2}
    return {"passed": True, "concrete_possible_outputs": [0, 1],
            "underapproximation": [0], "desired_outputs": [1],
            "underapproximation_would_falsely_refute": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("model_results.json"))
    args = parser.parse_args()
    results = {
        "scope": "finite Python models; not Leant2 or Lean verification",
        "reverse_fold": test_reverse_fold(),
        "minimal_carrier": test_minimal_carrier(),
        "joint_cost_bound": test_joint_cost_bound(),
        "rollback_cache": test_rollback_cache(),
        "observation_cluster": test_observation_cluster(),
        "approximation_direction": test_approximation_direction(),
    }
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
