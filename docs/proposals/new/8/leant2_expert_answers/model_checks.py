#!/usr/bin/env python3
"""Small, deterministic model checks accompanying the Leant2 research article.

These are not Lean tests, formal proofs, or measurements of Leant2.  They check
finite examples of several claims and deliberately reproduce two bad shortcuts.
Requires Python 3.10+; uses only the standard library.
"""
from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, TypeVar

A = TypeVar("A")
B = TypeVar("B")
Word = tuple[int, ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def foldr(step: Callable[[A, B], B], initial: B, xs: Iterable[A]) -> B:
    result = initial
    for x in reversed(tuple(xs)):
        result = step(x, result)
    return result


def words(alphabet: tuple[int, ...], max_length: int) -> Iterable[Word]:
    for n in range(max_length + 1):
        yield from itertools.product(alphabet, repeat=n)


def incompatible_graph(
    observations: dict[Word, bool], vertices: tuple[Word, ...]
) -> set[tuple[int, int]]:
    """An edge needs an actual common-prefix observation with unequal outputs."""
    prefixes = {w[:cut] for w in observations for cut in range(len(w) + 1)}
    return {
        (i, j)
        for i in range(len(vertices))
        for j in range(i + 1, len(vertices))
        if any(
            u + vertices[i] in observations
            and u + vertices[j] in observations
            and observations[u + vertices[i]] != observations[u + vertices[j]]
            for u in prefixes
        )
    }


@dataclass(frozen=True)
class UnaryFoldMachine:
    transition: tuple[int, ...]
    outputs: tuple[bool, ...]

    def output_at_length(self, n: int) -> bool:
        if n < 0:
            raise ValueError("Length must be nonnegative")
        state = 0
        for _ in range(n):
            state = self.transition[state]
        return self.outputs[state]


def smallest_unary_machine(
    observations: dict[int, bool], max_states: int
) -> tuple[UnaryFoldMachine, list[dict[str, int | bool]]]:
    """Exhaust all total Boolean-output unary machines, with initial state 0.

    Fixing state 0 loses no machine: a state renaming can always name the initial
    state 0.  Exhaustion here is a genuinely finite, exact procedure.
    """
    ledger: list[dict[str, int | bool]] = []
    for q in range(1, max_states + 1):
        checked = 0
        for transition in itertools.product(range(q), repeat=q):
            for outputs in itertools.product((False, True), repeat=q):
                checked += 1
                machine = UnaryFoldMachine(transition, outputs)
                if all(machine.output_at_length(n) == value
                       for n, value in observations.items()):
                    ledger.append({"states": q, "checked": checked,
                                   "exhausted": False, "solution_found": True})
                    return machine, ledger
        ledger.append({"states": q, "checked": checked,
                       "exhausted": True, "solution_found": False})
    raise ValueError("No consistent machine within the declared finite bound")


def run_checks() -> dict[str, object]:
    inputs = tuple(words((0, 1), 10))
    for xs in inputs:
        actual = foldr(lambda x, r: r + (x,), (), xs)
        require(actual == tuple(reversed(xs)), "Plain-fold reversal failed")
    reverse = {"binary_lists_checked": len(inputs), "max_length": 10,
               "plain_fold_agrees_with_reverse": True}

    observations = {tuple([0] * n): n == 2 for n in range(6)}
    vertices = tuple(tuple([0] * n) for n in range(6))
    edges = incompatible_graph(observations, vertices)
    clique = tuple(range(4))
    require(all((i, j) in edges for i, j in itertools.combinations(clique, 2)),
            "Missing edge in the four-state lower-bound certificate")
    machine, ledger = smallest_unary_machine({n: n == 2 for n in range(6)}, 4)
    require(len(machine.transition) == 4, "Expected minimal four-state machine")
    counterexample = next(n for n in range(100)
                          if machine.output_at_length(n) != (n == 2))
    require(counterexample == 6, "Expected first minimal machine to overfit at length 6")
    refined_machine, refined_ledger = smallest_unary_machine(
        {n: n == 2 for n in range(counterexample + 1)}, 4)
    require(refined_machine.transition == (1, 2, 3, 3), "Unexpected refined machine")
    require(all(refined_machine.output_at_length(n) == (n == 2) for n in range(100)),
            "Refined machine does not agree on the additional finite checks")
    carrier = {"observed_lengths": list(range(6)), "graph_vertices": len(vertices),
               "graph_edges": len(edges), "clique_lengths": list(clique),
               "state_lower_bound": 4, "minimal_states_in_exhaustive_search": 4,
               "transition": list(machine.transition),
               "outputs": list(machine.outputs), "enumeration_ledger": ledger,
               "first_minimal_machine_generalizes": False,
               "first_counterexample_length": counterexample,
               "refined_transition": list(refined_machine.transition),
               "refined_outputs": list(refined_machine.outputs),
               "refined_enumeration_ledger": refined_ledger,
               "refined_additional_length_checks": 100}

    # A search-step model: assigning a shared variable closes four constraints.
    number_of_obligations = 4
    optimal_decision_cost = 1
    max_lower_bound = max([1] * number_of_obligations)
    require(number_of_obligations > optimal_decision_cost, "Bad heuristic not exposed")
    require(max_lower_bound <= optimal_decision_cost, "Maximum bound not admissible")
    heuristic = {"open_obligations": number_of_obligations,
                 "optimal_decision_cost": optimal_decision_cost,
                 "hole_count_overestimates": True,
                 "maximum_individual_bound": max_lower_bound}

    naive_cache: dict[str, int] = {}
    def naive_eval(assignment: int) -> int:
        return naive_cache.setdefault("?x + 1", assignment + 1)
    first = naive_eval(0)
    stale = naive_eval(1)
    persistent_cache: dict[tuple[str, int], int] = {}
    def versioned_eval(assignment: int) -> int:
        return persistent_cache.setdefault(("?x + 1", assignment), assignment + 1)
    require(first == 1 and stale == 1, "Expected deliberately stale cache behavior")
    require(versioned_eval(0) == 1 and versioned_eval(1) == 2,
            "Versioned cache failed")
    rollback = {"first_branch_result": first, "naive_second_branch_result": stale,
                "correct_second_branch_result": versioned_eval(1)}

    f = lambda n: 0
    g = lambda n: n * (n - 1)
    probes = (0, 1)
    require(all(f(n) == g(n) for n in probes), "Probe agreement missing")
    require(f(2) != g(2), "Distinguishing context missing")
    profiles = {"probes": list(probes), "agree_on_probes": True,
                "distinguishing_input": 2, "f_output": f(2), "g_output": g(2)}

    row_a = {0: False}
    row_b = {1: True}
    conflict = any(row_a[k] != row_b[k] for k in row_a.keys() & row_b.keys())
    require(not conflict, "Unknown entries were treated as inequalities")
    partial_rows = {"different_partial_rows_force_distinct_states": conflict}

    available = {"A"}
    required_arguments = {"A", "C"}
    conjunctive_enabled = required_arguments <= available
    pairwise_edge_enabled = bool(required_arguments & available)
    require(not conjunctive_enabled and pairwise_edge_enabled,
            "Expected coarse reachability false positive")
    hyperedges = {"available": sorted(available),
                  "provider_arguments": sorted(required_arguments),
                  "conjunctive_provider_enabled": conjunctive_enabled,
                  "pairwise_abstraction_enabled": pairwise_edge_enabled}

    return {"schema_version": 1,
            "scope": "Finite Python models only; no Lean execution or performance claims",
            "all_checks_passed": True,
            "plain_fold_reverse": reverse, "finite_carrier": carrier,
            "shared_goal_heuristic": heuristic, "rollback_cache": rollback,
            "observational_noncongruence": profiles,
            "partial_observation_rows": partial_rows,
            "conjunctive_retrieval": hyperedges}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("model_checks.json"))
    args = parser.parse_args()
    results = run_checks()
    text = json.dumps(results, indent=2, sort_keys=True) + "\n"
    args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
