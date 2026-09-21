#!/usr/bin/env python3
"""Finite executable checks accompanying the Leant2 expert-questions report.

These are mathematical toy models, NOT a Lean implementation, a benchmark of
Leant2, or a verification of its kernel interface. Python 3.10+, standard library.
Run: python3 model_checks.py --output results.json
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path
from typing import Callable, Sequence

Word = tuple[int, ...]

def words(alphabet_size: int, max_length: int) -> list[Word]:
    return [w for n in range(max_length + 1)
            for w in itertools.product(range(alphabet_size), repeat=n)]

def foldr(step: Callable[[int, object], object], seed: object,
          xs: Sequence[int]) -> object:
    state = seed
    for x in reversed(xs):
        state = step(x, state)
    return state

def finite_machines(alphabet_size: int, output_size: int, samples: dict[Word, int],
                    max_states: int) -> dict:
    """Exhaustively inspect every labeled total machine at each state count.
    A table entry delta[a*n+s] is step(a,s); output is finish(state).
    This is a complete decision procedure for these FINITE tables and samples.
    """
    levels = []
    for n in range(1, max_states + 1):
        examined, solutions, first = 0, 0, None
        for delta in itertools.product(range(n), repeat=alphabet_size*n):
            for seed in range(n):
                for finish in itertools.product(range(output_size), repeat=n):
                    examined += 1
                    good = True
                    for xs, expected in samples.items():
                        state = seed
                        for a in reversed(xs):
                            state = delta[a*n+state]
                        if finish[state] != expected:
                            good = False
                            break
                    if good:
                        solutions += 1
                        if first is None:
                            first = dict(delta=list(delta), seed=seed,
                                         finish=list(finish))
        levels.append(dict(states=n, examined=examined, solutions=solutions))
        if solutions:
            return dict(sample_count=len(samples), minimal_states=n,
                        levels=levels, first_witness=first)
    return dict(sample_count=len(samples), minimal_states=None, levels=levels)

def chromatic_number(size: int, edges: set[tuple[int, int]]) -> int:
    for k in range(1, size + 1):
        for colors in itertools.product(range(k), repeat=size):
            if all(colors[u] != colors[v] for u, v in edges):
                return k
    raise AssertionError("Every finite graph has a coloring")

def main() -> dict:
    # One shared assignment can close two logical obligations.
    goals = frozenset(("g1", "g2"))
    close_both_cost = 1
    assert len(goals) > close_both_cost
    astar = dict(open_goals=len(goals), true_remaining_cost=close_both_cost,
                 sum_heuristic=2, max_heuristic=1, sum_is_admissible=False)

    # Reverse is a plain right fold with List as its carrier.
    binary_words = words(2, 7)
    for xs in binary_words:
        got = foldr(lambda a, zs: list(zs) + [a], [], xs)
        assert got == list(reversed(xs))
    reverse = dict(tested_words=len(binary_words), max_length=7,
                   all_match=True, semantic_check_only=True)

    # Missing entries are unknown. Three distinct rows require only two colors.
    rows = ((0, None), (None, 0), (1, None))
    edges = {(i, j) for i in range(3) for j in range(i+1, 3)
             if any(a is not None and b is not None and a != b
                    for a, b in zip(rows[i], rows[j]))}
    chromatic = chromatic_number(3, edges)
    assert edges == {(0, 2)} and chromatic == 2
    partial_table = dict(rows=rows, conflicting_pairs=sorted(edges),
                         distinct_partial_rows=3, chromatic_lower_bound=chromatic)

    parity = finite_machines(2, 2,
        {w: sum(w) % 2 for w in words(2, 4)}, max_states=2)
    assert parity["minimal_states"] == 2
    mod3 = finite_machines(1, 3,
        {w: len(w) % 3 for w in words(1, 5)}, max_states=3)
    assert mod3["minimal_states"] == 3

    # A rolled-back identity is not an assignment/environment fingerprint.
    naive_cache = {"hole7": 0}
    branch_b_assignment = {"hole7": 1}
    stale = naive_cache["hole7"]
    versioned_cache = {("branchA", "hole7", 0): 0,
                       ("branchB", "hole7", 1): 1}
    fresh = versioned_cache[("branchB", "hole7", branch_b_assignment["hole7"])]
    assert stale != 1 and fresh == 1
    cache = dict(stale_value=stale, expected_value=1,
                 versioned_value=fresh)

    # Position tests up to a length bound cannot determine every length.
    bound = 4
    identity = lambda xs: list(xs)
    bounded_identity = lambda xs: list(xs) if len(xs) <= bound else []
    assert all(identity(list(range(n))) == bounded_identity(list(range(n)))
               for n in range(bound+1))
    witness = list(range(bound+1))
    assert identity(witness) != bounded_identity(witness)
    parametric = dict(agreeing_lengths=list(range(bound+1)),
                      first_disagreeing_length=bound+1,
                      witness=witness)

    # Sorting fixes order, not membership of deadline-truncated candidate sets.
    discovered_at = {"a": 3, "b": 7, "c": 12}
    by_work = lambda work: sorted(k for k, v in discovered_at.items() if v <= work)
    slow, fast = by_work(10), by_work(20)
    assert slow != fast and by_work(10) == by_work(10)
    deadline = dict(slow_work=10, fast_work=20, slow_candidates=slow,
                    fast_candidates=fast, same_logical_budget_candidates=by_work(10))

    # Applications are AND-hyperedges, not disjunctive ordinary edges.
    initial = {"A"}
    edge_inputs = {"A", "B"}
    ordinary_graph_claims_c = bool(initial & edge_inputs)
    hypergraph_claims_c = edge_inputs <= initial
    assert ordinary_graph_claims_c and not hypergraph_claims_c
    hypergraph = dict(initial=sorted(initial), required=sorted(edge_inputs),
                      ordinary_path_reaches_C=ordinary_graph_claims_c,
                      conjunctive_reachability_reaches_C=hypergraph_claims_c)

    return dict(status="all checks passed", experiment_groups=8,
                scope="finite toy-model checks; no Lean execution or performance claim",
                astar=astar, reverse=reverse, incomplete_observation_table=partial_table,
                finite_carriers=dict(parity=parity, unary_mod3=mod3),
                rollback_cache=cache, bounded_parametric_testing=parametric,
                deadline_vs_work=deadline, hypergraph=hypergraph)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    result = main()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")
