#!/usr/bin/env python3
"""Executable finite sanity checks for the accompanying Leant2 research report.

These are Python checks of mathematical examples, not Lean type checks,
Leant2 benchmarks, or proofs of the proposed engine implementation.
Uses only the Python standard library; compatible with Python 3.9+.
"""
from __future__ import annotations
import itertools
import json
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Tuple, TypeVar

A = TypeVar('A')
B = TypeVar('B')

def foldr(step: Callable[[A, B], B], seed: B, xs: Sequence[A]) -> B:
    state = seed
    for x in reversed(xs):
        state = step(x, state)
    return state

def words(alphabet: Sequence[int], max_length: int) -> Iterable[Tuple[int, ...]]:
    for n in range(max_length + 1):
        yield from itertools.product(alphabet, repeat=n)

def reverse_plain(xs: Sequence[int]) -> List[int]:
    return foldr(lambda a, r: r + [a], [], xs)

def reverse_endo(xs: Sequence[int]) -> List[int]:
    # Denotational check only: Python list prepending copies, so this is not
    # a performance model of Lean's linked lists.
    def step(a: int, k: Callable[[List[int]], List[int]]) -> Callable[[List[int]], List[int]]:
        return lambda ys: k([a] + ys)
    return foldr(step, lambda ys: ys, xs)([])

def minmax(xs: Sequence[int]) -> Optional[Tuple[int, int]]:
    def step(a: int, state: Optional[Tuple[int, int]]) -> Optional[Tuple[int, int]]:
        return (a, a) if state is None else (min(a, state[0]), max(a, state[1]))
    return foldr(step, None, xs)

def fib_pair(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a

def fib_doubling(n: int) -> Tuple[int, int]:
    if n == 0:
        return (0, 1)
    a, b = fib_doubling(n // 2)
    c, d = a * (2 * b - a), a * a + b * b
    return (d, c + d) if n % 2 else (c, d)

def unary_output(transitions: Tuple[int, ...], outputs: Tuple[bool, ...], n: int) -> bool:
    state = 0
    for _ in range(n):
        state = transitions[state]
    return outputs[state]

def compatible(left: Dict[int, bool], right: Dict[int, bool]) -> bool:
    return all(left[c] == right[c] for c in left.keys() & right.keys())

def main() -> None:
    samples = list(words((0, 1, 2), 7))
    assert len(samples) == 3280
    for xs in samples:
        expected = list(reversed(xs))
        assert reverse_plain(xs) == expected
        assert reverse_endo(xs) == expected
        assert minmax(xs) == ((min(xs), max(xs)) if xs else None)
    for n in range(61):
        assert fib_pair(n) == fib_doubling(n)[0]

    # Full observations for h(a^n) = (n mod 3 == 0).
    rows = [{p: (p + s) % 3 == 0 for p in range(3)} for s in range(3)]
    edges = [(i, j) for i in range(3) for j in range(i + 1, 3)
             if not compatible(rows[i], rows[j])]
    assert len(edges) == 3
    # Distinct partial rows need not be incompatible.
    sparse_rows = [{0: False}, {1: True}]
    assert sparse_rows[0] != sparse_rows[1] and compatible(*sparse_rows)

    machines = {}
    for size in (1, 2, 3):
        tested = accepted = 0
        for transition in itertools.product(range(size), repeat=size):
            for output in itertools.product((False, True), repeat=size):
                tested += 1
                accepted += all(unary_output(transition, output, n) == (n % 3 == 0)
                                for n in range(9))
        machines[str(size)] = {'tested': tested, 'sample_consistent': accepted}
    assert machines == {'1': {'tested': 2, 'sample_consistent': 0},
                        '2': {'tested': 16, 'sample_consistent': 0},
                        '3': {'tested': 216, 'sample_consistent': 2}}

    # Top-level sample coincidence is not a congruence for composition.
    f = lambda n: n
    g = lambda n: n if n < 2 else 0
    assert all(f(n) == g(n) for n in (0, 1))
    assert f(1 + 1) != g(1 + 1)

    # Illustrative ABA error in a rollback cache, not a Lean evaluator.
    bad_cache = {('hole', 1): False}  # branch A: hole=0, query hole==1
    branch_b_actual = (1 == 1)       # branch B: hole=1, reused version 1
    assert bad_cache[('hole', 1)] != branch_b_actual
    good_cache = {('branch-A', 'hole', 1): False}
    assert ('branch-B', 'hole', 1) not in good_cache

    # An abstract coupled-goal cost counterexample.
    goal_count = 2
    shared_instantiation_cost = 1
    assert goal_count > shared_instantiation_cost

    result = {
        'scope': 'Python finite semantic sanity checks only; no Lean or Leant2 execution',
        'reverse': {'alphabet': [0, 1, 2], 'max_length': 7, 'cases': len(samples),
                    'plain_fold_and_endomorphism_fold_match_reference': True},
        'optional_minmax': {'cases': len(samples), 'all_match_reference': True},
        'fibonacci_pair': {'n_min': 0, 'n_max': 60, 'cases': 61,
                           'matches_fast_doubling': True},
        'unary_moore_machines': {'initial_state': 0, 'sample_lengths': list(range(9)),
                                 'enumeration': machines,
                                 'certifying_incompatibility_clique_size': 3},
        'partial_observation_rows': {'unequal_rows_can_merge': True},
        'sample_equivalence': {'agrees_on': [0, 1], 'distinguishing_argument': 2,
                              'not_a_composition_congruence': True},
        'rollback_cache': {'generation_reuse_is_unsafe': True,
                           'branch_qualified_key_avoids_this_example': True},
        'heuristic': {'open_goals': goal_count,
                      'possible_remaining_cost': shared_instantiation_cost,
                      'goal_count_is_not_an_admissible_lower_bound': True},
        'all_assertions_passed': True
    }
    destination = Path(__file__).with_name('semantic_results.json')
    destination.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
