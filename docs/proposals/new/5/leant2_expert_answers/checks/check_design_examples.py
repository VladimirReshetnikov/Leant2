#!/usr/bin/env python3
"""Finite checks for the companion article; NOT a Leant2 benchmark.

Uses only Python's standard library. The machine enumeration fixes the initial
state to 0 without loss of generality (rename the initial state of any machine).
Every transition table and Boolean output table is enumerated for 1..3 states.
"""
from __future__ import annotations
import itertools
import json
from pathlib import Path
from typing import Iterable

Word = tuple[int, ...]

def words(max_length: int) -> list[Word]:
    return [w for n in range(max_length + 1)
            for w in itertools.product((0, 1), repeat=n)]

def target(w: Word) -> bool:
    return 0 in w and 1 in w

def run_machine(w: Word, table: tuple[int, ...], outputs: tuple[bool, ...], m: int) -> bool:
    state = 0
    # Right fold: consume the suffix first; table[a*m + q] is step(a,q).
    for a in reversed(w):
        state = table[a * m + state]
    return outputs[state]

def finite_carriers() -> dict:
    samples = words(3)
    counts = []
    for m in (1, 2, 3):
        tried = 0
        survivors = 0
        for table in itertools.product(range(m), repeat=2*m):
            for outputs in itertools.product((False, True), repeat=m):
                tried += 1
                if all(run_machine(w, table, outputs, m) == target(w) for w in samples):
                    survivors += 1
        assert survivors == 0
        counts.append({'states': m, 'tables_checked': tried, 'survivors': survivors})
    suffixes: list[Word] = [(), (0,), (1,), (0, 1)]
    prefixes: list[Word] = [(), (0,), (1,)]
    rows = [[int(target(u+x)) for u in prefixes] for x in suffixes]
    assert len({tuple(row) for row in rows}) == 4
    # Four states store two presence bits. Initial state is 00.
    table4 = tuple(q | (1 << a) for a in (0, 1) for q in range(4))
    outputs4 = (False, False, False, True)
    for w in words(8):
        assert run_machine(w, table4, outputs4, 4) == target(w)
    return {'observations': len(samples), 'enumeration': counts,
            'distinguishing_rows': rows, 'four_state_table': table4,
            'four_state_output': outputs4, 'four_state_test_words': len(words(8))}

def reverse_fold(w: Word) -> Word:
    r: Word = ()
    for a in reversed(w):
        r = r + (a,)
    return r

def reverse_continuation(w: Word) -> Word:
    k = lambda ys: ys
    for a in reversed(w):
        old_k = k
        k = lambda ys, a=a, old_k=old_k: old_k((a,) + ys)
    return k(())

def other_checks() -> dict:
    test_words = words(7)
    for w in test_words:
        assert reverse_fold(w) == tuple(reversed(w)) == reverse_continuation(w)
    # Incomplete observation-row agreement is not an equivalence relation.
    rows = [(0, None), (None, 1), (1, 1)]
    def compatible(a, b):
        return all(x is None or y is None or x == y for x, y in zip(a, b))
    assert compatible(rows[0], rows[1]) and compatible(rows[1], rows[2])
    assert not compatible(rows[0], rows[2])
    # A stale cache keyed only by a hole name incorrectly reuses branch A's result.
    cache_bad = {'m': (0 == 1)}
    sibling_assignment = 1
    assert cache_bad['m'] != (sibling_assignment == 1)
    cache_versioned = {('m', 'branchA'): False, ('m', 'branchB'): True}
    assert cache_versioned[('m', 'branchB')]
    # One assignment with free propagation can close two obligations.
    true_remaining_cost = 1
    open_goal_count = 2
    assert open_goal_count > true_remaining_cost
    # Testing every canonical list of length <= N does not establish equivalence.
    n = 7
    def alternative(w): return () if len(w) > n else w
    assert all(alternative(w) == w for w in test_words)
    assert alternative((0,) * (n+1)) != (0,) * (n+1)
    return {'reversal_words_checked': len(test_words),
            'partial_row_compatibility_nontransitive': True,
            'rollback_cache_counterexample': True,
            'open_goal_heuristic_counterexample': {'h': open_goal_count,
                                                   'true_cost': true_remaining_cost},
            'bounded_observation_non_equivalence': True}

def main() -> None:
    report = {'scope': 'finite mathematical models, not Lean execution or engine performance',
              'finite_carriers': finite_carriers(), 'other_checks': other_checks()}
    out = Path(__file__).with_name('results.json')
    out.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
