#!/usr/bin/env python3
"""Finite sanity checks for the Leant2 expert-questions article.

Python 3.10+, standard library only. These are mathematical toy experiments,
not Lean kernel checks, Leant2 benchmarks, or an implementation of Leant2.
Run: python3 experiments/check_claims.py --output experiments/results.json
"""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path
from typing import Iterable

Word = tuple[int, ...]


def words(alphabet: tuple[int, ...], max_length: int) -> Iterable[Word]:
    for n in range(max_length + 1):
        yield from product(alphabet, repeat=n)


def both_symbols(xs: Word) -> bool:
    return 0 in xs and 1 in xs


def run_right_fold(xs: Word, initial: int, transition: tuple[int, ...],
                   outputs: tuple[bool, ...], k: int) -> bool:
    state = initial
    for letter in reversed(xs):
        state = transition[letter * k + state]
    return outputs[state]


def finite_carrier_experiment() -> dict:
    """Exhaust every total k-state Boolean-output machine for k = 1, 2, 3."""
    prefixes: tuple[Word, ...] = ((), (0,), (1,))
    suffixes: tuple[Word, ...] = ((), (0,), (1,), (0, 1))
    profiles = [[both_symbols(c + u) for c in prefixes] for u in suffixes]
    assert len({tuple(row) for row in profiles}) == 4
    observations = {c + u: both_symbols(c + u) for c in prefixes for u in suffixes}
    checked: dict[str, dict[str, int]] = {}
    for k in (1, 2, 3):
        count = 0
        satisfying = 0
        for initial in range(k):
            for transition in product(range(k), repeat=2 * k):
                for out in product((False, True), repeat=k):
                    count += 1
                    if all(run_right_fold(xs, initial, transition, out, k) == answer
                           for xs, answer in observations.items()):
                        satisfying += 1
        assert count == k ** (2 * k + 1) * 2 ** k
        assert satisfying == 0
        checked[str(k)] = {"machines_checked": count, "satisfying_machines": satisfying}

    # State bits record whether 0 and 1 have appeared.
    transition4 = tuple(state | (1 << a) for a in (0, 1) for state in range(4))
    outputs4 = (False, False, False, True)
    tested = 0
    for xs in words((0, 1), 10):
        assert run_right_fold(xs, 0, transition4, outputs4, 4) == both_symbols(xs)
        tested += 1
    return {
        "prefixes": prefixes, "suffixes": suffixes, "profiles": profiles,
        "unique_observations": len(observations), "exhaustive_search": checked,
        "explicit_four_state_transition": transition4,
        "four_state_tested_words": tested,
        "note": "The article supplies the all-input proof; testing alone is not that proof."
    }


def reverse_experiment() -> dict:
    count = 0
    for xs in words((0, 1, 2), 7):
        acc: Word = ()
        for a in reversed(xs):
            acc = acc + (a,)
        assert acc == tuple(reversed(xs))
        count += 1
    # Tail is not itself a plain fold into its own result with identity finish.
    tail = lambda xs: xs[1:]
    u, v, a = (), (1,), 0
    assert tail(u) == tail(v)
    assert tail((a,) + u) != tail((a,) + v)
    return {"reverse_tested_words": count,
            "tail_plain_fold_counterexample": {"u": u, "v": v, "a": a}}


def counterexample_checks() -> dict:
    # Compatibility of partially known rows is not an equivalence relation.
    rows = ((False, None), (None, False), (True, False))
    compatible = lambda x, y: all(a is None or b is None or a == b
                                 for a, b in zip(x, y))
    assert compatible(rows[0], rows[1]) and compatible(rows[1], rows[2])
    assert not compatible(rows[0], rows[2])

    # A single refinement can discharge two shared constraints.
    per_constraint_estimates = (1, 1)
    true_shared_remaining_cost = 1
    assert sum(per_constraint_estimates) > true_shared_remaining_cost

    # Equal values on one probe are not function equality.
    identity, constant = lambda x: x, lambda x: 0
    assert identity(0) == constant(0) and identity(1) != constant(1)

    # Metavariable IDs alone do not identify assignment versions across siblings.
    stale = {("hole7", "observation2"): True}
    branch_values = {("branchA", "hole7"): 0, ("branchB", "hole7"): 1}
    old = stale[("hole7", "observation2")]
    new = branch_values[("branchB", "hole7")] == 0
    assert old != new

    # Surface-disjoint expressions can depend on a shared metavariable transitively.
    dependencies = {"g1": {"m1"}, "g2": {"m2"},
                    "m1": {"u"}, "m2": {"u"}, "u": set()}
    def closure(x: str) -> set[str]:
        result: set[str] = set()
        pending = list(dependencies[x])
        while pending:
            item = pending.pop()
            if item not in result:
                result.add(item)
                pending.extend(dependencies[item])
        return result
    assert not (dependencies["g1"] & dependencies["g2"])
    assert closure("g1") & closure("g2") == {"u"}
    return {"partial_row_compatibility_nontransitive": True,
            "sum_of_shared_goal_costs_can_overestimate": True,
            "finite_observations_do_not_imply_function_equality": True,
            "branch_blind_cache_can_be_stale": True,
            "transitive_dependencies_matter": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results = {"scope": "Finite mathematical sanity checks; no Lean/Leant2 execution",
               "finite_carriers": finite_carrier_experiment(),
               "folds": reverse_experiment(),
               "hazard_witnesses": counterexample_checks()}
    text = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
