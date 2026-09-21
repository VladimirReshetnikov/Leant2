#!/usr/bin/env python3
"""Finite mathematical checks accompanying the Leant2 expert-question report.

Python 3.9+, standard library only. These are NOT tests of Leant2 or Lean.
Run: python checks/check_models.py --output checks/results.json
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path
from typing import Callable, Dict, Iterable, List, Sequence, Tuple

Word = Tuple[int, ...]

def words(alphabet: Sequence[int], max_length: int) -> Iterable[Word]:
    for length in range(max_length + 1):
        yield from itertools.product(alphabet, repeat=length)

def fold_right(step: Callable, seed, word: Sequence[int]):
    state = seed
    for symbol in reversed(word):
        state = step(symbol, state)
    return state

def find_machine(k: int, samples: Dict[Word, bool]):
    """Exhaust all k-state right-fold machines with initial state 0.

    Fixing the initial state to 0 loses no machine up to state renaming.
    delta[2*s+a] stores step(a,s), alphabet {0,1}; finish is Boolean.
    """
    tried = 0
    for delta in itertools.product(range(k), repeat=2*k):
        states = {w: fold_right(lambda a, s: delta[2*s+a], 0, w) for w in samples}
        for finish in itertools.product((False, True), repeat=k):
            tried += 1
            if all(finish[states[w]] == output for w, output in samples.items()):
                return {"states": k, "seed": 0, "delta": list(delta),
                        "finish": list(finish), "candidates_examined": tried}
    return {"states": k, "solution": None, "candidates_examined": tried}

def main() -> dict:
    report = {"scope": "Finite mathematical models; no Leant2/Lean execution", "checks": []}
    def record(name: str, **details):
        report["checks"].append({"name": name, "passed": True, **details})

    reverse_inputs = list(words((0,1,2), 6))
    for w in reverse_inputs:
        got = fold_right(lambda a, r: r + (a,), (), w)
        assert got == tuple(reversed(w))
    record("reverse_is_a_plain_right_fold", inputs=len(reverse_inputs), max_length=6)

    # A Boolean output can require three states, despite having only two values.
    samples = {w: len(w) % 3 == 0 for w in words((0,1), 4)}
    machines = [find_machine(k, samples) for k in (1,2,3)]
    assert machines[0]["solution"] is None and machines[1]["solution"] is None
    assert "delta" in machines[2]
    # Existence for all lengths is proved algebraically in the article;
    # this independent witness is additionally checked through length 9.
    witness_delta = [1,1,2,2,0,0]
    witness_finish = [True,False,False]
    for w in words((0,1),9):
        s = fold_right(lambda a, s: witness_delta[2*s+a], 0, w)
        assert witness_finish[s] == (len(w)%3 == 0)
    record("minimal_finite_carrier_for_length_mod_3", samples=len(samples),
           machines=machines, witness_delta=witness_delta, witness_finish=witness_finish)

    suffixes = [(), (0,), (0,0)]
    contexts = [(), (1,), (1,1)]
    rows = [[samples[u+x] for u in contexts] for x in suffixes]
    assert all(any(a != b for a,b in zip(rows[i],rows[j]))
               for i in range(3) for j in range(i+1,3))
    record("context_conflict_clique_lower_bound", rows=rows, clique_size=3)

    r1, r2 = {"c0": False}, {"c1": True}
    conflict = any(r1[c] != r2[c] for c in r1.keys() & r2.keys())
    assert r1 != r2 and not conflict
    record("different_partial_rows_need_not_conflict", row1=r1, row2=r2)

    # One transition can close two coupled obligations; a sum of 1+1 overestimates.
    remaining_cost, naive_sum, safe_max = 1, sum((1,1)), max((1,1))
    assert naive_sum > remaining_cost and safe_max <= remaining_cost
    record("coupled_goal_sum_not_admissible", true_cost=remaining_cost,
           naive_sum=naive_sum, safe_max=safe_max)

    # Same local dependency ID is not sufficient to validate a cache after undo.
    branches = {"left": {"h": 0}, "right": {"h": 1}}
    wrong_key = lambda branch: ("h",)
    right_key = lambda branch: ("h", branches[branch]["h"])
    assert wrong_key("left") == wrong_key("right")
    assert right_key("left") != right_key("right")
    record("rollback_cache_requires_assignment_identity")

    f, g = lambda n: n, lambda n: 0
    assert f(0) == g(0) and f(1) != g(1)
    record("finite_probe_agreement_is_not_global_equivalence")

    # Consistent angelic calls must return the same result at equal arguments.
    consistent_possible = any(v != v for v in range(4))
    independently_guessed_possible = any(v != w for v in range(4) for w in range(4))
    assert not consistent_possible and independently_guessed_possible
    record("angelic_calls_require_shared_constraints")

    # Passing from a slower to a faster execution exposes a longer trace prefix.
    slow, fast = tuple(range(3)), tuple(range(6))
    assert slow == fast[:len(slow)] and slow != fast
    record("deterministic_trace_is_not_identical_wall_clock_output")

    fib = [0,1]
    for _ in range(30):
        fib.append(fib[-1]+fib[-2])
    a,b = 0,1
    for n in range(31):
        assert (a,b) == (fib[n],fib[n+1])
        a,b = b,a+b
    record("fibonacci_pair_invariant", inputs=31)

    # An existentially chosen failed oracle value must not refute all choices.
    options = (0,1)
    assert not (options[0] == 1) and any(v == 1 for v in options)
    record("failed_angelic_choice_is_not_branch_refutation")
    report["passed"] = len(report["checks"])
    return report

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = main()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text)
