#!/usr/bin/env python3
"""Deterministic finite sanity checks for the accompanying article.

Python 3.9+; standard library only. These are not Lean proofs, an implementation
of Leant2, or measurements of synthesis/model accuracy. The mathematical claims
for arbitrary inputs are justified separately in the article.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path
from typing import Callable, Iterable, List, Sequence, Tuple, TypeVar

A = TypeVar("A")
B = TypeVar("B")
Pair = Tuple[int, int]


def words(alphabet: Sequence[A], max_length: int) -> List[Tuple[A, ...]]:
    return [w for n in range(max_length + 1)
            for w in itertools.product(alphabet, repeat=n)]


def foldr(step: Callable[[A, B], B], initial: B, xs: Iterable[A]) -> B:
    result = initial
    for x in reversed(tuple(xs)):
        result = step(x, result)
    return result


def reverse_checks() -> dict:
    inputs = words((0, 1), 8)
    accumulators = words((0, 1), 3)
    for xs in inputs:
        assert foldr(lambda a, r: r + (a,), (), xs) == xs[::-1]
        # Default arguments capture the current step's values, avoiding late binding.
        composed = foldr(
            lambda a, k: (lambda acc, a=a, k=k: k((a,) + acc)),
            lambda acc: acc,
            xs,
        )
        for acc in accumulators:
            assert composed(acc) == xs[::-1] + acc
    return {
        "input_lists": len(inputs),
        "snoc_fold_checks": len(inputs),
        "accumulator_lists": len(accumulators),
        "function_carrier_checks": len(inputs) * len(accumulators),
        "all_passed": True,
    }


def unary_machine_checks() -> dict:
    # Initial state fixed to 0; all other finite transition/output tables are tried.
    samples = [(n, n % 3 == 0) for n in range(9)]
    runs = []
    witness = None
    for q in range(1, 4):
        tested = 0
        matches = 0
        for transition in itertools.product(range(q), repeat=q):
            for output in itertools.product((False, True), repeat=q):
                tested += 1
                state = 0
                correct = True
                for n, wanted in samples:
                    if output[state] != wanted:
                        correct = False
                        break
                    state = transition[state]
                if correct:
                    matches += 1
                    if witness is None:
                        witness = {"states": q, "initial": 0,
                                   "transition": list(transition),
                                   "output": list(output)}
        runs.append({"states": q, "tables_tested": tested, "matches": matches})
    assert [r["matches"] > 0 for r in runs] == [False, False, True]
    rows = [[(s + context) % 3 == 0 for context in range(3)] for s in range(3)]
    assert len({tuple(row) for row in rows}) == 3
    return {"sample_lengths": list(range(9)), "enumeration": runs,
            "first_witness": witness, "complete_distinguishing_rows": rows,
            "minimum_for_these_samples": 3, "all_passed": True}


def prefix_summary(xs: Sequence[int]) -> Pair:
    total = 0
    peak = 0
    for x in xs:
        total += x
        peak = max(peak, total)
    return total, peak


def combine(left: Pair, right: Pair) -> Pair:
    s, m = left
    t, n = right
    return s + t, max(m, s + n)


def prefix_checks() -> dict:
    inputs = words((-1, 0, 1), 4)
    for xs in inputs:
        # Maximum prefix sum alone is a right fold; tupling is needed for the
        # concatenation-homomorphism scheme, NOT for this ordinary right fold.
        assert foldr(lambda x, m: max(0, x + m), 0, xs) == prefix_summary(xs)[1]
        for ys in inputs:
            assert combine(prefix_summary(xs), prefix_summary(ys)) == prefix_summary(xs + ys)
    states = [(s, m) for s in range(-3, 4) for m in range(4) if s <= m]
    for s in states:
        assert combine((0, 0), s) == s
        assert combine(s, (0, 0)) == s
    for a, b in itertools.product(states, repeat=2):
        c = combine(a, b)
        assert c[1] >= 0 and c[0] <= c[1]
    for a, b, c in itertools.product(states, repeat=3):
        assert combine(combine(a, b), c) == combine(a, combine(b, c))
    # Without the reachable-state invariant, the proposed identity fails.
    assert combine((0, 0), (1, -1)) != (1, -1)
    # h(xs) alone cannot determine h(xs ++ zs) in the concatenation scheme.
    xs, ys, zs = (0,), (-1,), (1,)
    assert prefix_summary(xs)[1] == prefix_summary(ys)[1]
    assert prefix_summary(xs + zs)[1] != prefix_summary(ys + zs)[1]
    return {"input_lists": len(inputs), "right_fold_checks": len(inputs),
            "concatenation_checks": len(inputs) ** 2,
            "invariant_states": len(states), "identity_checks": 2 * len(states),
            "closure_checks": len(states) ** 2,
            "associativity_checks": len(states) ** 3,
            "unrestricted_identity_counterexample": [1, -1],
            "scheme_distinguishing_inputs": [list(xs), list(ys), list(zs)],
            "all_passed": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    results = {"scope": "finite semantic sanity checks; not Lean or Leant2 benchmarks",
               "reverse": reverse_checks(),
               "unary_machines": unary_machine_checks(),
               "maximum_prefix_sum": prefix_checks()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(results, indent=2, sort_keys=True) + "\n"
    args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")


if __name__ == "__main__":
    main()
