#!/usr/bin/env python3
"""Executable models of two design invariants; NOT a full Lean synthesizer.

1. Observational buckets retain all derivations, so a new observation can split
   a bucket and resurrect a correct candidate hidden behind a bad representative.
2. Counterexample-guided selection of a finite affine-fold sketch. The universal
   correctness proof of the selected parameters is in lean/RecursionCertificates.lean.
No timings or coverage claims are inferred from these small regression models.
"""
from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable


@dataclass(frozen=True)
class BooleanCandidate:
    name: str
    function: Callable[[bool], bool]


def buckets(candidates: Iterable[BooleanCandidate], tests: tuple[bool, ...]) -> dict:
    result: dict[tuple[bool, ...], list[BooleanCandidate]] = {}
    for candidate in candidates:
        signature = tuple(candidate.function(x) for x in tests)
        result.setdefault(signature, []).append(candidate)
    return result


def observational_regression() -> dict:
    candidates = [BooleanCandidate("constant_true", lambda _: True),
                  BooleanCandidate("identity", lambda x: x),
                  BooleanCandidate("constant_false", lambda _: False),
                  BooleanCandidate("not", lambda x: not x)]
    initial = buckets(candidates, (True,))
    destructively_retained = [group[0] for group in initial.values()]
    naive_solutions = [c.name for c in destructively_retained
                       if all(c.function(x) == x for x in (True, False))]
    recovered = [c.name for group in buckets(candidates, (True, False)).values()
                 for c in group if all(c.function(x) == x for x in (True, False))]
    assert naive_solutions == []
    assert recovered == ["identity"]
    assert sum(map(len, initial.values())) == len(candidates)
    return {"initial_tests": [True], "initial_bucket_sizes": sorted(map(len, initial.values())),
            "new_counterexample": False, "destructive_merging_solutions": naive_solutions,
            "retained_derivation_solutions": recovered,
            "claim": "Exact on Bool, not a universal equivalence test for arbitrary Lean functions."}


@dataclass(frozen=True, order=True)
class Fold:
    base: int
    element: int
    accumulator: int
    bias: int

    def evaluate(self, xs: tuple[int, ...]) -> int:
        result = self.base
        for x in reversed(xs):
            result = self.element * x + self.accumulator * result + self.bias
        return result


def finite_fold_cegis() -> dict:
    grammar = [Fold(*coefficients) for coefficients in itertools.product(range(3), repeat=4)]
    # This finite verifier supplies counterexamples. It is NOT the universal proof.
    domain = [xs for length in range(5)
              for xs in itertools.product(range(3), repeat=length)]
    tests: list[tuple[int, ...]] = []
    trace: list[dict] = []
    survivors = grammar
    while survivors:
        candidate = survivors[0]
        counterexample = next((xs for xs in domain
                               if candidate.evaluate(xs) != sum(xs)), None)
        trace.append({"candidate": candidate.__dict__, "survivors": len(survivors),
                      "counterexample": list(counterexample) if counterexample is not None else None})
        if counterexample is None:
            break
        tests.append(counterexample)
        survivors = [f for f in grammar if all(f.evaluate(xs) == sum(xs) for xs in tests)]
    else:
        raise AssertionError("The known satisfying sketch was lost")
    assert candidate == Fold(0, 1, 1, 0)
    assert len(domain) == 121
    # The selected candidates remaining after all finite tests are explicitly counted.
    full_survivors = [f for f in grammar if all(f.evaluate(xs) == sum(xs) for xs in domain)]
    assert full_survivors == [candidate]
    return {"grammar_size": len(grammar), "finite_verifier_inputs": len(domain),
            "trace": trace, "selected": candidate.__dict__,
            "full_finite_survivors": len(full_survivors),
            "universal_proof": "RecursionCertificates.sumCorrect (separately Lean-checked)",
            "claim": "A finite sketch experiment, not automatic recursion-scheme invention."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("experiments/results.json"))
    args = parser.parse_args()
    result = {"observational_buckets": observational_regression(), "affine_fold": finite_fold_cegis()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
