#!/usr/bin/env python3
"""Finite, reproducible CEGIS experiment for list-fold steps.

This is an algorithm experiment, not a general Lean synthesizer. The synthesis
inventory contains only [], [head], tail-result, and append. Python's reverse is
used only by the verifier. Certificates.lean independently proves the exact
selected Lean step correct for all lists, and proves the length-summary rule.
"""
from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Iterable, Optional


@dataclass(frozen=True)
class Step:
    tag: str
    left: Optional["Step"] = None
    right: Optional["Step"] = None

    def size(self) -> int:
        if self.tag != "append":
            return 1
        assert self.left is not None and self.right is not None
        return 1 + self.left.size() + self.right.size()

    def summary(self) -> tuple[int, int]:
        if self.tag == "nil":
            return (0, 0)
        if self.tag == "single":
            return (0, 1)
        if self.tag == "tail":
            return (1, 0)
        assert self.left is not None and self.right is not None
        a, b = self.left.summary()
        c, d = self.right.summary()
        return (a + c, b + d)

    def evaluate(self, head: int, tail_result: tuple[int, ...]) -> tuple[int, ...]:
        if self.tag == "nil":
            return ()
        if self.tag == "single":
            return (head,)
        if self.tag == "tail":
            return tail_result
        assert self.left is not None and self.right is not None
        return self.left.evaluate(head, tail_result) + self.right.evaluate(head, tail_result)

    def run(self, xs: tuple[int, ...]) -> tuple[int, ...]:
        if not xs:
            return ()
        return self.evaluate(xs[0], self.run(xs[1:]))

    def lean(self) -> str:
        if self.tag == "nil":
            return "Step.nil"
        if self.tag == "single":
            return "Step.single"
        if self.tag == "tail":
            return "Step.tail"
        assert self.left is not None and self.right is not None
        return f"(Step.append {self.left.lean()} {self.right.lean()})"


@lru_cache(maxsize=None)
def exact_size(size: int) -> tuple[Step, ...]:
    if size == 1:
        # This order deliberately puts the identity step before reversal.
        return (Step("nil"), Step("single"), Step("tail"))
    if size < 1 or size % 2 == 0:
        return ()
    result: list[Step] = []
    for left_size in range(1, size - 1, 2):
        right_size = size - 1 - left_size
        for left in exact_size(left_size):
            for right in exact_size(right_size):
                result.append(Step("append", left, right))
    return tuple(result)


def corpus(max_length: int = 4) -> tuple[tuple[int, ...], ...]:
    return tuple(xs for n in range(max_length + 1)
                 for xs in itertools.product((0, 1, 2), repeat=n))


def oracle(xs: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(reversed(xs))


def signature(step: Step, bank: Iterable[tuple[int, ...]]) -> tuple[tuple[int, ...], ...]:
    return tuple(step.run(xs) for xs in bank)


def cegis(candidates: tuple[Step, ...], verifier_inputs: tuple[tuple[int, ...], ...]) -> dict:
    bank: list[tuple[int, ...]] = [(), (0,)]
    rounds: list[dict] = []
    while True:
        # Keep every member of an observation class. Repartition on each new
        # counterexample rather than deleting non-representatives permanently.
        groups: dict[tuple[tuple[int, ...], ...], list[Step]] = {}
        for step in candidates:
            groups.setdefault(signature(step, bank), []).append(step)
        target_signature = tuple(oracle(xs) for xs in bank)
        survivors = groups.get(target_signature, [])
        if not survivors:
            return {"status": "finite_grammar_exhausted", "rounds": rounds}
        chosen = survivors[0]
        witness = next((xs for xs in verifier_inputs if chosen.run(xs) != oracle(xs)), None)
        rounds.append({
            "bank": [list(xs) for xs in bank],
            "observation_classes": len(groups),
            "consistent_candidates": len(survivors),
            "selected_step": chosen.lean(),
            "selected_size": chosen.size(),
            "counterexample": None if witness is None else list(witness),
        })
        if witness is None:
            return {"status": "finite_corpus_pass", "rounds": rounds,
                    "selected_step": chosen.lean(), "corpus_size": len(verifier_inputs)}
        bank.append(witness)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-size", type=int, default=9)
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    args = parser.parse_args()
    if not 1 <= args.max_size <= 11:
        parser.error("--max-size must be between 1 and 11 (explicit resource guard)")
    candidates = tuple(step for n in range(1, args.max_size + 1) for step in exact_size(n))
    viable = tuple(step for step in candidates if step.summary() == (1, 1))
    inputs = corpus()
    # Exhaustively check the proposed summary against a small concrete domain.
    # The universal version is a separately checked Lean theorem.
    summary_checks = 0
    for step in candidates:
        a, b = step.summary()
        for n in range(5):
            assert len(step.evaluate(7, tuple(range(n)))) == a * n + b
            summary_checks += 1
    plain = cegis(candidates, inputs)
    guided = cegis(viable, inputs)
    # An intentionally unsound optimization: retain only the first permanent
    # representative of each class under the initial examples.
    bank = [(), (0,)]
    representatives: dict[tuple[tuple[int, ...], ...], Step] = {}
    for step in viable:
        representatives.setdefault(signature(step, bank), step)
    naive = cegis(tuple(representatives.values()), inputs)
    results = {
        "grammar": "step ::= nil | single(head) | tailResult | append(step, step)",
        "max_ast_nodes": args.max_size,
        "generated_candidates": len(candidates),
        "candidates_by_size": {str(n): len(exact_size(n)) for n in range(1, args.max_size + 1, 2)},
        "length_viable_candidates": len(viable),
        "length_pruned_candidates": len(candidates) - len(viable),
        "summary_concrete_checks": summary_checks,
        "plain_cegis": plain,
        "length_guided_cegis": guided,
        "permanent_observation_dedup_control": naive,
        "interpretation": "Finite corpus passes are not universal correctness proofs. See the Lean certificate for the exact selected AST.",
    }
    if args.max_size >= 3:
        assert guided["status"] == "finite_corpus_pass"
        assert guided["selected_step"] == "(Step.append Step.tail Step.single)"
        assert naive["status"] == "finite_grammar_exhausted"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
