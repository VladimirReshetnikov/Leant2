#!/usr/bin/env python3
"""Small, finite CEGIS experiment, not a general Lean synthesizer.

The fixed skeleton folds left over its input, starting with [].  We enumerate
step expressions over acc, [], [x], and append. No reverse operation is in the
candidate grammar. The Python oracle is used only by the finite verifier.
Successful finite verification is explicitly NOT a universal proof.
"""
from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class Step:
    op: str
    left: Step | None = None
    right: Step | None = None

    def evaluate(self, acc: tuple[int, ...], x: int) -> tuple[int, ...]:
        if self.op == 'acc':
            return acc
        if self.op == 'nil':
            return ()
        if self.op == 'one':
            return (x,)
        if self.op == 'append' and self.left is not None and self.right is not None:
            return self.left.evaluate(acc, x) + self.right.evaluate(acc, x)
        raise ValueError(f'Invalid step expression: {self!r}')

    def render(self) -> str:
        if self.op in ('acc', 'nil', 'one'):
            return {'acc': 'acc', 'nil': '[]', 'one': '[x]'}[self.op]
        assert self.left is not None and self.right is not None
        return f'({self.left.render()} ++ {self.right.render()})'


def grammar(max_nodes: int) -> list[Step]:
    if max_nodes < 1:
        return []
    by_size: dict[int, list[Step]] = {1: [Step('acc'), Step('nil'), Step('one')]}
    for size in range(2, max_nodes + 1):
        by_size[size] = [
            Step('append', left, right)
            for left_size in range(1, size - 1)
            for left in by_size.get(left_size, [])
            for right in by_size.get(size - 1 - left_size, [])
        ]
    return [term for size in range(1, max_nodes + 1) for term in by_size[size]]


def run(step: Step, xs: tuple[int, ...]) -> tuple[int, ...]:
    acc: tuple[int, ...] = ()
    for x in xs:
        acc = step.evaluate(acc, x)
    return acc


def observations(alphabet: Iterable[int], max_length: int) -> list[tuple[int, ...]]:
    values = tuple(alphabet)
    return [xs for n in range(max_length + 1) for xs in itertools.product(values, repeat=n)]


def synthesize(max_nodes: int = 7) -> dict[str, object]:
    terms = grammar(max_nodes)
    domain = observations((-1, 0, 1), 3)
    examples: list[tuple[int, ...]] = [()]
    history: list[dict[str, object]] = []
    checked = 0
    while True:
        candidate = None
        for term in terms:
            checked += 1
            if all(run(term, xs) == xs[::-1] for xs in examples):
                candidate = term
                break
        if candidate is None:
            return {'status': 'finite_grammar_exhausted', 'history': history}
        counterexample = next((xs for xs in domain if run(candidate, xs) != xs[::-1]), None)
        history.append({
            'candidate': candidate.render(),
            'examples_before': [list(xs) for xs in examples],
            'counterexample': None if counterexample is None else list(counterexample),
        })
        if counterexample is None:
            return {
                'status': 'passes_finite_domain_not_universally_proved',
                'grammar_nodes_bound': max_nodes,
                'grammar_terms': len(terms),
                'finite_domain_size': len(domain),
                'candidate_checks_including_revisits': checked,
                'candidate_step': candidate.render(),
                'history': history,
                'lean_universal_proof_file': '../prototype/ReverseCertificate.lean',
            }
        assert counterexample not in examples
        examples.append(counterexample)


def regression_checks() -> dict[str, object]:
    small = observations((0, 1), 1)
    identity = lambda xs: xs
    reverse = lambda xs: xs[::-1]
    assert all(identity(xs) == reverse(xs) for xs in small)
    witness = (0, 1)
    assert identity(witness) != reverse(witness)
    # A single deterministic hole h cannot satisfy h(0)=0 AND h(0)=1.
    consistent_hole_valuations = [y for y in (0, 1) if y == 0 and y == 1]
    assert consistent_hole_valuations == []
    # Independent occurrence-wise angelic values incorrectly report a solution.
    independent_occurrences = [(a, b) for a in (0, 1) for b in (0, 1)
                               if a == 0 and b == 1]
    assert independent_occurrences == [(0, 1)]
    return {
        'observational_equality_is_not_global_equality': {
            'initial_tests': len(small), 'distinguishing_input': list(witness),
            'identity_output': list(identity(witness)),
            'reverse_output': list(reverse(witness)),
        },
        'repeated_hole_requires_functional_consistency': {
            'consistent_assignments': len(consistent_hole_valuations),
            'incorrect_independent_assignments': len(independent_occurrences),
        },
        'all_assertions_passed': True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('cegis-results.json'))
    args = parser.parse_args()
    result = {'synthesis': synthesize(), 'regressions': regression_checks()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
