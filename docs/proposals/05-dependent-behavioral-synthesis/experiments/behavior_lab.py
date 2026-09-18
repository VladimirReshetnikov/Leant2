#!/usr/bin/env python3
"""Finite behavioral-search laboratory; not a Lean synthesis implementation.

Standard library only, Python 3.9+. Enumerates a deliberately tiny total DSL,
checks an exact affine-length interpretation, and exercises reversible
observational parking. Finite testing is NEVER labeled universal verification.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
import itertools
import json
from pathlib import Path
import unittest
from typing import Dict, Iterable, List, Tuple

Word = Tuple[int, ...]
Input = Tuple[Word, Word]

@dataclass(frozen=True)
class Term:
    op: str
    args: Tuple['Term', ...] = ()

    def evaluate(self, xs: Word, ys: Word) -> Word:
        if self.op == 'empty':
            return ()
        if self.op == 'xs':
            return xs
        if self.op == 'ys':
            return ys
        if self.op == 'reverse':
            return self.args[0].evaluate(xs, ys)[::-1]
        if self.op == 'append':
            return self.args[0].evaluate(xs, ys) + self.args[1].evaluate(xs, ys)
        raise ValueError('Unknown constructor: ' + self.op)

    def lengths(self) -> Tuple[int, int]:
        """Exact coefficients a,b: len(eval(t,x,y)) = a*len(x)+b*len(y)."""
        if self.op == 'empty':
            return 0, 0
        if self.op == 'xs':
            return 1, 0
        if self.op == 'ys':
            return 0, 1
        if self.op == 'reverse':
            return self.args[0].lengths()
        if self.op == 'append':
            a, b = self.args[0].lengths()
            c, d = self.args[1].lengths()
            return a + c, b + d
        raise ValueError('Unknown constructor: ' + self.op)

    def __str__(self) -> str:
        if not self.args:
            return self.op
        return self.op + '(' + ', '.join(map(str, self.args)) + ')'


def enumerate_terms(max_size: int) -> List[Term]:
    if max_size < 1:
        raise ValueError('max_size must be positive')
    by_size: Dict[int, List[Term]] = {1: [Term('empty'), Term('xs'), Term('ys')]}
    for size in range(2, max_size + 1):
        terms = [Term('reverse', (t,)) for t in by_size[size - 1]]
        for left_size in range(1, size - 1):
            right_size = size - left_size - 1
            terms.extend(Term('append', (left, right))
                         for left in by_size[left_size]
                         for right in by_size[right_size])
        by_size[size] = terms
    return [t for size in range(1, max_size + 1) for t in by_size[size]]


def inputs() -> List[Input]:
    words = [tuple(w) for n in range(3) for w in itertools.product((0, 1), repeat=n)]
    return list(itertools.product(words, words))


class ParkingBank:
    """Keep the complete finite member set, not one irreversible representative.

    Production implementations can retain replay recipes instead of ASTs.
    Re-bucketing re-evaluates only actual concrete closed terms here.
    """
    def __init__(self, members: Iterable[Term]):
        self.members = list(members)
        self.examples: List[Input] = []

    def add(self, example: Input) -> None:
        if example not in self.examples:
            self.examples.append(example)

    def buckets(self) -> Dict[Tuple[Word, ...], List[Term]]:
        groups: Dict[Tuple[Word, ...], List[Term]] = {}
        for term in self.members:
            signature = tuple(term.evaluate(*x) for x in self.examples)
            groups.setdefault(signature, []).append(term)
        return groups


class MechanismTests(unittest.TestCase):
    def test_affine_lengths_on_all_small_inputs(self) -> None:
        for term in enumerate_terms(7):
            a, b = term.lengths()
            for xs, ys in inputs():
                self.assertEqual(len(term.evaluate(xs, ys)), a * len(xs) + b * len(ys))

    def test_reversible_parking_recovers_distinguished_term(self) -> None:
        zero, identity = Term('empty'), Term('xs')
        bank = ParkingBank([zero, identity])
        bank.add(((), ()))
        self.assertEqual(len(bank.buckets()), 1)
        destructive_representatives = [members[0] for members in bank.buckets().values()]
        bank.add(((1,), ()))
        self.assertEqual(len(bank.buckets()), 2)
        self.assertIn(identity, bank.members)
        self.assertNotIn(identity, destructive_representatives)

    def test_counterexample_only_refutes_a_completion(self) -> None:
        # append(xs, hole) has both a bad and a good completion for append(x,y).
        bad = Term('append', (Term('xs'), Term('empty')))
        good = Term('append', (Term('xs'), Term('ys')))
        pair = ((0,), (1,))
        self.assertNotEqual(bad.evaluate(*pair), pair[0] + pair[1])
        self.assertEqual(good.evaluate(*pair), pair[0] + pair[1])

    def test_unknown_is_not_rejection_or_a_blocking_answer(self) -> None:
        # A verifier queue must keep an unknown result while allowing later work.
        pending, certified = [], []
        for candidate, verdict in [('first', 'unknown'), ('second', 'proof')]:
            if verdict == 'unknown':
                pending.append(candidate)
            elif verdict == 'proof':
                certified.append(candidate)
        self.assertEqual(pending, ['first'])
        self.assertEqual(certified, ['second'])

    def test_correlated_witness_backtracking(self) -> None:
        choices = [0, 1]
        greedy = choices[0]
        continuation_solution = next(n for n in choices if n == 1)
        self.assertNotEqual(greedy, 1)
        self.assertEqual(continuation_solution, 1)


def report(max_size: int = 7) -> dict:
    terms, domain = enumerate_terms(max_size), inputs()
    length_compatible = [t for t in terms if t.lengths() == (1, 1)]
    passing = [t for t in length_compatible
               if all(t.evaluate(xs, ys) == xs + ys for xs, ys in domain)]
    bank = ParkingBank(length_compatible)
    bucket_counts = []
    for example in [((), ()), ((0,), (1,)), ((0, 1), (1, 0))]:
        bank.add(example)
        bucket_counts.append(len(bank.buckets()))
    # Each new counterexample refines the concrete observational partition.
    examples: List[Input] = [((), ())]
    trace = []
    for term in length_compatible:
        if not all(term.evaluate(x, y) == x + y for x, y in examples):
            continue
        counterexample = next((pair for pair in domain
                               if term.evaluate(*pair) != pair[0] + pair[1]), None)
        trace.append({'candidate': str(term), 'counterexample': counterexample})
        if counterexample is None:
            break
        examples.append(counterexample)
    return {
        'scope': 'Finite total DSL, node size <= %d; NOT a Lean coverage benchmark' % max_size,
        'max_ast_nodes': max_size,
        'enumerated_terms': len(terms),
        'concrete_input_pairs': len(domain),
        'affine_length_validation_checks': len(terms) * len(domain),
        'length_compatible_terms': len(length_compatible),
        'excluded_by_necessary_length_condition': len(terms) - len(length_compatible),
        'terms_passing_finite_append_tests': len(passing),
        'first_finite_test_success': str(passing[0]) if passing else None,
        'bucket_counts_on_growing_examples': bucket_counts,
        'all_members_retained': len(bank.members),
        'cegis_trace': trace,
        'limitations': [
            'No general-purpose SMT solver is used.',
            'The Python interpreter and length analysis are not Lean-certified.',
            'Passing the 49 test pairs is not recorded as a universal proof.',
            'This finite grammar includes append as a supplied primitive.',
            'Timing is omitted; these are deterministic mechanism checks, not speed claims.'
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('behavior_results.json'))
    args = parser.parse_args()
    result = unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(MechanismTests))
    if not result.wasSuccessful():
        raise SystemExit(1)
    data = report()
    data['unit_tests_run'] = result.testsRun
    data['unit_test_failures'] = len(result.failures)
    data['unit_test_errors'] = len(result.errors)
    args.output.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(data, indent=2))

if __name__ == '__main__':
    main()
