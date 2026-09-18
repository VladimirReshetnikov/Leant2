#!/usr/bin/env python3
"""Reproducible affine-fold synthesis experiment, standard library only.

This is a bounded synthesis-domain experiment, not a Lean implementation of
Leant2. Generated candidate certificates are consumed by Certificates.lean.
All arithmetic in this experiment is exact Python integer arithmetic.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from itertools import product
from pathlib import Path
import json

@dataclass(frozen=True)
class Candidate:
    c: int
    a: int
    b: int
    d: int
    def evaluate(self, xs: tuple[int, ...]) -> int:
        value = self.c
        for x in reversed(xs):
            value = self.a * x + self.b * value + self.d
        return value

@dataclass(frozen=True)
class Spec:
    A: int
    B: int
    C: int
    def evaluate(self, xs: tuple[int, ...]) -> int:
        return self.A * sum(xs) + self.B * len(xs) + self.C

# Completeness for this schema is proved in the article, not assumed for
# arbitrary Lean programs. Order is intentional and deterministic.
SEPARATORS = ((), (0,), (1,), (0, 0), (0, 1))

def equations(candidate: Candidate, spec: Spec) -> list[tuple[int, int]]:
    return [(candidate.c, spec.C), (candidate.a, spec.A),
            (candidate.b * spec.A, spec.A),
            (candidate.b * spec.B, spec.B),
            (candidate.b * spec.C + candidate.d, spec.B + spec.C)]

def check_certificate(candidate: Candidate, spec: Spec) -> bool:
    return all(left == right for left, right in equations(candidate, spec))

def find_counterexample(candidate: Candidate, spec: Spec) -> tuple[int, ...] | None:
    return next((xs for xs in SEPARATORS
                 if candidate.evaluate(xs) != spec.evaluate(xs)), None)

def solve(spec: Spec, grammar: list[Candidate]) -> dict:
    bank: list[tuple[int, ...]] = []
    trace: list[dict] = []
    point_evaluations = 0
    for candidate in grammar:
        for xs in bank:
            point_evaluations += 1
            if candidate.evaluate(xs) != spec.evaluate(xs):
                break
        else:
            eqs = equations(candidate, spec)
            if check_certificate(candidate, spec):
                trace.append({'candidate': asdict(candidate), 'verdict': 'certified',
                              'equations': eqs})
                return {'spec': asdict(spec), 'candidate': asdict(candidate),
                        'certificate_attempts': len(trace), 'counterexamples': bank,
                        'bank_point_evaluations': point_evaluations, 'trace': trace,
                        'baseline_certificate_attempts': grammar.index(candidate) + 1}
            witness = find_counterexample(candidate, spec)
            if witness is None:
                raise AssertionError('The proved five-point separator property failed')
            if witness in bank:
                raise AssertionError('Counterexample bank failed to reject a candidate')
            bank.append(witness)
            trace.append({'candidate': asdict(candidate), 'verdict': 'counterexample',
                          'input': witness, 'actual': candidate.evaluate(witness),
                          'expected': spec.evaluate(witness)})
    raise AssertionError(f'Grammar unexpectedly has no solution for {spec}')

def main() -> None:
    root = Path(__file__).resolve().parent
    grammar = [Candidate(*params) for params in product(range(3), repeat=4)]
    grammar.sort(key=lambda e: (e.c + e.a + e.b + e.d, e.c, e.a, e.b, e.d))
    specs = [Spec(*params) for params in product(range(3), repeat=3)]
    tasks = [solve(spec, grammar) for spec in specs]
    valid = invalid = 0
    # An exhaustive cross-check over the declared finite parameter domain.
    for spec in specs:
        for candidate in grammar:
            certified = check_certificate(candidate, spec)
            counterexample = find_counterexample(candidate, spec)
            assert certified == (counterexample is None)
            if certified:
                valid += 1
            else:
                invalid += 1
                assert candidate.evaluate(counterexample) != spec.evaluate(counterexample)
    # Separate held-out evaluations do not constitute the universal proof.
    holdout_inputs = [tuple(xs) for n in range(7) for xs in product((0, 2, 5), repeat=n)]
    for task in tasks:
        candidate = Candidate(**task['candidate']); spec = Spec(**task['spec'])
        assert all(candidate.evaluate(xs) == spec.evaluate(xs) for xs in holdout_inputs)
    summary = {'schema': 'f [] = c; f (x::xs) = a*x + b*f xs + d',
               'parameter_values': [0, 1, 2], 'grammar_size': len(grammar),
               'tasks': len(tasks), 'solved': len(tasks),
               'certificate_attempts': sum(t['certificate_attempts'] for t in tasks),
               'baseline_certificate_attempts': sum(t['baseline_certificate_attempts'] for t in tasks),
               'counterexamples_replayed': sum(len(t['counterexamples']) for t in tasks),
               'maximum_counterexamples_per_task': max(len(t['counterexamples']) for t in tasks),
               'exhaustive_candidate_spec_pairs': len(specs) * len(grammar),
               'valid_pairs': valid, 'invalid_pairs_with_witnesses': invalid,
               'holdout_inputs_per_solution': len(holdout_inputs),
               'holdout_evaluations': len(holdout_inputs) * len(tasks)}
    (root/'results.json').write_text(json.dumps({'summary': summary, 'tasks': tasks}, indent=2)+'\n')
    source = (root/'CertificatePrelude.lean').read_text()
    for i, task in enumerate(tasks):
        c,a,b,d = (task['candidate'][k] for k in ('c','a','b','d'))
        A,B,C = (task['spec'][k] for k in ('A','B','C'))
        source += (f'\ntheorem task_{i:03d} : ∀ xs : List Nat,\n'
                   f'    affine {c} {a} {b} {d} xs = {A} * xs.sum + {B} * xs.length + {C} := by\n'
                   f'  apply certify <;> decide\n#print axioms task_{i:03d}\n')
    source += '\n#eval Lean.versionString\nend Leant2Affine\n'
    (root/'Certificates.lean').write_text(source)
    print(json.dumps(summary, indent=2))

if __name__ == '__main__':
    main()
