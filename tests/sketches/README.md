# Public sketch acceptance gates

[run_sketches.py](../../tools/run_sketches.py) checks seven logical cases in
fresh Lean processes. Three positive cases also replay the actual completed
source in separate processes that import only `Lean`. A full successful run
therefore has **7 scored cases, 10 public process stages, and 1 separate
reference process**. The reference process is a prerequisite, not an eighth
case. Its failure makes the runner exit nonzero even when the public score is
7/7; failed or missing stages never shrink the denominator.

| Case | Owned holes | Required outcome |
| --- | ---: | --- |
| `two-hole-fold` | 2 | Fill the step and seed of a supplied `List.foldr`; prove all four original equations and three held-out observations, execute values, and replay the emitted source |
| `lambda-identity` | 1 | Preserve local type/value binders; prove the universal identity contract and held-out Nat/Bool/List observations, execute values, and replay the emitted source |
| `zero-hole-correct` | 0 | Verify a supplied complete fold body against the same original and held-out equations, execute values, and replay its source |
| `zero-hole-wrong` | 0 | Record at least one rejected program for the wrong seed, with no result alias; exhaustion and global impossibility do not pass |
| `duplicate-label` | Invalid | Reject two explicit occurrences of `?same` as a preparation error, with no result alias |
| `unregistered-hole` | Invalid | Reject anonymous `_` as unfinished elaborator work, with no result alias |
| `false-contract` | 2 | Report a certified contract-negative outcome for literal `False`, with no result alias |

Every original process imports `Leant2` and uses the public command's curated
providers and native rules. It verifies that the session provider inventory is
empty. No witness or reference definition is declared before synthesis.
[reference-controls.lean](reference-controls.lean) runs independently and is
never imported by a query or replay: it checks the exact fold contract against
the known witness, wrong seed, and wrong step. Provider-restricted search and
internal ownership/state restoration are separate native tests; empty session
inventory does not mean an empty provider array. The fold is guided synthesis
with a supplied traversal skeleton, while the zero-hole positive is verification
of a supplied program.

The runner extracts the command's actual `leant2 sketch source:` JSON diagnostic
and preserves its term text, changing only indentation for embedding. Each fresh
`import Lean` replay repeats the original contract proof, held-out proof, and
executable checks. The original and replay stages inspect declaration bodies,
including opaque theorem values, and transitive axiom dependencies; holes, free
variables, `sorry`, and axioms outside the standard policy fail the gate. The
native accepted term is authoritative; these independent replays establish that
its displayed source also works for the checked cases.

Well-formed negatives must exit zero and check that both bare `it` and numbered
`it1` are absent through the result map and native alias resolver. Malformed
inputs must exit one with exactly one preparation error at the command and
complete the same absence checks. These fresh-process controls do not test
preservation of aliases from an earlier query; native command tests cover that
stateful behavior. Unexpected errors or warnings, stderr, missing or duplicate
required diagnostics, timeouts, invalid UTF-8, or missing replay stages fail the
runner. A wrong fixed body must produce a positive rejected-program count;
neither a bounded miss nor a claim that every possible program fails suffices.

After building the project, use a fresh output directory for each run:

```powershell
python -B tools/run_sketches.py --budget 5000 --out baseline-out/sketches-5000
python -B tools/run_sketches.py --budget 10000 --out baseline-out/sketches-10000
python -B -m unittest discover -s tools -p 'test_run_sketches.py' -v
```

The runner **never builds**. It retains generated sources, raw JSON stdout,
stderr, elapsed time, exit status, classifications, reference results, and the
actual emitted terms. Before/after fingerprints cover the Lean executable,
recorded project compiled-module inventory, Lean/config sources, runner and
shared helper, and these fixtures. The runtime environment is not recorded.
Cooperative synthesis budgets and the separate process timeout are distinct;
stable fingerprints do not by themselves prove that a build occurred.

These case fields passed focused development runs at both budgets before
promotion. Those receipts came from a changing implementation checkout and do
not establish a complete clean-source aggregate checkpoint. The configured
aggregate adds seven cases to the preceding 832, for **839 across 14 families**;
historical archive scores retain their original scope.
