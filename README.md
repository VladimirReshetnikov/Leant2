Leant2 is contemplated as exclusively Lean-oriented successor of Djex & Leant, implemented in Lean.

* https://github.com/VladimirReshetnikov/Djex (`C:\Djex\` locally)
* https://github.com/VladimirReshetnikov/Leant (`C:\Leant\` locally)

These tools allow to automatically generate implementations for a subset of Lean type signatures with optional additional behavioral constraints. But they are implemented in Haskell, internally use Haskell approximations of Lean types, and also Djex has a Haskell frontend and needs to remain compatible with it. All these put certain limitations on their Lean capabilities. We would like to create a successor (let's name it Leant2), which is implemented in Lean, has only Lean frontend, and is designed specifically to handle Lean types (+ behavioral constraints). Of course, it couldn't possibly be made to autogenerate implementations for *all* inhabited Lean types (because that's untractable and possibly undecidable problem); but still we would like it to be able to handle a large fraction of Lean types that occur in practice.

A sibling project (we might even merge them if they converge):

* https://github.com/VladimirReshetnikov/Forge (`C:\Forge\` locally)

We may freely borrow any Lean code and ideas from there.

## Design

The design is in `docs/proposals/`: nine independent proposals (`01-` to `09-`)
and the unified proposal `10-unified-proposal/Leant2.pdf` that consolidates
them. The implementation below follows the unified proposal; section numbers
in the source comments refer to it.

## Implementation status

Lean 4.34.0, core only (no Mathlib). `lake build` builds the library, the
tests, and the `leant2` REPL executable.

- `Leant2/Search/Core.lean`: continuation-backtracking search over
  obligations with per-goal depth, deferral of type and open holes, the rule
  set (introduction, invertible destructuring, exact locals, instance
  resolution, projections as heads, constructors, local application, forward
  application, case splits, head- and demand-filtered providers, a proof
  portfolio on closed propositions, classical splits).
- `Leant2/Accept/Gate.lean`: the acceptance gate: universe generalization,
  synchronous kernel check, axiom audit against a trust profile.
- `Leant2/Engine.lean`: the adaptive lanes under one wall-clock budget
  (constructive, refutation, deeper constructive, classical, deeper
  refutation). There are no engine switches and no user settings.
- `Leant2/Frontend/Command.lean`: `#leant2 T`, `#leant2 f : T where P`,
  `#leant2_check`, `#leant2_none`; results are bound as `it1`, `it2`, ...
- `Main.lean`: the compatibility REPL that consumes Leant transcripts
  (`:synth`, `:set` ignored, `:reset`, `:prove`, declarations, `#eval`).

### The baseline

The minimal acceptance baseline is Leant's `:synth` golden corpus
(`C:\Leant\test\synth-*.txt`), scored by outcome category rather than by
transcript text (unified proposal, Definition 1.5):

```bash
lake build
python tools/run_baseline.py --budget 10000
```

The harness runs every transcript through the REPL, writes the outputs to
`baseline-out/`, and prints per-fixture scores and a total.

