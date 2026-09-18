# Leant2: Native Dependent Program Synthesis in Lean

Detailed architecture and algorithm proposal, dated September 17, 2026.

Read `article/Leant2.pdf`. The editable master is `article/Leant2.tex`, with
section sources under `article/sections/`.

## Included artifacts

- `prototype/NativeSearch.lean`: an actually checked Lean-native bounded search
  prototype. It exercises dependent types, higher-rank callbacks, shared-goal
  backtracking, and supplied recursive sketches.
- `prototype/FiniteCEGIS.lean`: an actually checked Lean implementation of finite
  Boolean counterexample-guided synthesis, with a universal correctness theorem.
- `scripts/`: local Lean runner, exact-source remote-check wrapper, independent
  Python enumeration, and receipt-validator unit tests.
- `evidence/`: actual run summaries, source identities, Python results,
  repository snapshot metadata, and explicitly marked failed experimental sources.
- `tools/user-provided/`: unchanged AXLE clients and documentation from the user's
  uploaded archive. These are included for convenience and attribution, not
  presented as newly written tools.

## Main recommendation

Use native Lean expressions, universes, contexts, and metavariable constraints
as semantic authority. Search over a transactional **whole goal forest** so that
a later proof obligation can backtrack over an earlier implementation choice.
Add component retrieval, recursive-sketch generation, contract decomposition,
and specialized finite/solver lanes behind one checking and publication gate.
Keep typing, behavioral proof, and executability as separate result guarantees.

This archive does **not** contain a complete implementation of that architecture.
All proposed production syntax and APIs in the article are labeled as proposals.
The two Lean experiments are narrow, runnable mechanism tests. Their recursive
skeletons are supplied rather than automatically discovered.

## Results actually obtained

Both final Lean files compiled remotely in Lean 4.34.0 with their own `import
Lean` headers preserved. Across 29 explicit declaration audits, 28 inventories
were empty; indexed `vectorHead` used only `propext`. No final declaration used
`sorryAx`.

The finite search considered a 9168-term grammar through eight nodes. It found
XOR after five proposals and four counterexamples, then proved the full Boolean
specification. The independent Python script reproduced the trace and counts.

Read `evidence/EXPERIMENTS.md` for limitations, warnings, failed versions, request
IDs, and the distinction between transcribed summaries and fresh HTTP receipts.
There was no local Lean toolchain and no execution/benchmarking of Leant or Djex.

## Reproduction

With Lean 4.34.0 installed:

```sh
./scripts/check_local.sh
```

Independent finite-grammar calculation and receipt-wrapper tests:

```sh
python3 scripts/finite_reference.py
python3 -m unittest discover -s scripts -p 'test_*.py' -v
```

With network access to AXLE:

```sh
python3 scripts/check_remote.py prototype/NativeSearch.lean
python3 scripts/check_remote.py prototype/FiniteCEGIS.lean
```

The remote wrapper submits the source unchanged, checks every printed axiom
inventory, rejects source substitution and incomplete declarations, and writes
a new full-response receipt. It permits only `propext` by default. The service
is external; availability and future toolchain compatibility are not guaranteed.

Build the PDF with an ordinary TeX Live installation:

```sh
make article
```

The article bibliography pins repository observations. It distinguishes current
repository snapshots from Leant's separately documented vendored Djex pin.
