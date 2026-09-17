# Leant2: architecture, algorithms, and checked prototypes

The main deliverable is **Leant2_Architecture.pdf**, with its self-contained
LaTeX source in **Leant2_Architecture.tex**. The article designs a Lean-only
successor to Leant and Djex around exact dependent types, a contract-carrying
obligation graph, transactional Lean state, recursive schemas, and a separate
acceptance boundary.

This is an architecture proposal with small checked foundations, **not a
complete implementation of Leant2**. The proposed `synth_def` syntax and most
module interfaces in the article are design sketches. The `leant2_core` and
`synth_bool` prototypes in the source files are actually implemented.

## Contents

- `lean/NativeSearch.lean`: Lean-native bounded search using actual Lean goals,
  applications, constructors, and case analysis. Eleven synthesized definitions,
  five explicit specification theorems, three rejection controls.
- `lean/FiniteCegis.lean`: 208-candidate finite circuit grammar and CEGIS for all
  16 two-input Boolean truth tables; universal correctness and success theorems.
- `lean/CertifiedFold.lean`: supplied certified-recursion constructions,
  function-valued indexing fold, universal correctness, and two exact
  noninhabitation proofs. This file does **not** autonomously discover recursion.
- `receipts/`: hand-transcribed summaries of the final remote responses, two
  initial-failure summaries, and offline replay-validator test output.
- `tools/replay_axle.py`: standard-library-only Python client for fresh checks;
  saves complete new HTTP responses and audits expected axiom inventories.
- `tools/check_local.sh`: local checking commands for a Lean installation.
- `tools/build_pdf.sh`: rebuilds the PDF with pdfLaTeX.
- `tools/test_replay_validation.py`: offline tests of the replay validator, not
  Lean execution.
- `lean-toolchain`, `lakefile.toml`: minimal pinned Lean 4.34.0 project files,
  with no Mathlib dependency.

## What was actually checked

All three final Lean source files were compiled remotely through the Wolfram
connector against AXLE environment `lean-4.34.0`, with `ignore_imports=false`
and `theorems_only=false`. The actual source uses `import Lean`. All final checks
reported `okay=true`, no failed declarations, no Lean errors, and no service
errors. Source echoes matched after trimming boundary whitespace. Each file
reported Lean version 4.34.0.

The native vector-head output depends on `propext`; the other twelve printed
inventories in that file are empty. The finite verifier theorem and its two
uniform success/correctness theorems depend on `propext`; the emitted XOR program
and its specialized theorem have empty inventories. All six inventories printed
in CertifiedFold are empty. No successful final inventory contains `sorryAx`.
The finite proofs use ordinary `decide`, not `native_decide`.

The remote service recommended its default Mathlib header, but did not replace
the submitted imports. The native rejection controls also produced expected
unused-tactic linter warnings. There was **no local Lean run and no independent
checker run**. Whole-file remote timings are not synthesis benchmark results.

The summaries in `receipts/` are manually transcribed from the actual returned
fields; they are not raw or signed service receipts. Fresh raw receipts can be
obtained with the supplied replay client in a network-enabled environment.
The client itself was syntax-checked and its validation logic was tested offline;
it was not used for the original remote calls, which used Wolfram URLRead.

## Reproduce

With the pinned toolchain installed:

```sh
bash tools/check_local.sh
```

Equivalently, run `lake env lean` on each source file. These scripts and minimal
Lake project files are supplied for reproduction; the original environment had
no local Lean/Lake installation, so that local workflow was not exercised here.

For remote checking (Python 3.9+, network access):

```sh
python tools/replay_axle.py --output fresh-receipts
```

Use a new output directory on each run. The client submits all three full source
files to AXLE, so review the source before sending project-private modifications.
It checks the exact expected axiom sets; intentional changes to proofs may require
reviewing and updating those expectations. Service availability can change.
An optional AXLE_API_KEY environment variable is supported.

To rebuild the article:

```sh
bash tools/build_pdf.sh
```

The TeX preamble lists the required standard packages (including Latin Modern,
TikZ, listings, booktabs, longtable, hyperref, and xurl). Bibliography entries are
included directly in the TeX file; no separate BibTeX run is necessary.

## Repository basis

Reviewed on September 17, 2026:

- Leant: `6bf05ad78c467989e68290f2d08bbed40802d485`
- Djex: `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`

The article acknowledges the existing Lean-rewrite analysis and current
rank-N/evidence work, rather than presenting those ideas as new. It develops the
additional dependent synthesis, contract, recursion, and scheduling mechanisms.

## Scope

The Boolean experiment is a tiny complete finite problem. The native examples
are deliberately small and several constraints strongly determine the witness.
The recursion experiment checks supplied schemas rather than discovering them.
None of these establishes a practical coverage percentage or superiority over
Leant, Djex, or other tools. Initial failures are reported separately and are not
counted as successful experiments.
