# Leant2: a Lean-native synthesis architecture

This package contains a 32-page architecture article, an actual Lean research
prototype, compiler receipts, and small executable algorithm experiments.
The full proposed Leant2 system is not implemented in this package.

## Read first

- `article/Leant2.pdf`: the complete article.
- `article/Leant2.tex`: self-contained LaTeX source, including its bibliography.
- `receipts/development-notes.md`: what was checked, failed attempts, fixes,
  actual axiom inventories, and environmental limitations.

The design uses exact Lean expressions, transactional whole-continuation search,
dependent elimination, explicit dictionary semantics, proof-carrying recursion,
carrier/measure search, reversible observational partitions, and checked
admission. It distinguishes implemented experiments from proposed algorithms.

## Executable artifacts

`lean/Leant2Core.lean` is a readable native tactic prototype. `lean/Tests.lean`
contains 21 synthesis examples, four expected-failure controls, and eight
additional statements. `lean/StandaloneTests.lean` combines those files.
`lean/Validation.lean` removes comments and blank lines from that combination;
it is the exact source submitted in the successful remote native compilation.

`lean/RecursionCertificates.lean` supplies a proof-carrying map scheme, an affine
fold, the universally quantified correctness theorem for the coefficients
selected by the Python experiment, and an emptiness proof. The recursion schemas
are supplied, not automatically invented by `leant2_core`.

`experiments/search_models.py` runs two small regression models: preservation of
all candidates under observational bucket refinement, and counterexample-guided
selection among 81 affine-fold sketches. `experiments/results.json` records the
executed trace. Finite observations are not mistaken for the universal Lean proof.

## Results

The native source compiled remotely in Lean 4.34.0 with all 21 synthesis examples,
all four controls, and all eight additional statements accepted. The audit
covers the 25 named synthesis/control declarations: 24 empty axiom inventories,
and only `propext` for `indexedHeadNative`.

The recursion artifact also compiled. Three of its four audited declarations
have empty axiom inventories; `sumCorrect` uses only `propext`. No accepted output
uses `sorryAx`, `Classical.choice`, or `Quot.sound`.

There was no local Lean/Lake installation. Actual checking used a Wolfram
Language HTTP client and AXLE, following the user-supplied tools. The source was
submitted with imports preserved. The API echoed one additional terminal
newline. Local and remote source hashes match. The two compact JSON receipts
retain observed messages and executor identities; they are not a claim of a
local build or a benchmark against Leant/Djex.

## Reproduce

Run commands from this directory. Python 3.10+ is sufficient for the local models
and clients; they have no third-party Python dependencies.

```sh
python tools/verify_package.py
python experiments/search_models.py
```

With Lean 4.34.0 installed (the `lean-toolchain` file pins it):

```sh
lean lean/Validation.lean
lean lean/RecursionCertificates.lean
```

For split-module development, make `lean/` a Lean module search directory or use
your usual Lake project. The standalone validation command avoids that setup.
No local Lake build was performed here and no Lake manifest is asserted tested.

Remote compilation sends the named source to AXLE:

```sh
python tools/check_lean.py lean/Validation.lean --audit-marker LEANT2_AUDIT:
python tools/check_lean.py lean/RecursionCertificates.lean --audit-marker LEANT2_RECURSION_AUDIT:
```

The Python client checks errors, incomplete declarations, sorry warnings,
per-declaration inventories, the completed audit marker, and unchanged source
apart from the observed appended newline. A future service change may correctly
cause this strict client to fail. Set `AXLE_API_KEY` when your service access
requires a key. Never put credentials in receipts.

The optional Wolfram script uses the same transport approach but has lighter
validation; use the Python client for the complete receipt checks.

```sh
cd article
latexmk -pdf Leant2.tex
```

A standard TeX Live installation with TikZ, tcolorbox, Latin Modern, and stmaryrd
builds the article. No bibliography tool or external figure asset is needed.

## Baseline and limits

The review uses Leant `6bf05ad78c467989e68290f2d08bbed40802d485` and Djex
`e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`; Leant's recorded pinned Djex
revision is `e237e866`. Existing repository design work is explicitly credited.
The original legacy indexing and two-universe benchmarks were not rerun, and no
claim of solving those original fixtures or outperforming either repository is
made. This small prototype is bounded depth-first search, not a complete solver
or the production architecture described in the article.
