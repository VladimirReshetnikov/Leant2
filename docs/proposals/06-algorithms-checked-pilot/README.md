# Leant2: architecture, algorithms, and checked pilot

This archive contains a comprehensive design for a Lean-native successor to Leant and Djex. It is a design study with a small working synthesis pilot, not a finished Leant2 implementation.

## Start with the paper

`article/leant2.pdf` is the compiled paper. `article/leant2.tex` is its self-contained LaTeX source, including references. The paper covers native dependent search, correlated metavariables, library composition, recursion and motive synthesis, behavioral constraints, counterexample-guided refinement, certified pruning, executable lowering, trust boundaries, and an implementation/evaluation plan.

The repository comparison uses Leant `6bf05ad78c467989e68290f2d08bbed40802d485` and its Djex submodule pin `e237e8667190aff38faaa590ce5b12afbffac452`. The bibliography explains which inspected project documentation came from the main branch rather than the pinned source. No existing repository test suite was rerun.

## What was checked

`prototype/Leant2Pilot.lean` is the exact 133-line source checked remotely under Lean 4.34.0. It synthesizes fourteen small declarations using native Lean metaprogramming. All fourteen reported empty axiom inventories. Seven further examples check selected types or equations, and two negative controls confirm bounded search failure.

The same file contains four **hand-written**, not automatically synthesized, supporting declarations for indexed vectors and accumulator reversal. `Vec.zip` and `reverseAux_spec` reported `propext`; the other two reported no axioms.

`prototype/Certificates.lean` is also exact checked source. Three small logical certificates reported no axioms. A hand-written correspondence theorem between a recursor model and executable tree code reported `propext`. These certificates do not prove correctness of the complete proposed synthesis architecture.

`experiments/RecursorCompileProbe.expected-failure.lean` deliberately fails executable compilation in the tested environment. It demonstrates the direct-recursor/code-generator boundary. Its failure is expected and must not be included in an ordinary all-files-must-compile target.

The `*-receipt.json` files are **selected-field transcriptions of observed responses**, not complete raw responses or signed attestations. `VALIDATION.md` gives request identities, warnings, limitations, and source status.

## Local reproduction

With the Lean 4.34.0 toolchain available, run:

```sh
cd prototype
lean Leant2Pilot.lean
lean Certificates.lean
```

The `lean-toolchain` file pins `leanprover/lean4:v4.34.0`. The sources use `import Lean`; no Haskell runtime or additional package is required by their explicit imports. These commands were not run locally in the creation session: the actual checks used the remote AXLE environment through Wolfram HTTP requests.

## Remote reproduction

The standard-library-only Python client preserves the import header and saves the complete new request/response along with a conservative audit. Run from the archive root:

```sh
python tools/check_axle.py prototype/Leant2Pilot.lean \
  --axiom-profile experiments/pilot-axioms.json \
  --output experiments/pilot-new.axle.full.json

python tools/check_axle.py prototype/Certificates.lean \
  --axiom-profile experiments/certificates-axioms.json \
  --output experiments/certificates-new.axle.full.json
```

Run the separate expected-failure probe with:

```sh
python tools/check_axle.py \
  experiments/RecursorCompileProbe.expected-failure.lean \
  --expect-compiler-error "code generator does not support recursor" \
  --output experiments/recursor-new.axle.full.json
```

A `PASS` on this last command means the **specified rejection was observed**, not that the Lean file compiled. The client checks source echo integrity, compilation errors, failed declarations, warnings mentioning admitted proofs, and exact printed axiom inventories when a profile is supplied. It does not independently check Lean proof terms. Header advisories are retained rather than silently suppressed.

The client defaults to `lean-4.34.0`. Network access and the service's continued availability are required. An optional `AXLE_API_KEY` environment variable is supported but is never written to the receipt. The service may change, and it does not report an exact Mathlib revision. See its official documentation at https://axle.axiommath.ai/v1/docs/tools/check/.

## Offline client tests

```sh
cd tools
python -m unittest -v test_check_axle.py
```

All eleven response-audit tests passed locally during artifact preparation. These tests exercise the Python response checker, not the Lean synthesis engine. The network path of this new Python client was not run locally because the container had no direct network access; the recorded Lean checks used the equivalent Wolfram byte-array HTTP route.

## Rebuild the paper

A standard TeX installation with pdfLaTeX, Latin Modern, TikZ, listings, hyperref, cleveref, and the usual AMS/table packages is sufficient:

```sh
cd article
pdflatex -interaction=nonstopmode -halt-on-error leant2.tex
pdflatex -interaction=nonstopmode -halt-on-error leant2.tex
pdflatex -interaction=nonstopmode -halt-on-error leant2.tex
```

Three passes stabilize the multi-page contents and page references from a clean build. No external figures, font files, shell escape, or bibliography processor are needed.
