# Leant2: Native Dependent Program Synthesis in Lean

A comprehensive architecture and algorithms proposal, with a small compiled Lean-native prototype and a reproducible semantic-domain experiment. Prepared September 17, 2026.

## Start here

Read `article/leant2.pdf`. The main LaTeX source is `article/leant2.tex`; all included source files are in the same directory. The article is 39 pages, including front matter, appendices, and references.

The design uses exact Lean expressions and contextual types, shared backtracking across program and proof obligations, demand-driven provider application, dependent elimination, termination-aware recursion templates, proof-producing contract domains, and a separate acceptance transaction. It does not claim to decide arbitrary Lean inhabitation or to have implemented the entire proposed system.

## Contents

- `article/`: compiled article and complete LaTeX source tree.
- `prototype/Combined.lean`: the exact standalone source of the final successful native Lean run.
- `prototype/NativeCore.lean`, `prototype/DependentExamples.lean`: modular view of the prototype; the latter imports the former. This modular build arrangement was not separately run here.
- `experiments/run_experiments.py`: deterministic, standard-library-only affine-fold synthesis experiment.
- `experiments/CertificatePrelude.lean`: an intentionally open namespace fragment consumed by the generator, not a standalone Lean module.
- `experiments/Certificates.lean`: generated, self-contained generic certificate plus 27 universal contract theorems.
- `experiments/results.json`: candidate parameters, counterexamples, certificate equations, traces, and summary counts.
- `experiments/receipts/`: normalized transcriptions of actual remote-check outcomes, including initial failures and repairs. These are not raw HTTP captures.
- `experiments/negative_controls/`: deliberately invalid or inadmissible sources. Do not import them into positive builds.
- `experiments/check_axle.py`: optional standard-library HTTP client for reruns, with raw response retention and a conservative response audit.
- `experiments/test_response_audit.py`: 14 offline unit tests of the client audit logic. These are not Lean proof checks.
- `design/IMPLEMENTATION_CHECKLIST.md`: implementation gates and important prototype limitations.

## What was actually checked

### Native Lean prototype

The final standalone file was checked remotely with AXLE, using Wolfram as the HTTP transport. The requested and reported environment was `lean-4.34.0`; imports were retained and definitions were checked, not just theorems. The service echoed the submitted source unchanged modulo final whitespace.

The corpus contains 14 fully synthesized definitions, two definitions with manually supplied structural/case templates and synthesized branches, and four audited theorems. Nineteen of the 20 audited declarations have no axioms. The vector-map behavior theorem uses only `propext`. Evaluations returned 13 for the synthesized successor at 12, 1 for the constrained natural witness, 9 for the right-payload contract, and `[3, 4]` for vector mapping.

The successful run has two harmless linter warnings and service advisories about the nondefault `import Lean` header; the receipt records them. It has no Lean errors or failed declarations.

**Important limitation:** vector-map recursion discovery was not implemented. A structural match and smaller recursive call were supplied. An earlier recursor-form implementation type-checked without axioms but failed code generation. That failed run is preserved and was not accepted.

### Affine-fold experiment

The grammar contains 81 coefficient tuples and the specification set contains 27 targets. All 27 targets were solved. Certificate attempts decreased from 1,104 for the ordered baseline to 105 with a counterexample bank. These are operation counts, not runtime measurements or comparisons against Leant or Djex.

The experiment exhaustively cross-checks 2,187 candidate/specification pairs and separately runs 29,511 held-out evaluations. The generic inductive certificate and all 27 generated universal contracts were remotely checked in Lean. Each reported only `propext` and `Quot.sound`; there were no errors, failed declarations, or warnings. Universal correctness comes from these proofs, not from the held-out tests.

The article proves that five particular lists form an exact separator family for the affine schema. The Lean file formalizes the sufficient certificate theorem; the unrestricted necessity/separation argument is written mathematically in the article and is not formalized in the supplied Lean file.

### Negative checks and assurance scope

Four separate sources tested an invalid False proof, an incorrect behavioral equality, a custom axiom, and `sorry`. All were rejected by the stated policy. The last two returned `okay=true`, illustrating why that field alone is insufficient.

No local Lean compiler was available. No independent external kernel checker was run. The remote service reported its executor identity but did not expose an exact Mathlib commit. The receipts state these limits. The optional Python client was tested locally only at the response-audit level; actual HTTP checks in this session used Wolfram.

## Reproduce the Python work

Python 3.10 or later; no third-party packages:

```sh
python3 experiments/run_experiments.py
(cd experiments && python3 -m unittest -v test_response_audit)
```

The first command regenerates `results.json` and `Certificates.lean`. Run without Python's `-O` switch, because implementation cross-checks use assertions.

## Recheck the Lean source locally

With Lean 4.34.0 available, the standalone native file needs only Lean's own libraries:

```sh
cd prototype
lean Combined.lean
```

For the modular view, a typical command sequence is:

```sh
lean -o NativeCore.olean NativeCore.lean
LEAN_PATH=. lean DependentExamples.lean
```

The modular commands are provided as a build arrangement, not reported as executed here. The standalone file is the remotely tested artifact. `prototype/lean-toolchain` pins Lean 4.34.0 for Elan-based setups.

The affine theorem file requires a compatible Mathlib project. From such a project, use `lake env lean` with the path to `experiments/Certificates.lean`. There is no invented Mathlib revision pin in this archive; use a documented compatible checkout and retain its manifest for a new fully pinned run.

## Optional remote recheck

These commands submit the named source to AXLE. They require network access and send code to a third-party checking service. The client preserves imports, checks definitions, refuses to overwrite an existing output receipt, and stores the complete returned JSON.

```sh
python3 experiments/check_axle.py prototype/Combined.lean \
  --manifest experiments/native_audit.json --output native-rerun.json

python3 experiments/check_axle.py experiments/Certificates.lean \
  --manifest experiments/affine_audit.json --output affine-rerun.json
```

An API key can be supplied through `AXLE_API_KEY` when required. Service availability and supported environments may change. The client's log parsing assumes honest source, logs, and service behavior; it is not a sandbox or an independent kernel implementation. It audits only declarations named in the supplied manifest.

## Rebuild the article

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error leant2.tex
```

The PDF was compiled and visually inspected. No font files, compiled Lean caches, or external repository snapshots are bundled.

## Reviewed repository versions

Leant: `6bf05ad78c467989e68290f2d08bbed40802d485`.
Djex dependency: `e237e8667190aff38faaa590ce5b12afbffac452`.
The article's source map identifies the specific files and ranges reviewed. Historical repository success counts were not rerun or presented as new measurements.
