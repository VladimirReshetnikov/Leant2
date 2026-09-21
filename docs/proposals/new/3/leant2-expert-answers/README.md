# Answers to Leant2's Expert Questions

**From Open Questions to a Verifiable Synthesis Architecture**
Research and design review prepared September 21, 2026.

## Scope

Answers all 31 numbered questions in R1–R9 of
`docs/proposals/11-further-improvements` in VladimirReshetnikov/Leant2,
inspected at commit `784664ff34e819422510a4d470ab07fe48bb736b`.

The report includes source-specific integration recommendations, mathematical
arguments, literature corrections, a staged implementation plan, an explicit
question-to-answer index, and six executable finite-model checks.

## Contents

- `article.pdf`: compiled article.
- `article.tex`: main LaTeX source.
- `sections/*.tex`: complete editable section sources.
- `references.tex`: included bibliography, with primary-source links.
- `validate_models.py`: standard-library Python checks.
- `model_results.json`: actual results from executing those checks.

## Build the article

A standard TeX Live installation with the packages used in `article.tex` is
required. From this directory, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

No BibTeX invocation or internet connection is required. Keep the `sections`
directory and `references.tex` next to the main source when compiling.

## Reproduce the finite-model checks

Python 3.10 or later is sufficient; no third-party modules are required.

```sh
python3 validate_models.py
```

The script asserts all six check families and regenerates `model_results.json`.
These are finite Python models, NOT Lean proofs or Leant2 benchmarks.

## Evidence and limitations

No Lean executable was available during preparation. No proposed Lean interface
was compiled, no Leant2 performance benchmark was rerun, and no repository source
was changed. Historical benchmark numbers in the article are attributed to the
proposal. New algorithms and interfaces are recommendations, not implemented
features. The mathematical arguments are English proofs with stated assumptions,
not machine-checked formalizations. Model-accuracy and speedup figures have not
been invented.

The source review distinguishes the Leant2 snapshot, selected Lean v4.34.0 source
files, and the rolling Lean reference as accessed on September 21, 2026.
