# Leant2: Answers to the Questions for Experts

Technical research report, 21 September 2026.

## Contents

- `leant2-expert-answers.pdf`: compiled report.
- `leant2-expert-answers.tex`: complete, standalone LaTeX article, including its bibliography.
- `experiments/check_constructions.py`: deterministic Python 3.9+ finite checks.
- `experiments/results.json`: results from the executed checks.

The article individually answers all 31 expert questions in R1–R9 of
`docs/proposals/11-further-improvements` at Leant2 commit
`784664ff34e819422510a4d470ab07fe48bb736b`.

## Build

From this directory, with TeX Live installed:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error leant2-expert-answers.tex
```

The bibliography is included in the LaTeX source. No BibTeX/Biber invocation,
remote resources, or external graphics are needed. Without latexmk, run
pdflatex repeatedly until the table of contents and references stabilize.

Run the finite checks with:

```sh
python experiments/check_constructions.py
```

The script overwrites `experiments/results.json` with deterministic results.
It has no external Python dependencies or network calls.

## Validation and scope

The PDF was compiled and rendered for visual inspection. The Python assertions
were executed and all passed. The investigation used primary literature,
selected repository source inspection, and official Lean documentation/source.

The mathematical arguments are not machine-checked Lean proofs. No new Lean
implementation was compiled and no Leant2 synthesis benchmark was rerun in this
environment. The report labels proposed engineering work and does not claim
measured performance improvements or model accuracy.

Exact Lean integration points were inspected at tag v4.34.0; moving latest
reference-manual links are separately identified. The bibliography contains
source URLs and version/snapshot details.
