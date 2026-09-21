# Answering the Expert Questions for Leant2

Research report prepared for Vladimir Reshetnikov, September 21, 2026.

The article answers all 31 enumerated expert questions in R1–R9 of
`docs/proposals/11-further-improvements/`, using the Leant2 snapshot
`784664ff34e819422510a4d470ab07fe48bb736b` and Lean 4.34.0 documentation/source.

## Contents

- `Leant2_Expert_Answers.pdf`: the 34-page report, including its title page,
  contents, question crosswalk, source audit, and 23 bibliography entries.
- `Leant2_Expert_Answers.tex`: self-contained LaTeX source; bibliography included.
- `source_manifest.json`: snapshot, inspected source locations, question mapping,
  and validation scope.
- `experiments/check_claims.py`: deterministic, standard-library Python checks.
- `experiments/results.json`: the recorded experiment output.
- `build.sh`: PDF build helper for a Unix-like environment with pdfLaTeX.

## Build the document

A normal TeX Live or MiKTeX installation with the packages named in the source
is sufficient. No external images, separate bibliography database, downloaded
fonts, or shell-escape execution are needed.

Run `sh build.sh`, or run the following command three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error Leant2_Expert_Answers.tex
```

Multiple passes resolve the contents and cross-references. PDF byte identity
is not promised across TeX versions or builds (for example, PDF timestamps vary).

## Reproduce the finite experiment

Python 3.10 or later, with no third-party packages:

```sh
python3 experiments/check_claims.py --output experiments/results.json
```

The script exhausts the 2 one-state, 128 two-state, and 17,496 three-state
right-fold machines for a nine-observation Boolean task, finding none that fit.
The article proves a four-state lower bound and an all-input four-state
realization. The script additionally tests the realization on 2,047 binary
words and the direct reverse fold on 3,280 ternary words, and checks several
small hazard witnesses. These are finite mathematical sanity checks, not a
Leant2 implementation or performance benchmark.

## Evidence and limitations

The PDF was compiled and visually inspected. The experiment was executed.
The Lean code and proposal files were inspected through the GitHub connector;
research claims were checked against primary papers and official documentation.

No Lean compiler was available in the report's execution environment. No Lean
snippet was compiled, proposed adapter executed, or repository benchmark rerun.
Pseudocode is an algorithmic design, not tested implementation code. Source
benchmark claims are explicitly separated from the report's own experiment.
Existing results, mathematical arguments, proposed adaptations, and unmeasured
hypotheses are identified separately in the article.

The report does not claim that all discussed mechanisms are implemented, that
all proof obligations are decidable, or that finite tests establish universal
contracts. No upstream repository files were modified.
