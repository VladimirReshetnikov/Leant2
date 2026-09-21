# Leant2: Answers to the Expert Questions

Prepared for Vladimir Reshetnikov, 21 September 2026.

## Contents

- `leant2_expert_answers.pdf`: the 38-page research article.
- `leant2_expert_answers.tex`: self-contained LaTeX source, including its bibliography.
- `experiments/model_checks.py`: eight deterministic finite-model checks, requiring Python 3.10 or newer and no third-party packages.
- `experiments/results.json`: the recorded successful output of those checks.
- `source_manifest.json`: reviewed repository snapshot, source paths, primary references, question mapping, and evidence boundaries.

The article answers all 31 questions in research areas R1–R9 of
`docs/proposals/11-further-improvements` in the Leant2 repository. It also provides
formal arguments and counterexamples, code-level implementation recommendations,
a revised roadmap, and an experimental protocol.

## Reviewed snapshot

Repository: https://github.com/VladimirReshetnikov/Leant2

Commit: `784664ff34e819422510a4d470ab07fe48bb736b`

Repository toolchain: `leanprover/lean4:v4.34.0`

The selected Lean induction and `cbv` source interfaces were inspected at the
same Lean tag. The article distinguishes these pinned checks from descriptions
in the moving online Lean reference manual.

## Build the PDF

A normal TeX Live or MiKTeX installation with the packages named in the preamble
is sufficient. No custom fonts, images, or external bibliography files are needed.

From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error leant2_expert_answers.tex
```

Alternatively run `pdflatex` three times to resolve the table of contents and
cross-references:

```sh
pdflatex -interaction=nonstopmode -halt-on-error leant2_expert_answers.tex
pdflatex -interaction=nonstopmode -halt-on-error leant2_expert_answers.tex
pdflatex -interaction=nonstopmode -halt-on-error leant2_expert_answers.tex
```

The delivered PDF was compiled successfully, with no unresolved references or
citations and no overfull boxes, and its pages were rendered for layout review.

## Reproduce the finite checks

```sh
python3 experiments/model_checks.py --output experiments/results.json
```

On systems where the executable is named `python`, replace `python3` accordingly.
The script prints JSON and writes the same content to the given output file.
Do not use Python's `-O` option, which disables assertions.

The checks cover coupled-goal cost, a reverse fold, incomplete observation rows,
finite carrier search, rollback cache identity, bounded parametric tests,
deadline-versus-work discovery, and conjunctive provider reachability. The
carrier checks exhaust 2,392 labeled machine tables. All assertions passed.

## Evidence boundary

This is a source-based investigation with mathematical arguments and small
executable models, not an implementation or benchmark of an improved Leant2.
No Lean executable was available in the execution environment; no proposed Lean
engine changes or example programs were compiled and no repository acceptance
suite was rerun. The repository's historical benchmark measurements are clearly
identified as such. The article's propositions are not machine-checked Lean
proofs. In particular, its interpreter simulation is a proposed proof obligation,
not a delivered verified interpreter. There are no new model-accuracy figures.

The Python rollback example is a model counterexample, not a reproduced bug in
Leant2. The logical-work experiment is not a processor-speed measurement. A
finite carrier minimum applies only to its explicitly stated finite table model.
