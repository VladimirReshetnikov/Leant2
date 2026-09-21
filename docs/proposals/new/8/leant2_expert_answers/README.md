# Leant2: Answers to the Questions for Experts

Research review prepared for Vladimir Reshetnikov, 21 September 2026.

## Contents

- `article.pdf`: the complete article, with answers to all 31 expert questions,
  proofs and counterexamples, 35 references, an implementation plan, and a
  page-by-page question cross-reference.
- `article.tex`: self-contained LaTeX source, including the bibliography.
- `model_checks.py`: deterministic, standard-library-only finite model checks.
- `model_checks.json`: the actual output of those checks.
- `Makefile`: rebuild and check commands.

## Review scope

Main repository: https://github.com/VladimirReshetnikov/Leant2

Pinned revision: `784664ff34e819422510a4d470ab07fe48bb736b`

Primary proposal: `docs/proposals/11-further-improvements`, especially the
R1–R9 sections and their 31 numbered expert questions. `12-ranking.tex`
contains both R8 and R9. The implementation comparison uses
`Leant2/Engine.lean` and `Leant2/Accept/Gate.lean`. The repository toolchain
specifies `leanprover/lean4:v4.34.0`. The actual library-suggestion API in that
Lean version was also read.

## What was and was not executed

The PDF was compiled and visually inspected. The Python model checks were run.
They include an exhaustive small finite-state synthesis experiment, a
counterexample-refinement step, and countermodels for invalid shortcuts in
search and caching.

No Lean compiler was available in the working environment. Therefore no
Leant2 build, Lean proof replay, engine benchmark, or model-proposal accuracy
experiment is claimed. Pseudocode in the article is architectural, not a
compiled patch. Mathematical propositions include paper proofs; they have not
been formally verified here.

The finite-state experiment deliberately records that the first minimum-state
sample-consistent machine overfits. Adding the first counterexample yields the
intended four-state machine. The JSON retains both machines and both search
ledgers rather than treating sample fit as full correctness.

## Rebuild

A standard TeX Live installation with New PX, microtype, hyperref, listings,
longtable, titlesec, and related packages is sufficient:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Or run `pdflatex article.tex` repeatedly until the cross-references stabilize.
No separate BibTeX/Biber step is needed. No network access is needed after the
TeX packages are installed.

To regenerate the finite checks, using Python 3.10 or newer:

```sh
python3 model_checks.py
```

Alternatively:

```sh
make
make check
```

The model checks use no external packages, services, random seeds, or timing
measurements. Explicit checks remain active even with `python -O`.

## Interpreting the article

Existing research, inspected implementation details, mathematical deductions,
and proposed experiments are identified separately. The article does not
claim a general decision procedure for Lean synthesis or an empirically
validated rewrite. References to live documentation and auxiliary project
READMEs are dated; principal repository and API references are pinned.
