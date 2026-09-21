# Leant2: Answers to the Expert Questions in Proposal 11

Prepared for Vladimir Reshetnikov, 21 September 2026.

## Main deliverables

- `leant2_expert_answers.pdf`: the complete article.
- `leant2_expert_answers.tex`: main LaTeX source.
- `sections/*.tex`: all article sections and appendices.
- `references.tex`: the inline, linked bibliography (no BibTeX dependency).

The article gives individually numbered answers to all 31 expert questions
in R1–R9 of `docs/proposals/11-further-improvements` and includes a source
cross-reference, mathematical arguments, implementation recommendations,
a staged roadmap, and an evaluation plan.

## Source/version boundary

Repository: https://github.com/VladimirReshetnikov/Leant2
Pinned commit: 784664ff34e819422510a4d470ab07fe48bb736b
Repository toolchain: leanprover/lean4:v4.34.0
Review date: 2026-09-21

The proposal's historical measurements concern commit 33cec8b. They were
not reproduced in this review. The repository inspection was selective
source analysis, not a full security audit. No Lean compiler was available
in the execution environment; no new Lean implementation, build success,
or Leant2 performance improvement is claimed. Pseudocode is labelled as
proposed rather than compiler-tested Lean code.

The mathematical results are proved in the article. They are not claimed
to be mechanized proofs or wholly new literature results. New implementation
choices are distinguished from established sources and empirical unknowns.

## Build the PDF

Use a TeX Live or MiKTeX installation with `pdflatex` and the packages named
in the preamble, including newpx, microtype, amsmath/amsthm, mathtools,
booktabs, longtable, array, tabularx, enumitem, listings, fancyhdr, needspace,
hyperref, and cleveref.

On a shell supporting POSIX sh:

```sh
./build.sh
```

On other systems, run this command three times from this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error leant2_expert_answers.tex
```

The sources need no downloaded figures, external bibliography processor,
network calls, or bundled font files. Fonts are resolved by the installed
TeX distribution.

## Reproduce the finite checks

With Python 3.10 or later:

```sh
python3 checks/check_design_examples.py
```

This regenerates `checks/results.json` and checks finite mathematical models,
not Lean programs or engine performance. In particular, it exhausts 5,898
one-, two-, and three-state transition/output tables against 15 observations,
finds no matching carrier, and checks an explicit four-state realization.
It also checks the reversal constructions and several small counterexamples
used to motivate safe search and caching.

No third-party Python packages are needed. The exhaustive finite experiments
are supplementary checks, not a substitute for the general proofs.

## Reproducibility metadata

`provenance.json` records the repository/toolchain/review boundary and the
validation performed for the delivered document. `SHA256SUMS` records the
packaged file contents. PDF regeneration may change timestamps and hence the
PDF hash, even when the article text and layout are unchanged.
