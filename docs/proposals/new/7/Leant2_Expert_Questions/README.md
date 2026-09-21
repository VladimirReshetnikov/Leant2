# Answers to Leant2's 31 Expert Questions

**From improvement proposals to a trustworthy synthesis architecture**  
Research report prepared for Vladimir Reshetnikov, 21 September 2026.

## Read the report

`article.pdf` is the 42-page finished report. `article.tex` is its self-contained
LaTeX source, including the bibliography. The report answers all 31 expert
questions in the nine R1–R9 research themes, reviews relevant implementation
code, gives mathematical arguments and counterexamples, and proposes a staged
implementation and evaluation plan.

The reviewed repository snapshot is:

- Repository: https://github.com/VladimirReshetnikov/Leant2
- Commit: `784664ff34e819422510a4d470ab07fe48bb736b`
- Proposal: `docs/proposals/11-further-improvements/`
- Pinned Lean toolchain: `leanprover/lean4:v4.34.0`

## Bundle contents

- `article.pdf`: compiled, visually inspected article.
- `article.tex`: complete source with an internal bibliography; no BibTeX needed.
- `question_index.json`: all 31 question identifiers, answer sections/pages, and
  immutable source links. Page numbers are the printed article numbers.
- `source_manifest.json`: scope, versions, references, and validation boundaries.
- `sanity_checks.py`: independent finite-model reference checks using only Python's
  standard library.
- `sanity_results.json`: the actual deterministic output from those checks.
- `build.sh`: optional shell helper to rebuild the PDF and run the checks.

## Build

Use a TeX distribution containing the packages named in `article.tex`.
Run from this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
python3 sanity_checks.py --output sanity_results.json
```

Python 3.10 or later is sufficient. On systems where the interpreter is named
`python`, substitute that command for `python3`. Another LaTeX pass may be needed
when editing changes cross-references or pagination. `build.sh` runs three passes
and the Python checks on systems with a POSIX shell.

## What was actually checked

The finite experiment accounts for every deterministic right-fold machine with
one, two, or three labeled states over a two-letter alphabet, including every
seed, transition table, and Boolean finishing map: 2, 128, and 17,496 machines,
respectively. None satisfies the nine observations used in the article. A
four-state witness fits the observations and was also checked on all 511 words
of length at most eight. The universal sufficiency argument is proved in the
article by a state invariant, not inferred from those finite tests.

Additional checks cover a two-feature carrier proposal, nontransitive partial
observation compatibility, shared-goal lower bounds, two reverse fold
representations, consistent angelic calls, and the limits of finite-probe
candidate equivalence. All script assertions passed.

## Evidence and limitations

This is a source-grounded research/design report, not a tested implementation
patch. No Leant2 build or performance reproduction, Lean compilation of the
proposed mechanisms, model-accuracy experiment, or human-preference study was
performed. Mathematical proofs are ordinary written proofs, not Lean
formalizations. Python checks are independent reference models, not Leant2 tests.
The repository was not modified. These distinctions are stated in the article,
including where a question still calls for empirical evaluation.

Only original report and reference-check artifacts are included; no copied
third-party papers or font files are distributed.
