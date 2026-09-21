# Leant2: Answers to the Expert Questions

Research and design assessment prepared for Vladimir Reshetnikov.
Date: September 21, 2026.

## Contents

- `article.pdf`: the complete article.
- `article.tex`: main LaTeX source.
- `sections/`: the article's section sources, including all 31 individually numbered answers, the implementation roadmap, evaluation plan, and coverage/source-audit appendices.
- `references.tex`: embedded bibliography; BibTeX is not required.
- `checks/check_models.py`: reproducible finite mathematical checks (Python 3.9+, standard library only).
- `checks/results.json`: output from the executed checks.
- `provenance.json`: repository/version identifiers and the verification boundary.

## Build the PDF

Run from this directory with a recent TeX Live or MiKTeX installation:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three times.
The source uses ordinary TeX-distribution packages including newtxtext/newtxmath,
amsmath/amsthm, microtype, geometry, longtable, listings, hyperref, cleveref, and xurl.
No network access, external graphics, shell escape, or separately supplied font files are needed.

## Run the finite checks

```text
python checks/check_models.py --output checks/results.json
```

Run without Python's `-O` flag: the checks use assertions. All 11 checks passed
in the article preparation run. The suite includes an exhaustive exclusion of
one- and two-state fold machines for a 31-observation Boolean-output task, a
three-state witness, reversal and Fibonacci examples, and small countermodels
for several tempting but invalid guarantees.

## Evidence and limitations

Repository analysis is pinned to Leant2 commit:
`784664ff34e819422510a4d470ab07fe48bb736b`.

The proposal's reported benchmark/profile results belong to its own recorded
runs, including measured commit `33cec8b`. They were not reproduced here.
Selected Lean implementation APIs were read at tag `v4.34.0`; moving official
manual pages are identified separately in the article.

The article contains written mathematical proofs and proposed algorithms.
There is no new Lean implementation or Lean-checked formalization in this
package. The Python checks are not tests of Lean or Leant2. Performance gains
and exact model accuracy on Leant2's carrier/helper tasks are research questions,
not measured claims. All included Lean-like interface listings are design
pseudocode, not promised drop-in code.

Published papers and external source code retain their own licenses. This
package does not redistribute their full text, repository code, or font files.
