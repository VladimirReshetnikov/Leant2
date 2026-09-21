# Leant2: answers to the expert questions

**From Expert Questions to a Verifiable Search Architecture**
Research report, 21 September 2026. 37 pages.

## Contents

- `leant2_expert_answers.pdf`: compiled article.
- `leant2_expert_answers.tex`: self-contained LaTeX source; bibliography is embedded.
- `semantic_checks.py`: Python 3.9+ finite semantic checks, standard library only.
- `semantic_results.json`: recorded successful output of those checks.
- `source_manifest.json`: snapshot, question coverage, inspected native API files,
  reference links, and evidence limitations.
- `SHA256SUMS.txt`: checksums of the other package files.

The report addresses all 31 questions in R1–R9. The final question index maps
each identifier to its answer page.

## Rebuild the PDF

With TeX Live or another suitably complete LaTeX installation:

```text
pdflatex -interaction=nonstopmode -halt-on-error leant2_expert_answers.tex
pdflatex -interaction=nonstopmode -halt-on-error leant2_expert_answers.tex
```

Alternatively: `latexmk -pdf leant2_expert_answers.tex`.
The package uses newpxtext/newpxmath and the other packages named in the preamble.
No separate bibliography processor or source images are needed.

## Reproduce the semantic checks

```text
python semantic_checks.py
```

The script prints JSON and writes `semantic_results.json` beside itself.
Assertions fail with a nonzero exit status. Do not run Python with `-O`,
which disables assertions.

## Scope and verification

Repository snapshot: `784664ff34e819422510a4d470ab07fe48bb736b`.
Inspected Lean toolchain: `leanprover/lean4:v4.34.0`.

The PDF was compiled successfully, checked for unresolved references and
layout overflow warnings, and visually inspected. The finite Python checks
were executed successfully. They cover two reverse representations, optional
min/max, Fibonacci tupling, a three-state finite observer, partial observation
compatibility, a non-congruence example, and illustrative cache/heuristic
countermodels.

**No Lean executable was available.** No proposed Lean interface was compiled,
no Leant2 benchmark suite was rerun, and no model accuracy study was performed.
The article's proofs are written arguments, not machine-checked Lean proofs.
The architecture is a proposed implementation plan, not a repository patch.
Reported repository benchmark figures are attributed to the original proposal.

This package does not include third-party papers or repository source snapshots.
The bibliography and source manifest provide their references.
