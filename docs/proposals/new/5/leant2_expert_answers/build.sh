#!/bin/sh
# Build all cross-references without requiring latexmk or BibTeX.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'pdflatex is required. Install a TeX distribution first.' >&2
    exit 1
fi
mkdir -p .build
pass=1
while [ "$pass" -le 3 ]; do
    pdflatex -interaction=nonstopmode -halt-on-error \
        -output-directory=.build leant2_expert_answers.tex \
        > ".build/pass-$pass.log" 2>&1 || {
            cat ".build/pass-$pass.log" >&2
            exit 1
        }
    pass=$((pass + 1))
done
cp .build/leant2_expert_answers.pdf leant2_expert_answers.pdf
printf '%s\n' 'Built leant2_expert_answers.pdf'
