#!/bin/sh
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
    printf '%s\n' 'pdfLaTeX is required (install TeX Live or MiKTeX).' >&2
    exit 1
fi
for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error Leant2_Expert_Answers.tex
done
