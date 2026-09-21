#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
command -v pdflatex >/dev/null 2>&1 || { echo "pdflatex is required" >&2; exit 1; }
if command -v python3 >/dev/null 2>&1; then
  PYTHON=python3
elif command -v python >/dev/null 2>&1; then
  PYTHON=python
else
  echo "Python 3.10 or later is required" >&2
  exit 1
fi
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
"$PYTHON" sanity_checks.py --output sanity_results.json
