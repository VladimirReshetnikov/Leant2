#!/usr/bin/env bash
# Requires pdflatex and the packages listed in the article preamble.
set -euo pipefail
cd "$(dirname "$0")/.."
build_dir="$(mktemp -d)"
trap 'rm -rf "$build_dir"' EXIT
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory="$build_dir" Leant2_Architecture.tex >"$build_dir/pass-$pass.log" 2>&1 || {
      cat "$build_dir/pass-$pass.log" >&2
      exit 1
    }
done
cp "$build_dir/Leant2_Architecture.pdf" Leant2_Architecture.pdf
printf 'Built Leant2_Architecture.pdf\n'
