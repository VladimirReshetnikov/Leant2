#!/usr/bin/env bash
# Requires the pinned Lean/Lake toolchain. The original run used remote Lean.
set -euo pipefail
cd "$(dirname "$0")/.."
for source in lean/NativeSearch.lean lean/FiniteCegis.lean lean/CertifiedFold.lean; do
  printf '\nChecking %s\n' "$source"
  lake env lean "$source"
done
