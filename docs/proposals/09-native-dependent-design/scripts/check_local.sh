#!/usr/bin/env bash
# Requires an installed Lean 4.34.0 toolchain. No Mathlib dependency.
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v lean >/dev/null 2>&1; then
  echo 'Lean is not installed or is not on PATH.' >&2
  exit 2
fi
version="$(lean --version)"
printf '%s\n' "$version"
if [[ "$version" != *'version 4.34.0'* ]]; then
  echo 'Expected Lean 4.34.0; the archive lean-toolchain selects that version.' >&2
  exit 2
fi
lean prototype/NativeSearch.lean
lean prototype/FiniteCEGIS.lean
