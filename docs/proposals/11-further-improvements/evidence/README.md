# Preserved expert-proposal model evidence

The directories `N1` through `N9` preserve the distinct executable model checks
and their original receipts from the nine incoming expert-answer packages.
The prose and repeated architectural material are being integrated into the
maintained article, rather than retained as nine competing articles.

These files are copied from the original Git blobs without rewriting their
contents. Historical source manifests, checksums and validation reports refer
to the **original packages**, including their original PDFs and source paths.
They are not checksums or validation reports for this consolidated article.
The complete original packages remain recoverable at revision
`5c3a53c22c18e6acd8ff17eb0902ce4da354518a`; the
[source inventory](../integration/sources.json) records every original path,
Git blob, SHA-256 and integration disposition. It separately records checkout
bytes where Git's line-ending conversion differed from the original blob.

The nine scripts exercise finite mathematical models, counterexamples and
bounded constructions. They do not run Lean or Leant2, establish a general
conservativity theorem, or measure synthesis performance. Repeated examples
in independently authored scripts are retained as historical executable
evidence; they must not be counted as independent algorithmic discoveries.

Run all suites in fresh copies, preserving the historical receipts:

```powershell
python -B tools/check_proposal_models.py --out baseline-out/proposal-models
```

Run from the repository root with ordinary Python (not `-O`, because the suites
use assertions). The runner preserves raw stdout, stderr and process receipts,
requires equality with each archived JSON result, and checks that these source
evidence directories remain unchanged. Its output directory must be new.

The [September 22 rerun](rerun-2026-09-22/receipt.json) passed all nine suites:
every process exited zero with empty stderr, every JSON result matched its
archived value, and all original evidence hashes remained unchanged. The same
directory preserves the raw stdout and stderr of each process.
