# Leant2: architecture, algorithms, and checked experiments

This package contains a 45-page technical design for a Lean-native successor to
Leant and Djex. Start with **`article/leant2.pdf`**. The complete, independently
buildable LaTeX source is **`article/leant2.tex`**.

The proposed engine keeps exact Lean expressions, dependent typing constraints,
program holes, and behavioral proof obligations in one revisable search state.
The article develops the corresponding search rules, recursion planning,
specification propagation, proof-service interfaces, scheduling, caching,
validation, and implementation milestones. It does not describe a completed
Leant2 implementation.

## Guide to the article

Sections 3–7 specify the query contract, component boundaries, joint search state,
and native dependent refinement. Sections 8–10 develop behavioral reasoning,
recursion planning, and proof/solver integration. Sections 11–15 specify resource
policies, validation, worked traces, conditional guarantees, and implementation
interfaces. Section 16 reports the executed experiments and their limitations;
Sections 17–18 define evaluation and delivery gates. The appendices give additional
algorithms and reproduction instructions. References are included in the source;
no external bibliography database is required.

## Included artifacts

| Path | Purpose |
| --- | --- |
| `article/leant2.tex`, `article/leant2.pdf` | Complete article source and rendered PDF. |
| `prototype/Prototype.lean` | Actual tested standalone joint-goal synthesis tactic and 12 synthesized declarations. |
| `prototype/SkeletonChecks.lean` | Actual tested indexed-vector map branch completion inside a supplied recursion skeleton. |
| `prototype/ReverseCertificate.lean` | Actual tested universal correctness proof for the fold selected by the finite experiment. |
| `prototype/lean-toolchain`, `prototype/lakefile.lean` | Minimal local reproduction setup, pinned to Lean 4.34.0. |
| `experiments/cegis.py` | Finite counterexample-guided synthesis plus two semantic regression checks. |
| `experiments/check_axle.py` | Standard-library AXLE reproduction client with response and axiom-audit checks. |
| `experiments/test_receipt_guard.py` | Nine synthetic-response unit tests for the client’s audit logic. |
| `receipts/` | Structured summaries of actual remote checks, the locally produced CEGIS result, and the receipt-guard test log. |
| `SOURCE_SNAPSHOT.md` | Exact repository revisions and the scope of source inspection. |
| `build_pdf.py` | Cross-platform XeLaTeX build helper. |

The Lean files are deliberately standalone. `Prototype.lean` and
`SkeletonChecks.lean` repeat the same tactic definitions; **run them independently,
not as imports into one module**.

## What was actually executed

All three standalone Lean files were submitted to AXLE through the Wolfram
connector using UTF-8 JSON, environment `lean-4.34.0`, `ignore_imports = false`,
and `theorems_only = false`. Their source imports `Lean` only. All three accepted
runs returned HTTP 200, `okay = true`, no failed declarations, and no Lean errors.
The returned source matched after trimming outer whitespace. The service can add
a final newline, so this is not a byte-for-byte echo claim.

The core tactic synthesized 12 declarations covering polymorphic composition,
dependent functions and pairs, polymorphic argument construction, sum/product
elimination, indexed vector elimination, dictionary data, propositions, and a
certified witness whose proof constraint requires the correct value. Ten of those
12 declarations had empty axiom inventories; the indexed vector head and tail
used `propext`. A separately written noninhabitation theorem was also checked.

The vector-map experiment supplied the recursion skeleton and recursive call
manually, then used the tactic for the branch bodies. Lean accepted the definition
and both universally quantified defining-equation theorems. All three audited
items were axiom-free. This experiment does **not** establish automatic discovery
of recursion skeletons or motives.

The Python experiment enumerated a 471-term step grammar for a fixed left fold.
Counterexamples eliminated three candidates before selecting `[x] ++ acc`.
The selected fold passed all 40 lists of length at most three over `{-1, 0, 1}`.
That result alone is finite testing. `ReverseCertificate.lean` separately proves
correctness for every list and every element type using a manually supplied
accumulator invariant. Its definition is axiom-free; its two proof declarations
use `propext`. The invariant and universal proof were not synthesized automatically.

Across the three accepted files, 19 named declarations were audited: 15 had empty
axiom inventories and four used `propext`. This is not a claim that 19 programs
were automatically synthesized, nor a practical-coverage benchmark.

The original unsuccessful core experiment is also recorded: unfiltered
implementation-detail locals exposed provisional recursive self-references.
Lean rejected the resulting cycles. The corrected source filters those locals;
the full design adds explicit recursive-call capabilities and a final closure
and dependency audit. The small prototype is not production-hardened: its broad
exception catch, rule fuel, and limited search policy are intentionally discussed
as boundaries rather than presented as final implementations.

### Receipt interpretation

The `*-check-summary.json` files are **transcribed structured summaries of actual
AXLE responses**, not raw response dumps. They retain request IDs, diagnostics,
observed axiom inventories, relevant timings, and the scope of each test. The
reproduction client saves the full JSON returned by each new run.

The Python client’s nine unit tests use synthetic response fixtures. They test
its audit logic; they are not additional Lean compilation runs. The original
remote submissions used Wolfram, not this Python network client. Local container
network access and a local Lean installation were unavailable during preparation.
The Python algorithm and audit tests were executed locally with Python 3.13.5.

## Reproduce the Lean checks locally

With Lean/Elan available, the included `lean-toolchain` selects the tested version.
From this package’s root:

```text
cd prototype
lake env lean Prototype.lean
lake env lean SkeletonChecks.lean
lake env lean ReverseCertificate.lean
```

Each command prints its named axiom inventories and evaluations. No Mathlib
package is required by these source files. The minimal Lake configuration is
provided for convenience; the actual compilation evidence is for the standalone
source submissions described above.

## Reproduce through AXLE

The supplied runner uses Python’s standard library. Python 3.10 or later is a
suitable target; the local tests used Python 3.13.5. From the package root:

```text
python experiments/check_axle.py prototype/Prototype.lean --output receipts/core-rerun.json
python experiments/check_axle.py prototype/SkeletonChecks.lean --output receipts/skeleton-rerun.json
python experiments/check_axle.py prototype/ReverseCertificate.lean --output receipts/reverse-rerun.json
```

The runner sends the source to the AXLE check endpoint and checks more than an
HTTP or `okay` flag: failed declarations, errors, source echo, expected audit
entries, and axiom dependencies. Its default allowed-axiom set is `{propext}`.
Use `--empty-axioms` to require an empty set. With the recorded source, that
stricter audit should accept `SkeletonChecks.lean` and reject the other two files
because of the explicitly reported dependencies. A network/service failure is
reported separately from a failed check. The service’s import-header advisories
are retained rather than silently changing the source imports.

## Reproduce the finite experiment and audit tests

Run from the package root:

```text
python experiments/cegis.py --output receipts/cegis-results-rerun.json
python experiments/test_receipt_guard.py
```

The first command prints the candidate/counterexample history and writes JSON.
The regression checks demonstrate why agreement on a finite observation set is
not global equality, and why repeated uses of one unknown function must share
functional consistency constraints.

## Rebuild the article

Install a TeX distribution containing XeLaTeX, `newpx`/`newpxmath`, `fontspec`,
`fvextra`, TikZ, `tcolorbox`, and the other packages named in the preamble. The
source uses the TeX-distributed `TeXGyrePagellaX-*.otf` fonts from `newpx`, plus
Liberation Sans and DejaVu Sans Mono. No font files are distributed here.

From the package root:

```text
python build_pdf.py
```

The helper runs XeLaTeX three times to resolve the table of contents and
cross-references. Alternatively, run the following command three times in
`article/`:

```text
xelatex -interaction=nonstopmode -halt-on-error leant2.tex
```

The shipped PDF was built with XeLaTeX, checked for missing glyphs/overflow and
unresolved references, and visually inspected in rasterized pages. It contains
45 pages, including the cover.
