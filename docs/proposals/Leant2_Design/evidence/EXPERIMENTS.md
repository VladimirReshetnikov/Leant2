# Experiment evidence

## Status and provenance

The two files under `prototype/` are the final, successfully checked sources.
Both were compiled with AXLE's `lean-4.34.0` environment by HTTP requests sent
through a Wolfram connector. The local container had no Lean installation and
could not resolve external hosts. The remote requests preserved `import Lean`
and processed all declarations, evaluations, and axiom reports.

`remote-results.json` is a **transcribed subset of actual tool responses**. It is
not an original HTTP response file and not a signed attestation. It records the
actual request IDs, source digests, service-build metadata, outputs, warnings,
and audited axiom inventories. The distributed source digests were recomputed
locally and matched the UTF-8 source digests reported by Wolfram. Source echoes
matched after trimming surrounding whitespace. A rerun using
`scripts/check_remote.py` creates a complete new receipt, including the returned
source and full service response.

## Final native search run

Request: `075fd65f-ec56-4045-b07e-30ddeeaac524`.
The source has 219 lines. Result: `okay = true`, no failed declarations, no Lean
or service errors. All 24 requested axiom reports appeared: 23 were empty;
`Leant2Demo.vectorHead` depended on `propext`. No `sorryAx` was present.

Evaluations, in source order: `29`, `"right"`, `[11, 12, 13]`, `7`, `[11, 12]`,
and Lean version `"4.34.0"`.

Two unused-tactic linter warnings concerned the intentionally failing negative
controls. Service warnings recommended its cached Mathlib imports. The requested
header was not replaced. Server-reported total time was 1610 ms, whole-request
time 1740 ms. These are single service observations, not isolated synthesis
benchmarks.

Limitations: the solver is bounded local search, not the proposed production
system. It uses a broad exception catch, no component index, no fair scheduler,
no automatic recursion discovery, and no CEGIS. Vector and list recursion
skeletons are supplied; the list output spine is additionally supplied.
`mixedUniverses` is not the exact predecessor's unresolved Church composition
benchmark. `exactDictionary` uses explicit records, not a new instance solver.

## Final finite CEGIS run

Request: `49fad6b0-3799-42bb-a41c-92b34b1c1d5c`.
The source has 114 lines. Result: `okay = true`, no failed declarations, errors,
or Lean warnings. All five requested axiom reports were empty.

Grammar sizes (including size zero): `[0,2,2,10,26,114,402,1722,6890]`.
There are 9168 syntax trees through size eight. Proposals were `x`, `y`, `x || y`,
`!(x && y)`, and `(x || y) && !(x && y)`. Counterexamples were `(false,true)`,
`(true,false)`, `(true,true)`, `(false,false)`. The last proposal passed; Lean
proved its universal Bool × Bool specification by ordinary `decide` after the
expression was quoted as a literal. No `native_decide` was used.

Server-reported total time was 1574 ms, whole-request time 1697 ms. The same
service-header advisories appeared. The grammar enumerator is deliberately
simple and inefficient; these timings are not a scaling study.

`finite-reference.json` was produced by actually executing the independent
Python enumerator. It confirmed the trace, counts, first satisfying size, and
an example showing why irreversible sample-equivalence pruning loses solutions.
This Python check is not a Lean proof or an independent Lean implementation.

## Preserved failed attempts

The three `.lean` files in this evidence folder are intentionally failing
historical versions and **are not build targets**.

* `NativeSearch.initial.lean`: data-producing declaration incorrectly labeled
  `theorem`, an executable definition emitted through a recursor rejected by the
  code generator, and an unavailable list relation under the core-only import.
* `NativeSearch.second.lean`: all intended constructions worked, but the length
  proof tried induction on a relation with a compound index. A generic lemma
  over variable list indices fixed the issue.
* `FiniteCEGIS.initial.lean`: a pattern variable collided with a grammar
  constructor name. Renaming the Boolean input variables fixed the error.

Some failed files produced `sorryAx` in error-recovery terms. They were not
counted as successful checks. The final files contain no `sorry` proofs.

## What was and was not tested locally

Executed locally: independent Python finite enumeration; eight unit tests of
receipt validation; Python syntax compilation; shell syntax check; LaTeX build;
PDF rendering and visual inspection. The new local Lean runner and new HTTP
wrapper were not network/Lean-executed in this environment. The original Lean
checks used the Wolfram HTTP route described above. No Leant or Djex performance
benchmark was run.
