# Experimental history and scope

All remote runs were performed synchronously on September 17, 2026, through the
Wolfram connector calling AXLE. The local container did not run Lean.

## API probes

The service returned `Lean.versionString = "4.34.0"` and confirmed the native
APIs used for saving/restoring Meta state, introducing goals, applying terms,
case analysis, fresh metavariables, structure metadata, and expression typing.
One diagnostic-only probe tried `Lean.Exception.isInternal`, which does not
exist in this environment. The final code does not use that name.

## Native search

The first substantive native prototype run failed at the dictionary-selection example.
The service reported the default 200,000-heartbeat limit being reached during
`isDefEq` and subsequent processing. Because the dictionary definition did not
succeed, a dependent test also failed and its interim axiom report included
`sorryAx`. This first run was NOT a successful verification.

The corrected source inserts actual structure projections before recursive
constructor growth. It also restores state and propagates interrupts/heartbeat
exceptions instead of swallowing them as ordinary alternative failure. Other
ordinary rule failures remain backtrackable. The full final file was resubmitted.

The accepted native run is
`217a1c39-4a72-4447-adf2-69426f4439b8`. Its exact submitted source is
`prototype/NativeCore.lean` (6,287 Unicode code points, 178 lines). The returned
source was exactly that string plus one terminal LF. No import replacement
occurred. The structured successful response summary is in
`native_core_receipt.json`.

## Reference certificates

These examples were manually authored; they are not outputs of an automatic
recursion planner or pruning plugin.

An initial draft (request `73eccfaf-e606-4de6-9b0c-4eedd8623545`) used `prefix` as
a binder, but that token is reserved in the relevant grammar. The binder was
renamed `fixedPart`.

A second draft (request `4c32dbfe-457c-4036-9759-e1c5f1240655`) supplied explicit
arguments to `List.length_append` where this version's theorem uses implicit
arguments. The proof was changed to simplify the actual equality using the
lemma, then invoke `omega`.

The accepted reference run is
`d599bef4-fec8-4a64-b2b1-e09b3fa622b0`. Its exact submitted source is
`prototype/Certificates.lean` (1,245 Unicode code points). The returned source
again appended exactly one LF. The successful response summary is in
`certificates_receipt.json`.

## Finite behavioral laboratory

`behavior_lab.py` ran locally with five tests, zero errors, and zero failures.
The deterministic generated results are in `behavior_results.json`. It enumerates
a small explicitly typed-by-construction Python list DSL, not Lean terms.
Neither its interpreter nor its length interpreter was formalized in Lean.

The script validates affine summaries, retains observation-equivalent terms,
and demonstrates why a failing completion does not refute a whole sketch.
The recorded append CEGIS loop's first candidate already passed all 49 inputs;
there was no nontrivial CEGIS refinement sequence in that run. The separate
parking tests do exercise partition refinement and recovery of a previously
parked alternative.

## Evidence qualifications

The receipt JSON files are structured transcriptions of actual tool responses,
not raw captures or signed attestations. The optional recheck client saves raw
responses on subsequent runs. No Mathlib revision was returned by the service,
and no local Lean replay or comparative Leant/Djex benchmark was performed.
Only the final successful sources are shipped as executable Lean examples;
preliminary failed drafts are described here rather than included as if tested.
