# Validation record

Prepared September 17, 2026.

## Environment and method

There was no local Lean/lake installation and no direct container network access. The user's supplied AXLE helpers identified a viable remote compilation route. Exact UTF-8 Lean source was posted through the Wolfram Language evaluator using `URLRead`, `HTTPRequest`, `ExportByteArray[..., "RawJSON"]`, and `ImportByteArray[..., "RawJSON"]`.

Requests selected `environment="lean-4.34.0"`, `ignore_imports=false`, and `theorems_only=false`. The returned source matched modulo trailing whitespace. The printed version was `4.34.0`. No independent `lean4checker`, Comparator, or local project-pinned replay was run.

The endpoint returned executor commit `4e4d05b692e56b4d928ac95c4f783f411eadabba`. Full executor image/artifact identities appear in the selected-field receipts. No Mathlib commit was returned.

## Final pilot

Source: `prototype/Leant2Pilot.lean` (133 lines).

Request: `e8685112-e949-4837-89e6-969f4eb3682b`.

Result: `okay=true`; no errors; no failed declarations; uncached response; echoed source matched. Fourteen generated declarations printed no axiom dependencies. They cover ordinary and dependent application, products and sums, proposition-valued goals, higher-rank argument construction, and correlated dependent witnesses.

The final source requests `newGoals := .all`, retaining original application argument order. The solver passes the full remaining obligation list through recursive search; later failure can therefore restore earlier witness choices. Fuel is 24 and is an operational search-transition bound, not a term-minimality certificate.

The `higherRank` example need not use its polymorphic argument. `rankNConsumer` is a stronger test because the arbitrary result type must be obtained through a consumer accepting a polymorphic function. Neither is an exhaustive polymorphism benchmark.

Seven selected type/equation examples and two `fail_if_success` negative search controls also passed. Native outputs included `2` and `(true, 7)`.

Hand-written support, not synthesized by the tactic:

| Declaration | Reported axioms |
| --- | --- |
| `Leant2Pilot.Vec.map` | none |
| `Leant2Pilot.Vec.zip` | `propext` |
| `Leant2Pilot.reverseAux` | none |
| `Leant2Pilot.reverseAux_spec` | `propext` |

Lean warnings concern unused outer variables and unused-tactic linting in the intentional negative controls. There were no reported admitted-proof warnings.

The whole-file service measurements were `parse_ms=1459`, `total_ms=1463`, and total request time 1586 ms, in a warm environment. They are not per-task synthesis times or performance comparisons.

## Earlier pilot

Source: `experiments/Leant2Pilot-first.checked.lean` (128 lines).

Request: `4d409bab-583d-444e-af0e-2fe822717c7a`.

It compiled with twelve synthesized declarations and empty axiom reports for those declarations. It used default application-goal ordering and did not contain the two extra final cases. Retained for provenance; superseded for the main results.

## Logical certificates and executable correspondence

Source: `prototype/Certificates.lean` (36 lines).

Request: `b7a9c77b-97e1-430f-a3c6-1ca890606df1`.

Result: `okay=true`; no Lean errors or warnings; no failed declarations; uncached; echoed source matched.

`noPolymorphicMap`, `safePruneAt`, and `finiteValidation` printed no axioms. `loweringCorrect` printed `[propext]`. The executable tree counter evaluated to 3. These are hand-written checked results, not synthesis outcomes. The abstract pruning theorem is conditional on a sound completion abstraction; no general abstract interpreter was implemented or verified.

## Intentional compiler rejection

Source: `experiments/RecursorCompileProbe.expected-failure.lean` (6 lines).

Request: `99ba2674-b93a-4986-8481-86859594289c`.

Result: `okay=false`; the Lean error was:

```
-:5:4-5:15: error: code generator does not support recursor `PilotTree.rec` yet, consider using 'match ... with' and/or structural recursion
```

The response had no failed-declaration names despite the compiler error, so checking only `failed_declarations` would have been insufficient. The separate noncomputable model, executable equations, and correspondence theorem in `Certificates.lean` all compiled.

## Service advisories and evidence limitations

AXLE advised importing `Mathlib.Tactic` and using its default `import Mathlib` header. The original `import Lean` header was preserved intentionally. Those advisories were not treated as successful independent verification or suppressed from the validation record.

The supplied receipts retain selected observed fields and are labeled transcriptions. They are not complete raw response files, cryptographic attestations, or formal proof objects. The exact submitted source is supplied. A new run of `tools/check_axle.py` writes a full raw response inside its receipt.

A compilation success flag alone is not proof validity: admitted proofs can compile. This study also inspected errors, failed declarations, warnings, axiom reports, and selected frozen type/equation checks. It did not independently audit the service infrastructure or prove the full metaprogram correct.

## Python helper checks

Eleven offline unit tests of `tools/check_axle.py` passed locally. They cover exact-source success, header replacement, anonymous admitted-proof warnings, named failures, missing/changed axiom inventories, ordinary compilation failure, the specific expected compiler rejection, unexpected rejection, service errors, and tool-layer errors.

Those tests do not exercise an external network call and do not count as additional Lean synthesis benchmarks.

## Manuscript build

The article was built with pdfLaTeX, rendered with Poppler, and visually inspected. The archive excludes LaTeX intermediate files, Python bytecode, rendered inspection images, and standalone checksum files.
