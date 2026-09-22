# Expected-type term and tactic checkpoint

Both complete runs passed **832/832 required checks across 13 families** at clean source revision `69221f14dc87992c48a3f45f8abb9e99b2bfb963`, using `leanprover/lean4:v4.34.0`. The configured denominator and observed complete scores agree. Each aggregate run records a successful full build; the frontend runner itself does not build. Query budgets are cooperative and do not impose a strict whole-process time limit.

| Family | 10,000 ms budget | 5,000 ms budget |
| --- | ---: | ---: |
| baseline | 278/278 | 278/278 |
| recursive | 9/9 | 9/9 |
| church | 28/28 | 28/28 |
| context | 95/95 | 95/95 |
| corpus | 350/350 | 350/350 |
| session | 6/6 | 6/6 |
| results | 10/10 | 10/10 |
| extended | 29/29 | 29/29 |
| recursion-gates | 5/5 | 5/5 |
| local-proofs | 6/6 | 6/6 |
| guard-gates | 5/5 | 5/5 |
| tree-composition | 3/3 | 3/3 |
| frontends | 8/8 | 8/8 |
| **Total** | **832/832** | **832/832** |

The [frontend fixtures](../../../tests/benchmarks/frontend-fixtures/cases.json) exercise `synth%` at an expected type and the `leant2` tactic with local data/proofs, dependent types, shared delayed type constraints, genuine lets/local instances, and indexed Vec mapping. The shared implicit type in the delayed fixture is constrained by a later argument; its first synthesized argument is not pretyped. Vec mapping is checked at its actual indexed type with universal nil/cons equations and executable Nat-to-Bool and Bool-to-Nat observations.

Three tactic cases extract the real emitted `Try this:` text, remove only its documented `[apply]` widget label and framing indentation, and insert that text into a new file importing **Lean only**. A separate fresh process repeats the relevant type, proof, and executable checks without the producer's compiler-adapter environment. The recursive display gate requires match/let-rec source rather than a raw recursor or compiler helper reference. This establishes unassisted synthesis and fresh source replay for these cases; separate tests that start from supplied known terms retain their narrower publication scope.

Two negative cases require rejection inside successful outer theorems whose actual proof bodies and transitive axioms are audited. Each also has a separate bare-failure file requiring the frontend's specific diagnostic and Lean error exit 1. A sorry warning from normal top-level recovery is permitted only in that deliberately failing file and is counted below. Successful original/replay stages reject errors, warnings, holes, and sorry dependencies. Public frontends use the standard axiom profile; local hypotheses are parameters of the checked query. This checkpoint does not imply completeness for arbitrary contextual/dependent search or support for additional contract/sketch syntax. See [implementation notes](../../implementation-notes.md).

All **29 original E8 cases remain required**, comprising 25 positive cases and 4 impossible controls, with zero open cases. The separate tree, guard, recursion, and local-proof gates retain their own obligations. Public tree searches permit ordinary providers including `List.append`; internal route tests and known-term publication tests remain distinct evidence. Required totals count acceptance checks with overlapping goals, not distinct synthesis problems.


At **10,000 ms**, the complete raw ZIP contains **164 files** (22 `.in`, 9 `.json`, 13 `.jsonl`, 13 `.lean`, 14 `.log`, 52 `.out`, 35 `.stderr`, 6 `.txt`) and **35 empty stderr streams**. The legacy audit records **837 synthesis-query records**: 278 baseline queries, 511 queries across 22 retained REPL sessions, and 48 manifest queries. Separately, the **8 frontend cases require 13 fresh Lean processes**: 8 original stages, 3 independent suggestion replays, and 2 deliberately failing files. Those files produce 2 expected error diagnostics and 0 ordinary recovery warnings. The non-replay frontend source contains 12 syntax occurrences; this is not a count of elaborator retries or a replacement for the legacy query total. Church stretch results are **0/13 solved**, with 13 bounded misses (13 `refuted`), excluded from the required score.

At **5,000 ms**, the complete raw ZIP contains **164 files** (22 `.in`, 9 `.json`, 13 `.jsonl`, 13 `.lean`, 14 `.log`, 52 `.out`, 35 `.stderr`, 6 `.txt`) and **35 empty stderr streams**. The legacy audit records **837 synthesis-query records**: 278 baseline queries, 511 queries across 22 retained REPL sessions, and 48 manifest queries. Separately, the **8 frontend cases require 13 fresh Lean processes**: 8 original stages, 3 independent suggestion replays, and 2 deliberately failing files. Those files produce 2 expected error diagnostics and 0 ordinary recovery warnings. The non-replay frontend source contains 12 syntax occurrences; this is not a count of elaborator retries or a replacement for the legacy query total. Church stretch results are **0/13 solved**, with 13 bounded misses (13 `refuted`), excluded from the required score.

The legacy baseline preserves **two scored preflight diagnostics** for ill-typed/unknown contract expressions and **one unscored post-query Option-call type error**. They are checked at their exact query boundaries. The recursive, context, corpus, Church, and session transcripts are independently reconstructed from the captured runner/fixture inputs, and their raw outcomes are rescored against each expected category; session provider histories are also checked. This semantic re-audit is additional to the retained protocol/count checks and aggregate logs. Expected rejected declarations in legacy session/results fixtures are checked against those fixtures' permitted diagnostics. Church setup has no unexpected comment/setup diagnostics. The archive is therefore not described as diagnostic-free; new frontend rejection diagnostics are separately scoped above. Bounded stretch outcomes concern these configured searches and do not prove mathematical impossibility.

The [manifest](manifest.json) binds the [pre-run snapshot](input-snapshot.json) to identical [post-run inputs](post-run-inputs.json): **151 source/configuration hashes**, **42 compiled-artifact hashes** covering the complete recorded compiled-module inventory, and **350 external fixture-file hashes**. External repository revisions and dirty flags are recorded independently. `leant2.exe` SHA-256 is `1b259161d8676e70ac82f9b31ca0c671382666ef6411c06da069a6c7e0922d80`; native Lean SHA-256 is `a8040e2cab341c12116ab591fed9f761816f5f6b08554f6cc1680e86dfbba0a2`. Fingerprints alone do not establish a rebuild; the successful aggregate build records are separate evidence.

The [10-second summary](10000-summary.json), [5-second summary](5000-summary.json), [10-second frontend receipt](10000-frontends.json), [5-second frontend receipt](5000-frontends.json), other detailed receipts, outer logs, and complete [10-second raw ZIP](10000-raw.zip) / [5-second raw ZIP](5000-raw.zip) preserve original bytes. File hashes, ZIP member inventories/hashes/CRCs, copied receipts, stage sources, actual suggestions, diagnostic classifications, and exits are independently rechecked. The archive preserves its [auditor](archive-script.py.txt) and pinned [tree auditor](tree-archive-script.py.txt), [base auditor](base-archive-script.py.txt), and [audit utilities](base-finish-script.py.txt). The local `.gitattributes` protects evidence bytes; this narrative is ordinary Git text outside the manifest hash scope.

The prior [p1-2026-09-21](../p1-2026-09-21/README.md), [induction-2026-09-21](../induction-2026-09-21/README.md), [local-proofs-2026-09-21](../local-proofs-2026-09-21/README.md), [guards-2026-09-21](../guards-2026-09-21/README.md), [tree-composition-2026-09-21](../tree-composition-2026-09-21/README.md) archives remain unchanged. Their historical scores and scopes are not retroactively extended by this checkpoint. This archive is a validation receipt bundle with input fingerprints, not a standalone toolchain or executable replay bundle. No separate Python-test or focused-reference-validation pass count is inferred from these complete-run receipts.
