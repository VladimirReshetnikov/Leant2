# Constructive guard checkpoint — 2026-09-21

Tested implementation: `ce31d3a49dec5c47ef3969567be15a891b619857`, with a clean working tree throughout
both runs. Lean `leanprover/lean4:v4.34.0`, core only, on Windows. Source,
executable, compiled modules, and external fixture inputs were hashed before
either run and checked again before archiving. The following evidence and
documentation commit does not change this implementation.

This checkpoint adds a bounded constructive conditional grammar. It does
not complete proposal 11's A1: predicate abduction, decision-tree learning,
arbitrary nested guards, and general conditional completeness remain open.

## Acceptance results

Both commands build the library, all Lean tests, and the REPL, then run all
eleven acceptance harnesses:

```powershell
python -X utf8 tools/run_all.py --budget 10000 --out baseline-out/guards-10000
python -X utf8 tools/run_all.py --budget 5000 --out baseline-out/guards-5000
```

| Harness | 10,000 ms/query | 5,000 ms/query | What is scored |
| --- | ---: | ---: | --- |
| baseline | 278/278 | 278/278 | Leant synthesis outcome categories |
| recursive | 9/9 | 9/9 | Recursive behavior queries |
| church | 28/28 | 28/28 | Contracted probes and impossible controls |
| context | 95/95 | 95/95 | Context, universes, scheduling, and contracts |
| corpus | 350/350 | 350/350 | Type-only Church signatures |
| session | 6/6 | 6/6 | Provider identity, filtering, comments, and undo |
| results | 10/10 | 10/10 | Result refresh, evaluation, failure rollback, namespaces, and undo |
| extended | 28/28 | 28/28 | 24 typed/replayed results and 4 certified impossible controls |
| recursion-gates | 5/5 | 5/5 | 3 typed/replayed results and 2 certified impossible controls; positive cases include universal kernel checks |
| local-proofs | 6/6 | 6/6 | 5 exact universal inhabitants, Fin execution, and 1 certified impossible control |
| guard-gates | 5/5 | 5/5 | 3 typed/replayed results and 2 certified impossible controls; positive cases include universal kernel checks |
| **Total** | **820/820** | **820/820** | Fixed required acceptance denominator |

These are 820 acceptance checks, not 820 distinct benchmark problems.
Maximum and drop-zero are now required in their original E8 form. Five
separate guard gates check stronger universal and executable obligations.
At 10,000 ms/query, E8 tree inorder remains open: **0/1** solved (1 `refuted`). The 13 Church stretch searches are also unsolved (13 `refuted`).

At 5,000 ms/query, E8 tree inorder remains open: **0/1** solved (1 `refuted`). The 13 Church stretch searches are also unsolved (13 `refuted`).

Neither open E8 nor Church stretch searches contributes to the required score. Bounded misses do not establish impossibility of their requested contracts.

Supplemental Python and native reference validation are separate from the
full-run receipts below; their success is not inferred from these summaries.
The full Lean build includes provider-free
construction, universal correctness, publication and printed-source checks,
permission boundaries, partial-closure probes, and transactional cancellation.
A focused pass or an earlier checkpoint does not replace either full run.

## What changed and what is established

The grammar considers at most four most-recent Nat locals, one orientation
of every pairwise order comparison, and equality to zero: at most ten
predicates. It skips unresolved local types and already-known positive or
negative predicates. Native `LE.le` preserves the key used for constructive
decidability lookup. Lean's `byCasesDec` constructs the proof-dependent branch
binders; no classical choice is introduced by this rule.

Only the actual root contract subtype constructor enables guards in its
program field. Computational construction carries permission, while proof,
type, class, and open goals clear it before constructing children. An ordinary
provider with the same result type cannot create this permission. A guard
uses one depth step and one shared split. Its children cannot introduce
another guard or extended outer induction; unrelated sibling obligations
retain their own metadata.

The split and its entire continuation use the existing rollback transaction.
Rejected continuations restore assignments, declarations, and diagnostics;
unknown internal exceptions and native cancellation retain their identity.
Work charges and deadlines stay outside rollback. Focused tests exercise
both a synthetic interruption and an actual `IO.CancelToken` after native
case analysis has assigned the parent goal.

The initial guard continuation disables partial residual pruning. Tests
check open native branch closures, branch proofs used in dependent values,
and cache invalidation after rollback, but those tests do not establish a
general soundness result for the delayed-assignment representation. An
independent poisoned-observation fixture verifies that this tier does not
consult partial observations. Closed candidates still prove the original
contract and pass the kernel and trust-profile gate.

The public maximum/minimum gates forbid their library implementations in
both provider inventories. The drop-zero public gate retains generic
`List.filter` and `List.filterMap`; it must not be described as a test with
those combinators withheld. All three first results must satisfy universal
equality with the withheld reference and held-out executable observations.
Two literal-False contracts require certified impossibility.

Separate Lean fixtures construct all three functions with an empty provider
inventory and a strict constructive profile. They require actual native
decidable case analysis, and actual `List.rec` without filter/fold reuse for
drop-zero. Publication retains the exact certified expression. The emitted
source is independently parsed, compiled, executed, and proved universally
equal to that expression. The generated local recursion helper is discovered
from the resulting declaration rather than by a fixed fresh name.

## Evidence and boundaries

- [10-second summary](10000-summary.json), [E8 receipt](10000-extended.json),
  [recursion receipt](10000-recursion-gates.json), [local-proof receipt](10000-local-proofs.json),
  [guard receipt](10000-guard-gates.json), [result sessions](10000-results.json),
  [complete run log](10000-run.log), and [all raw artifacts](10000-raw.zip).
- [5-second summary](5000-summary.json), [E8 receipt](5000-extended.json),
  [recursion receipt](5000-recursion-gates.json), [local-proof receipt](5000-local-proofs.json),
  [guard receipt](5000-guard-gates.json), [result sessions](5000-results.json),
  [complete run log](5000-run.log), and [all raw artifacts](5000-raw.zip).
- [Pre-run snapshot](input-snapshot.json), [post-run inputs](post-run-inputs.json),
  and [manifest](manifest.json) identify the exact tested source, executable,
  compiled modules, external inputs, receipt hashes, and every ZIP member.
- [Archive script](archive-script.py.txt) preserves the exact audit helper.
  The archive's `.gitattributes` protects all manifest-covered bytes against
  Git text conversion. The manifest excludes itself and this narrative README
  from its `files` hash map.

At 10,000 ms/query, every harness returned exit code zero. The archive retains 115 raw files, 22 empty subprocess stderr streams, 22 secondary REPL sessions, and 834 synthesis query records across all scored and unscored families. The baseline has 278 queries with complete markers; its diagnostic boundary was checked independently.

At 5,000 ms/query, every harness returned exit code zero. The archive retains 115 raw files, 22 empty subprocess stderr streams, 22 secondary REPL sessions, and 834 synthesis query records across all scored and unscored families. The baseline has 278 queries with complete markers; its diagnostic boundary was checked independently.

All five detailed receipt families record the same clean source revision and unchanged executable hash. The audit compares all 123 recorded source files, 27 compiled module artifacts, and 350 external input hashes between snapshots. Every manifest-covered artifact and every ZIP member is hash-checked; both ZIP CRC checks pass. These counts come from the captured inventories rather than a fixed previous-checkpoint module count.

The baseline scores synthesis-query outcomes, not every ordinary command in
Leant's transcripts. Each budget retains two intended preflight query errors
and one unscored ordinary-command error in `synth-prove`: an Option call omits
two explicit type arguments. The original Leant golden contains the same
error. Intentional invalid commands in the session/result tests have their
own checked diagnostic expectations.

These are source- and environment-specific validation receipts, not a
standalone synthesis-certificate format. Query and process times are recorded;
first-candidate timing and reference ranking remain unmeasured. These runs
establish no general speedup or under-1-ms node-cost claim. See the
[implementation notes](../../implementation-notes.md) and
[benchmark scope](../extended.md) for the broader open work.
