# Local proofs and cancellation checkpoint — 2026-09-21

Tested implementation: `914680d4e974c54eb22ee635666a28ce5996a3d3`, with a clean
working tree throughout both runs. Lean `leanprover/lean4:v4.34.0`, core only,
on Windows. The source, executable, compiled modules, and external fixture
inputs were hashed before either run and checked again before archiving.
The following evidence/documentation commit does not change this implementation.

This checkpoint adds bounded proof construction under local hypotheses,
cancellation-safe search rollback, and complete specialization of flexible
query universes in the existing classical lane. It leaves joint program/proof
search, general proof-debt scheduling, the broader P1 roadmap, and arbitrary
dependent synthesis open.

## Acceptance results

Both commands build the library, all Lean tests, and the REPL, then run all
ten acceptance harnesses:

```powershell
python -X utf8 tools/run_all.py --budget 10000 --out baseline-out/local-proofs-10000
python -X utf8 tools/run_all.py --budget 5000 --out baseline-out/local-proofs-5000
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
| extended | 26/26 | 26/26 | 22 typed/replayed results and 4 certified impossible controls |
| recursion-gates | 5/5 | 5/5 | 3 synthesized implementations with universal equations/runtime replay and 2 controls |
| local-proofs | 6/6 | 6/6 | 5 exact universal inhabitants and 1 certified impossible control |
| **Total** | **813/813** | **813/813** | Fixed required acceptance denominator |

These are 813 acceptance checks, not 813 distinct benchmark problems. Fin
of a successor and natural-order transitivity are now required in the original
E8 suite; six separate local-proof gates exercise the service more directly.
The three remaining E8 searches were solved in **0/3** cases at each budget.
The thirteen historical Church stretch searches remain unsolved at both
budgets. Neither group contributes to the required score. Their bounded
refuted outcomes are not impossibility proofs for the requested contracts.

Additional validation passed: 25 general harness/protocol tests and 12
benchmark protocol tests, plus separate elaboration of all five positive
local-proof references. The full Lean build includes the focused tests
described below. A focused result or an earlier checkpoint does not replace
either complete run in this archive.

## What changed and what is established

`Leant2/Proof/Local.lean` tries assumption/reflexivity, `simp_all`, and `omega`
on separate scratch goals in the original local context. Preparation, tactics,
and replay have separate heartbeat limits. Incoming metavariables are rigid;
an unresolved expression dependency in the target, a local type, or a local
let value suspends the attempt. This service does not jointly fill program
holes while proving their properties.

Every speculative exit restores the full Meta/Core state. Extraction rejects
unfinished assignments, sorry, reported errors, and escaped locals or
universes. Native tactics may create temporary auxiliary theorems, so their
bodies are recursively copied with universe instantiation and a finite
64-expansion cap. New axioms, definitions, and opaque declarations do not
escape this mechanism. The extracted expression must replay against the
original target in the original environment before only that goal is assigned.
The closed candidate still passes the normal kernel and trust-profile gate.

The public gates establish exact universal types for successor Fin, order
transitivity, contradiction implying False or a closed false equality, and
a polymorphic list-constructor step with a supplied length induction
hypothesis. Fin also has witness-neutral runtime observations. A separate
literal-False contract requires certified impossibility. Reference terms are
never introduced into synthesis, and named reference providers are checked
absent from the session and curated inventories. Standard imported proof
automation remains available; these checks do not claim library lemmas are
unavailable to the native tactics.

Focused Lean tests cover rigid expression/universe dependencies, hidden let
values, partial-tactic fallthrough, direct and delayed unfinished assignments,
incorrect types, errors and sorry, auxiliary theorem extraction, malicious
speculative state changes, replay, heartbeat exhaustion, deadline/grace exits,
real native cancellation tokens, and propagation of unknown internal exceptions.
An unresolved or exhausted proof attempt is never treated as logical refutation.

Search alternatives use native result-aware finalizers. Ordinary failure,
resource exceptions, and cancellation restore state, while successful values
retain the intended commit behavior. Work charges remain outside rollback.
Lane boundaries consume only recognized deadlines and heartbeat/recursion
limits; user cancellation and unrelated internal exceptions keep their identity.
The first expired lane/grace deadline determines timeout classification.
Open typeclass inputs use Lean's explicit deferred result, and upfront
contract refutation receives a fresh heartbeat origin and restores temporary
state. These are programmatic cancellation tests; they do not claim a separate
terminal Ctrl-C or editor integration test.

The classical lane now instantiates existing universe assignments before
specializing remaining placeholders and named parameters to zero. Level
successors and fixed Type universes are preserved; pending universe equations
conservatively prevent specialization. Construction, residual checks, and
acceptance share the same frozen target/contract pair. Candidates record their
actual specialized type, and the original universe holes stay unchanged.
Focused tests and the existing Basic suite cover the Peirce query, dependent
contracts, fixed/chained assignments, and structured levels. Lane-selection
policy itself is unchanged.

## Evidence and boundaries

- [10-second summary](10000-summary.json), [E8 receipt](10000-extended.json),
  [recursion receipt](10000-recursion-gates.json), [local-proof receipt](10000-local-proofs.json),
  [result sessions](10000-results.json), [complete run log](10000-run.log),
  and [raw inputs, outputs, and logs](10000-raw.zip).
- [5-second summary](5000-summary.json), [E8 receipt](5000-extended.json),
  [recursion receipt](5000-recursion-gates.json), [local-proof receipt](5000-local-proofs.json),
  [result sessions](5000-results.json), [complete run log](5000-run.log),
  and [raw inputs, outputs, and logs](5000-raw.zip).
- [Pre-run snapshot](input-snapshot.json) and [manifest](manifest.json) identify
  the tested source, executable, all discovered compiled project modules,
  external inputs, receipt hashes, and every raw ZIP member's hash.
- [Archive script](archive-script.py.txt) preserves the exact audit helper.
  The archive's `.gitattributes` preserves all manifest-covered bytes across
  Git checkout. The commands above reproduce the acceptance runs.

Every harness returned exit code zero. Each run retains 113 raw files and
22 empty subprocess stderr streams. The four detailed receipt families
record the same clean source revision and unchanged executable hash. The
archive audit reclassifies their raw outcomes, checks result transcripts
against the fixtures, verifies ZIP member hashes and CRCs, and compares
all 121 recorded source files, 26 compiled module artifacts, and 350 external
input hashes against the pre-run snapshot.

The baseline scores synthesis-query outcomes, not every ordinary command in
Leant's transcripts. At each budget its output includes two intended preflight
query errors and one unscored ordinary-command error in `synth-prove`: an
Option call omits the two explicit type arguments required by its requested
type. The original Leant golden transcript contains the same error. Other
intentional invalid commands belong to session/result rollback tests.

These receipts are tied to source and environment; they are not a standalone
synthesis-certificate format. Query and process times are recorded, while
first-candidate timing and reference ranking remain unmeasured. The runs are
not controlled performance measurements and establish no general speedup or
under-1-ms node-cost claim. See [implementation notes](../../implementation-notes.md)
and [benchmark scope](../extended.md) for the remaining implementation boundaries.
