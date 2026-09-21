# P1 implementation checkpoint — 2026-09-21

Tested implementation: `87ed037cae552b8f53aecabcd3145743f6147785`, with a clean working tree throughout both
runs. Lean `leanprover/lean4:v4.34.0`, core only, on Windows. The following
documentation/evidence commit does not change the tested implementation.

This checkpoint implements executable presentations of accepted recursor
terms, incremental kernel observation reports, opt-in profiling, an initial
local extended benchmark suite, and stricter acceptance harnesses. Proposal
11's P1 remains partial; this receipt does not close the broader roadmap.

## Acceptance results

Both commands build the library, all Lean tests, and the REPL before running
the seven harnesses:

```powershell
python -X utf8 tools/run_all.py --budget 10000 --out baseline-out/verified-10000
python -X utf8 tools/run_all.py --budget 5000 --out baseline-out/verified-5000
```

| Harness | 10,000 ms/query | 5,000 ms/query | What is scored |
| --- | ---: | ---: | --- |
| Baseline | 278/278 | 278/278 | Leant synthesis outcome categories |
| Recursive | 9/9 | 9/9 | Recursive behavior queries |
| Church | 28/28 | 28/28 | Contracted probes and impossible controls |
| Context | 95/95 | 95/95 | Context, universe, scheduling, and contract cases |
| Corpus | 350/350 | 350/350 | Type-only Church signatures |
| Session | 6/6 | 6/6 | Provider identity, comments, rejected-entry filtering, and undo |
| Extended | 21/21 | 21/21 | 17 required results with typed replay, plus 4 certified impossible controls |
| **Total** | **787/787** | **787/787** | Fixed required acceptance denominator |

The eight extended open searches were solved in **0/8** cases at
10,000 ms and **0/8** cases at 5,000 ms. The thirteen historical Church
stretch searches remain unsolved at both budgets. Neither group contributes
to the required denominator. Rejection of the candidates tried is a bounded
search outcome, not a proof that no satisfying program exists.

The extended suite consists of 29 fresh processes. All 25 positive fixture
references were independently checked for their types and stated contracts;
the references are withheld from synthesis. A result counts as solved only
after its first binding checks at the requested type and passes its replay.
The universal length contract is re-proved, and proof targets are checked at
their exact types. Concrete observations do not establish arbitrary universal
behavior or equivalence to the reference. See [extended-suite scope](../extended.md).

Additional validation passed: 23 general harness/protocol tests, 9 extended
protocol tests, and 11 executable REPL parser cases. The parser receipt
includes malformed-comment controls that must still produce diagnostics.
The Lean build includes publication round trips, kernel/cache observations,
and six bounded searches comparing candidate order and ledgers with profiling
enabled and disabled. These checks establish parity, not a speedup.

## Evidence and boundaries

- [10-second summary](10000-summary.json), [extended receipt](10000-extended.json),
  [complete run log](10000-run.log), and [raw transcripts and logs](10000-raw.zip).
- [5-second summary](5000-summary.json), [extended receipt](5000-extended.json),
  [complete run log](5000-run.log), and [raw transcripts and logs](5000-raw.zip).
- [REPL parser regression](comment-regression.json) records exact inputs,
  outputs, expected diagnostic status, and the tested executable hash.
- [Manifest](manifest.json) records the tested revision, executable and module
  hashes, input repository revisions, and hashes of the receipt files.

Both extended receipts record a clean tree, the same executable hash, and no
executable change during the run. Every harness returned exit code zero; all
captured subprocess stderr streams are empty. Full raw output is retained in
the ZIP files, including expected diagnostics.

The baseline scores synthesis queries, not every ordinary command in a Leant
transcript. Its raw output at each budget contains two intended preflight
query errors in `synth-behavior.out` (an ill-typed argument and an unknown
predicate), plus three **unscored ordinary-command errors**: `it * 10` before
synthesis and a later `#eval it2 "left" "right"` in `synth-manual.out`, and a
later Option evaluation using `it1` in `synth-prove.out`. The latter commands
assume legacy binding behavior or reuse a result binding. Thus 278/278 is not
evidence that every legacy transcript command executes successfully. The
separate extended suite tests newly returned bindings in isolated sessions.
The Church-provider transcript's previous three comment-only setup errors
are fixed and absent from these runs. The session suite also deliberately
submits one invalid declaration to verify that rejected entries do not become
providers.

These are source- and environment-bound validation receipts, not the proposed
standalone synthesis replay/certificate format. First-candidate timing and
reference ranking remain unmeasured (`null` in the extended receipts). Query
and process elapsed times are available; the run times are not controlled
performance benchmarks.

## Remaining P1 work

Generated compiler adapters support single, non-indexed inductive families;
unsupported indexed/mutual recursors and non-executable providers can still
require an explicitly reported noncomputable binding. Partial observation
reports use kernel reduction and conservative blockers; acceptance continues
to prove the original contract. Sampling-profile attribution, a demonstrated
local-cache benefit, the under-1-ms node-cost gate, external benchmark ports,
and the unsolved search cases remain open. See
[implementation notes](../../implementation-notes.md).
