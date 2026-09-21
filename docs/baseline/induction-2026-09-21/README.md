# Dependent recursion and session results checkpoint — 2026-09-21

Tested implementation: `555236a27f3f7d6f9a2284bcc597b1133b6e1be2`, with a clean working
tree throughout both runs. Lean `leanprover/lean4:v4.34.0`, core only, on
Windows. Source, executable, compiled modules, and external fixture inputs
were hashed before the first run and checked again before archiving. The
following evidence/documentation commit does not change the implementation.

This checkpoint adds bounded outer induction for Nat and supported
single-index families, executable publication of supported indexed recursors,
and transactional session result aliases. It does not close the broader P1
roadmap or claim arbitrary dependent program synthesis.

## Acceptance results

Both commands build the library, all Lean tests, and the REPL, then run all
nine harnesses:

```powershell
python -X utf8 tools/run_all.py --budget 10000 --out baseline-out/induction-10000
python -X utf8 tools/run_all.py --budget 5000 --out baseline-out/induction-5000
```

| Harness | 10,000 ms/query | 5,000 ms/query | What is scored |
| --- | ---: | ---: | --- |
| Baseline | 278/278 | 278/278 | Leant synthesis outcome categories |
| Recursive | 9/9 | 9/9 | Recursive behavior queries |
| Church | 28/28 | 28/28 | Contracted probes and impossible controls |
| Context | 95/95 | 95/95 | Context, universe, scheduling, and contract cases |
| Corpus | 350/350 | 350/350 | Type-only Church signatures |
| Session | 6/6 | 6/6 | Provider identity, comments, rejected-entry filtering, and undo |
| Results | 10/10 | 10/10 | Result refresh, immutable old definitions, evaluation, failures, namespaces, and undo |
| Extended | 24/24 | 24/24 | 20 required results with typed replay, plus 4 certified impossible controls |
| Recursion gates | 5/5 | 5/5 | 3 synthesized implementations with universal equations and executable replay, plus 2 certified impossible controls |
| **Total** | **805/805** | **805/805** | Fixed required acceptance denominator |

These are 805 acceptance checks, not 805 distinct benchmark problems. The
original predecessor, powers-of-two, and indexed-vector-map probes are now
required; the independent recursion gates test these implementations more
strongly. The five remaining extended searches were solved in **0/5** cases
at each budget. The thirteen historical Church stretch searches remain
unsolved at both budgets. Neither group contributes to the required score.
Rejection of tried candidates is a bounded search result, not an impossibility
proof for the requested contract.

Additional validation passed: 25 general harness/protocol tests and 12
extended protocol tests. The full Lean build includes native dependent
induction, rollback after completed branches, recursion eligibility,
indexed publication and printed-source replay, and result alias/evaluation
regressions. The detailed focused checks are described below.

## What changed and what is established

The new search tier uses Lean's native motive inference and dependent-local
reversion for one outer induction on Nat or a supported single-index recursive
family. Predecessor uses no providers in its Lean search test, power of two
uses only addition, and polymorphic vector map uses no providers. Kernel
checks establish predecessor's arbitrary-successor equation, power's base
and doubling equations, and vector map's nil/cons equations for arbitrary
parameters. The public harness separately verifies withheld provider names,
exact result types, and runtime observations beyond the training examples.

Recursion eligibility follows outer introductions and the program field of
the root `Subtype.mk`. A provider returning the same subtype cannot pass
this permission into its ordinary argument. Native induction failure and a
rejecting continuation restore the original goal and pre-existing sibling
assignments. Indexed induction disables the existing partial residual pruning;
closed candidates still prove the original contract and pass the acceptance
gate. Search does not yet cover general multiple-index, mutual, nested-family,
or arbitrarily nested natural induction.

Executable presentation supports single-family indexed recursors with varying
indices and major premise, including multiple indices and dependent motives.
The stored kernel expression remains unchanged; compiler adapters require a
kernel-checked equality proof and a standard-profile axiom audit. Lean tests
cover universe-polymorphic vector map, a two-index family, dependent proof
fields, runtime execution, and printed-source re-elaboration. Unsupported
mutual/nested-family adapters retain an explicit noncomputable fallback.
Presentation coverage is broader than the search grammar.

Session results now use replaceable aliases to fresh immutable declarations.
Each successful query refreshes `it1`, `it2`, and subsequent numbered names,
removes stale entries, and updates bare `it`. Previously elaborated definitions
keep their original values. Well-formed unsuccessful queries clear the
numbered batch but preserve bare `it`; preflight failures preserve both.
Bare expressions evaluate and update only `it`. An IO expression remains an
action, rather than a memoized runtime result. Known name collisions are
rejected before evaluation can perform IO, and failed publication/evaluation
restores alias and declaration state. Undo/reset and namespace/root-qualified
names have executable integration coverage. Generated declarations remain
outside the session provider inventory.

## Evidence and boundaries

- [10-second summary](10000-summary.json), [extended receipt](10000-extended.json),
  [recursion receipt](10000-recursion-gates.json), [result-session receipt](10000-results.json),
  [complete run log](10000-run.log), and [raw inputs, outputs, and logs](10000-raw.zip).
- [5-second summary](5000-summary.json), [extended receipt](5000-extended.json),
  [recursion receipt](5000-recursion-gates.json), [result-session receipt](5000-results.json),
  [complete run log](5000-run.log), and [raw inputs, outputs, and logs](5000-raw.zip).
- [Pre-run input snapshot](input-snapshot.json) records committed source,
  executable, module, and external input hashes before either run.
- [Manifest](manifest.json) records the tested revision, input comparisons,
  receipt hashes, and every raw ZIP member's hash. Receipt bytes are preserved
  across Git checkout by the local `.gitattributes` file.
- [Archive script source](archive-script.py.txt) preserves the exact audit
  script used from the repository's ignored `scratch` directory. This copy is
  provenance for the audit; the commands above reproduce the acceptance runs.

Every harness returned exit code zero. Each run retained 22 empty subprocess
stderr streams and 111 raw files. The three detailed receipt families record
the same clean source revision and executable hash. The archive audit also
reclassifies their outcomes from the raw outputs, checks result transcripts
against the fixture definitions, and verifies ZIP member hashes and CRCs.

The baseline scores synthesis queries, not every ordinary command in a Leant
transcript. Its raw output at each budget contains two intended preflight
query errors in `synth-behavior.out`, plus one unscored ordinary-command error
in `synth-prove.out`: an Option call omits the two explicit type arguments of
its requested type. Leant's original golden transcript already contains that
same error. The previous manual-transcript failures for bare `it * 10` and a
later `it2` evaluation are fixed. The session and result harnesses also submit
intentional invalid commands to verify filtering and transactional behavior.

These are source- and environment-bound validation receipts, not a standalone
synthesis certificate/replay format. Query and process elapsed times are
recorded; first-candidate timing and reference ranking remain unmeasured.
The runs are not controlled performance measurements and do not establish
an under-1-ms node-cost target or a general speedup. Local-context proof-service
and cancellation-hardening work follows this checkpoint; it is not included
in the tested source. See [implementation notes](../../implementation-notes.md)
and [benchmark scope](../extended.md) for the remaining roadmap and contracts.
