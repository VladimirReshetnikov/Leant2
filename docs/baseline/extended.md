# Initial E8 benchmark suite

`tools/run_extended.py` adds 29 independent REPL sessions beyond the Leant
corpus: the sixteen edge probes in proposal 11, nine small examples based on
Lean core definitions and equations, and four impossible-contract controls.
The sixteen probes are **reconstructions of the article's descriptions**;
the article did not preserve the original query transcripts. Their literal
examples must not be described as an exact replay of that historical run.

This is the initial local part of E8. It does not import or claim coverage of
Myth, Lambda2, Smyth, Burst, Trio, Agsy, or Sauto. The thirteen historical
Church stretch cases remain in `run_church.py`; they are not counted again
here. External benchmark ports, differential evaluation, reference ranking,
and time to first candidate remain open E8 work.

## Scoring

| Group | Required candidates | Impossible controls | Open searches |
| --- | ---: | ---: | ---: |
| Sixteen article probes | 16 | 0 | 0 |
| Lean core List/Option/Nat | 9 | 0 | 0 |
| Negative controls | 0 | 4 | 0 |
| Total | 25 | 4 | 0 |

`TOTAL passed/29` covers the required capabilities and controls; `OPEN solved/0`
records that no current E8 case is unscored. Case selection changes the
denominators to the selected cases. An open search can exhaust its budget or
search bounds, or refute all proposed candidates. An exception, malformed or
incomplete output, process timeout, bad replay, or candidate satisfying the
literal `False` contract fails the run even in the open group. Because all
positive fixtures have checked reference inhabitants, a claim of uninhabitedness
or impossible contract for one of them also fails the run. A negative control
requires `provably no program satisfies the contract`; silence or timeout does
not establish the control.

Tree inorder was promoted after its unchanged original queries passed at both
budgets and the separate tree gates passed universal equations and held-out
execution. Maximum and dropping
zeros were promoted after their original finite-contract queries synthesized
and replayed successfully and the separate public guard gates passed universal
post-checks and held-out execution.
`Fin (n+1)` and order transitivity were promoted after the bounded local proof
service passed their original probes and the separate local-proof gates below.
Power of two, indexed vector map, and
natural predecessor were promoted to required capabilities after focused
implementation runs synthesized and replayed all three original cases and
passed the stronger recursion gates below. These classifications are fixed
expectations, not a list silently derived from whichever cases pass.
List sum is a required capability because a reported result must also bind and
execute; it exercises proposal 11's E1 code-generation defect directly.

## Execution and evidence

Each query runs in a fresh process, with only its datatype setup and the
frontend's ordinary curated providers. No reference implementation is supplied
to synthesis. This avoids provider contamination and stale `it1` bindings from
an earlier query. The harness then checks the first returned binding at the
requested type and executes the concrete observations using `#eval`. The
universal length-preservation probe additionally re-proves its universal
contract against the binding. Proof-valued targets are checked at their exact
type. Search acceptance, successful binding, and executable replay are all
required for a solved result.

The checks concern the **first accepted candidate**. They do not establish
that every later displayed candidate runs, that a candidate is extensionally
equal to the reference, or that finite observations imply a universal
specification. The manifest distinguishes the universally quantified contract
and proof targets from the concrete examples. Library providers remain
available, so this suite measures synthesis with the normal provider policy;
it does not measure discovery with the named library function withheld.

The JSON receipt contains every query transcript, stdout/stderr, outcome,
expectation, source, query elapsed time, process wall time, executable hash,
manifest hash, Git revision, and dirty-worktree flag. Its executable hash is
captured before execution and a changed executable fails the run. A receipt
from a dirty tree is not evidence for the named commit alone. The frontend
currently reports total query elapsed time; `time_to_first_candidate_ms` and
`reference_rank` are therefore explicitly `null`, not estimates. The printed
candidate prefix is informational and is never used to score semantic equality.

```powershell
lake build leant2
python tools/run_extended.py --budget 10000
python tools/run_extended.py --case probe06_sum --case core_option_is_some --budget 3000
python tools/run_extended.py --list
```

The default receipt is `baseline-out/extended.json`. Use `--out` to retain a
revision-specific receipt. A process wall timeout defaults to the query budget
plus 30 seconds; `--timeout` can adjust it. A process killed by that outer
timeout is a harness failure, distinct from the engine's normal budget outcome.
Run integration must inspect the **exit code**, as an error on an open case
intentionally does not reduce the scored `TOTAL` denominator.

Before trusting outcomes, validate that the fixture references inhabit their
types and satisfy the stated contracts. This separate Lean process checks all
25 positive references, their concrete observations, and the universal
contract. The four literal-False controls intentionally have no reference.

```powershell
python tools/run_extended.py --validate-fixtures
python -m unittest discover -s tests/benchmarks -p test_extended.py -v
```

The protocol tests cover missing replay, named and unnamed Lean errors,
stderr and process failure, certified rejection versus timeout, executable
counterexamples, missing or duplicated query blocks, impossible claims on
inhabited open cases, and replay markers without candidates. Fixture validation
passed with Lean v4.34.0 during implementation. A preliminary seven-case run
against the original executable reproduced the list-sum compilation failure;
it is diagnostic evidence, not a completed 29-case acceptance receipt.

## Nat and indexed recursion gates

`tests/benchmarks/recursion.json` is a separate acceptance manifest for a
bounded recursion extension. Its `TOTAL passed/5` consists of three required
candidates and two literal-False controls. It is not part of the original
29-case E8 denominator above. Required expectations define what this gate must
demonstrate. The three corresponding original E8 cases additionally remain
required in their original form; the stronger checks below do not replace them.

| Required candidate | Synthesis input | Independent post-checks |
| --- | --- | --- |
| Natural predecessor | Four concrete examples | Kernel equations at zero and arbitrary successor; runtime inputs 2, 3, 32, and 127 |
| Power of two | Three concrete examples | Kernel base and doubling equations for arbitrary `n`; runtime inputs 1, 2, 8, and 10 |
| Indexed vector map | Polymorphic type over arbitrary `A B : Type` | Kernel nil/cons equations for arbitrary element types, function, length, head, and tail; execution on actual length-three indexed vectors from Nat to Bool and Bool to Nat |

The vector is a fresh indexed inductive family `RecursionVec A n`, not a list
with an external length check. Nat and indexed-map False controls must report
a certified impossible contract. Every session starts fresh. The frontend's
ordinary provider policy supplies arithmetic building blocks such as
`Nat.add`, but no reference implementation is introduced. Before synthesis,
the harness checks that explicitly forbidden providers are absent from both
the session and curated sets: `Nat.pred`/`Nat.sub`, `Nat.pow`/`HPow.hPow`/`Pow.pow`,
and `RecursionVec.map`, respectively. A provider-policy change that violates
these checks fails the gate instead of silently changing what it measures.

The optional manifest field `kernel_checks` contains `{type, proof}` pairs,
with `{f}` replaced by the first accepted result binding. These commands run
after synthesis and before the executable replay marker; a proof error fails
the case. `reference_proof` can supply a different proof for validating the
withheld reference. This allows a library implementation and a synthesized
recursor to satisfy the same equations through different reductions. The
current candidate proofs require the base and constructor equations to hold
definitionally. A future implementation with only propositional equations
will need an explicitly reviewed proof update rather than dropping the checks.

```powershell
python tools/run_extended.py --manifest tests/benchmarks/recursion.json --validate-fixtures --out baseline-out/recursion-gates.json
python tools/run_extended.py --manifest tests/benchmarks/recursion.json --budget 10000 --out baseline-out/recursion-gates.json
```

`--manifest` selects the fixture file; the receipt records its absolute path
and hash. The normal E8 file remains the default. Fixture validation checks
the three withheld references, their universal equations, and all runtime
observations in a separate Lean process. It does not run synthesis. These
gates check exact bound types, kernel equations, and executable behavior;
printed-source roundtrips and higher-universe presentation tests belong to the
separate `IndexedPresentation` Lean test module.

The focused implementation run passed all five recursion gates, and all three
original E8 probes produced candidates with successful replay. Those receipts
were taken from a dirty working tree and establish the promotion decision,
not a complete acceptance run for the recorded parent commit. Final milestone
evidence must identify the tested source revision, executable, and manifests.

The subsequent clean-source [induction checkpoint](induction-2026-09-21/README.md)
at `555236a` passed all 24 required E8 cases and all five recursion gates at
both 10,000 and 5,000 ms/query. Its five remaining E8 open searches were
unsolved at both budgets. The archive includes the unchanged executable hash,
pre-run input/module hashes, complete raw output, and universal-equation checks.

## Result-binding integration and aggregate scoring

`tools/run_results.py` checks ten independent REPL sessions: bare-expression
evaluation, type-changing synthesis and saved old definitions, shrinking
candidate batches, unsuccessful queries, preflight failures, failed evaluation,
a successful evaluation after an earlier diagnostic, undo/reset, namespace and
local-binder hygiene, and user-declaration collisions. Its fixed denominator is
`TOTAL passed/10`; the existing six-session provider suite stays separate.

The result suite requires exact executable markers and query outcomes, checks
provider inventories where specified, and rejects unexpected diagnostics,
missing query boundaries, stderr, and process failures. The three intentional
diagnostic sessions require their expected diagnostic exactly once; the prior
error must remain visible even when a later evaluation succeeds. Raw session
input, output, stderr, and the JSON receipt are retained under the supplied
`--out` directory. The focused implementation run passed all ten sessions.

```powershell
python tools/run_results.py --budget 10000 --out baseline-out/results
python tools/run_all.py --budget 10000 --out baseline-out/milestone-10000
```

`run_all.py` runs 13 harnesses with distinct artifact paths. Their expected
denominators are baseline 278, recursive 9, Church 28, context 95, corpus 350,
session 6, results 10, extended 29, recursion gates 5, local proofs 6, guard
gates 5, tree composition 3, and frontends 8: **832 acceptance checks in
total**. Some checks exercise the same synthesis goals at different boundaries,
so this is not a count of 832 distinct benchmark problems. The frontend family
uses fresh Lean files instead of REPL queries and keeps its process-stage counts
separate from the legacy synthesis-query totals. The
Church stretch cases remain outside these scored denominators; every E8 case
is now required. Every harness must also exit successfully;
a full printed score does not conceal a process or open-case failure.

The earlier nine-harness configuration passed **805/805** at both budgets in the clean-source
`555236a` checkpoint. Its ten result sessions also passed at each budget.

## Bounded local-proof gates

`tests/benchmarks/local-proofs.json` adds six independent public sessions:
five required inhabitants and a certified literal-False control. The positive
queries cover a successor `Fin`, natural-order transitivity, contradictory
arithmetic hypotheses proving `False` or a closed false equality, and a
polymorphic list-constructor step under an explicit length induction hypothesis.
Every result is rechecked at its exact universal type. The Fin result also
executes observations valid for any inhabitant; no particular witness is
required. The supplied induction hypothesis tests local proof construction,
not discovery of an induction scheme.

References are checked in a separate Lean process and never introduced into
the synthesis session. Named reference lemmas are forbidden in the session
and curated provider inventories, while ordinary imported proof automation
remains available. This measures construction through the local proof service;
it does not claim that the proof tactics lack access to library theorems.

```powershell
python tools/run_extended.py --manifest tests/benchmarks/local-proofs.json --validate-fixtures --out baseline-out/local-proofs.json
python tools/run_extended.py --manifest tests/benchmarks/local-proofs.json --budget 10000 --out baseline-out/local-proofs.json
```

The focused implementation run passed all six gates and both original
Fin/transitivity probes. These dirty-tree receipts justify their promotion;
they are not a complete acceptance receipt for the recorded parent revision.
The subsequent clean-source [local-proof checkpoint](local-proofs-2026-09-21/README.md)
at `914680d` passed **813/813** across all ten harnesses at both 10,000 and
5,000 ms/query. Its E8 suite passed 26/26 and the local-proof suite passed
6/6 at each budget; the three remaining E8 searches were unsolved. The archive
retains complete raw runs and verifies pre/post input hashes. Focused Lean
tests separately exercise dependency
rigidity, extraction and replay, auxiliary-theorem handling, cancellation,
rollback, and resource-exhaustion behavior.

## Constructive guard gates

`tests/benchmarks/guards.json` defines five additional public sessions: maximum,
minimum, dropping zeros from a natural-number list, and two literal-False
controls at the corresponding function types. Maximum and drop-zero retain
the original E8 finite synthesis contracts. Minimum uses the same natural
inputs with the opposite selection. Every positive result must pass a kernel
proof of its universal equality with the withheld reference and held-out
executable observations. The controls require certified contract impossibility.

Maximum and minimum providers are explicitly forbidden in both the session
and curated inventories. The public drop-zero case retains generic
`List.filter` and `List.filterMap`, consistent with the ordinary provider
policy. It measures the public result, not discovery of recursion with those
combinators withheld. Separate Lean fixtures use an empty provider inventory,
require native `Decidable` case analysis and actual `List.rec` for drop-zero,
and reject generic filter/fold reuse. They also check exact certified-term
publication, executable behavior, and universal equality after reparsing the
printed source.

```powershell
python tools/run_extended.py --manifest tests/benchmarks/guards.json --validate-fixtures --out baseline-out/guard-gates.json
python tools/run_extended.py --manifest tests/benchmarks/guards.json --budget 10000 --out baseline-out/guard-gates.json
```

Reference validation runs in a separate Lean process and does not run
synthesis. Required expectations describe the acceptance obligations; they
are not themselves evidence that a build passes. The guarded-program gates
have their own denominator and do not replace the original E8 probes.

The focused development run passed all five public gates at 5,000 ms/query,
including the universal post-checks, and both original E8 probes synthesized
and replayed successfully. All three positive references passed separate
native validation. These receipts came from the dirty implementation tree;
they justify the expectation promotions and do not establish a complete
acceptance checkpoint for the recorded parent revision.

The subsequent clean-source [constructive guard checkpoint](guards-2026-09-21/README.md)
at `ce31d3a` passed **820/820** across all eleven harnesses at both 10,000 and
5,000 ms/query. E8 passed 28/28 and the public guard family passed 5/5 at each
budget. Tree inorder was a bounded miss in both runs. The accepted public
drop-zero function uses generic `List.filter` with a synthesized zero-test
predicate; the separate empty-provider Lean test builds actual guarded
`List.rec`. Both raw runs and unchanged pre/post source, module, executable,
and external-input hashes are archived.

## Binary-tree composition gates

`tests/benchmarks/tree-composition.json` adds three required fresh-process
sessions, independently of the original E8 denominator. The first preserves
the original tree-inorder datatype, type, and three finite search observations
verbatim. Its post-checks require the empty-leaf equation and the node equation
for arbitrary left/right subtrees and labels, then execute four held-out trees.
The second uses a different datatype with values at tips and unlabelled binary
forks. Universal tip/fork equations require singleton tips and ordered
concatenation; five held-out trees exercise duplicates, zeros, and balanced
and skewed shapes. The third session certifies a literal-False contract at the
inhabited original tree-function type.

The ordinary provider set, including `List.append`, remains available. Only
fresh datatype declarations precede each query, and named traversal providers
are checked absent. References, equation lemmas, and diagnostic witnesses are
withheld from synthesis. A separate fixture-validation process checks the two
references. Public gates establish typed results, universal constructor
equations, and executable observations; they do not identify the internal
search route or establish an empty-provider result. Native unit tests separately
check actual composition-route permissions and publication of a known certified
tree recursor through independently parsed source with universal equivalence.

```powershell
python tools/run_extended.py --manifest tests/benchmarks/tree-composition.json --validate-fixtures --out baseline-out/tree-references.json
python tools/run_extended.py --manifest tests/benchmarks/tree-composition.json --budget 10000 --out baseline-out/tree-composition.json
```

Focused development runs passed all three gates at both 5,000 and 10,000 ms,
and the unchanged original E8 tree request passed independently at both
budgets. This justifies promoting that final E8 case to required, giving a
configured aggregate of 824 across twelve families. The development receipts
came from a dirty tree and do not establish complete acceptance at their
recorded parent revision. An enabled/disabled comparison on one unchanged
binary found this tree query in both modes: the new early closed-contract
evaluation benefits ordinary fallback too. Four runs with composition took
1,080–1,679 ms; four without it took 5,049–5,787 ms. These are fixture-specific
total query times, not first-candidate timing or a general performance claim.

The subsequent clean-source [tree-composition checkpoint](tree-composition-2026-09-21/README.md)
at `313a441` passed **824/824 across all twelve harnesses** at both 10,000 and
5,000 ms/query. All 29 original E8 cases and all three new tree gates passed
their required checks. Positive cases passed typed and executable replay,
with the new positive tree gates also proving their universal constructor
equations. Both complete raw runs and unchanged
pre/post source, module, executable, and external-input hashes are archived.
All thirteen unscored Church stretch cases remain bounded misses at both
budgets. The full checkpoint establishes acceptance at the committed source;
the development ablation above remains a separate fixture-specific measurement.

## Expected-type frontend gates

`tools/run_frontends.py` and `tests/benchmarks/frontend-fixtures/` add 8 required
cases independently of the original 29-session E8 manifest. They test `synth%`
and the `leant2` tactic under local data/proofs, a delayed shared implicit type,
genuine lets/local instances, and a fresh indexed Vec family. Indexed mapping
must satisfy universal nil/cons equations and executable Nat-to-Bool and
Bool-to-Nat observations. Its type and obligations are not replaced by a list
encoding or a supplied known result.

The 8 cases require 13 fresh Lean processes: 8 originals, 3 independent
replays of actual emitted tactic suggestions, and 2 separate impossible-goal
error files. Replay files import only Lean and repeat the required typed,
kernel-proof, and executable checks without the producer's adapter state.
Successful declarations, including opaque theorem proof bodies, must have no
holes or sorry dependencies and pass the standard axiom audit. Negative outer
theorems themselves pass that audit, while each deliberate failing file must
produce the expected frontend diagnostic and Lean error exit. These rejection
checks do not claim an engine completeness result.

```powershell
python tools/run_frontends.py --budget 10000 --out baseline-out/frontend-gates
```

Build before running the family directly; it neither builds nor treats artifact
fingerprints as proof of a rebuild. Its output directory must be new. The
clean-source [frontend checkpoint](frontends-2026-09-21/README.md) at `69221f1`
passed **832/832 across 13 families at both 10,000 and 5,000 ms**,
including all 8 frontend cases and 13 stages per budget. The 837 legacy
synthesis-query records remain a separate count. Both native executables and
the full recorded source/module/fixture inventories have identical pre/post
hashes. The archive independently rechecks stage sources, actual suggestions,
diagnostics, exits, exact raw inventories, and secondary raw-outcome/provider
history scoring. Historical checkpoint counts above retain their own scope.

The later library-API implementation changes upfront raw-engine contract
refutation to use the requested profile and retain a portable certificate.
The [library API guide](../library-api.md) describes its current validation
status, certificate fields, and the remaining limits of the proof portfolio.
The `69221f1` archive above predates this correction: that implementation used
`.standard` for the upfront check and discarded its accepted certificate.
Its expected-type frontends use `.standard` and do not expose behavioral
contracts, so those historical frontend gates did not test this policy gap.

## Library API regression checkpoint

The [API checkpoint](library-api-2026-09-21/README.md) repeats all **832/832
external checks across 13 families at both 10,000 and 5,000 ms** on `9ec21c8`,
after the portable, profile-respecting contract-refutation correction. The full
native build passes 68 jobs, including the API and refutation tests. The new
native cases are not an additional external harness or denominator increment.

The same 837 legacy synthesis-query records and 8 frontend cases/13 process
stages are retained at each budget. Native executable, source, module, and
external-fixture hashes match before and after; raw outcomes, session provider
histories, actual suggestions, fresh Lean-only replays, diagnostics and exits
are independently re-audited. The earlier frontend archive above remains
evidence for `69221f1`, with its original scope.

## Closed program-sketch checkpoint

The [sketch checkpoint](sketches-2026-09-21/README.md) passes **839/839 required
checks across 14 families at both 10,000 and 5,000 ms** on `c69f484`. All 29 E8
cases remain required. The new [sketch family](../../tests/sketches/README.md)
adds seven checks: a supplied two-hole fold, a local-context identity, correct
and wrong complete bodies, two malformed-hole controls, and literal False.
Its ten public process stages include three replays of the actual emitted
completion source in fresh Lean-only processes. The separate reference process
is a prerequisite, not an eighth case.

Both aggregate builds record 83 successful jobs, separate from the external
denominator. Each budget retains 202 raw artifacts, 837 legacy synthesis-query
records, and the existing 13 frontend stages. Pre/post source, executable,
module, and fixture hashes match; independent audits reconstruct actual source
and suggestions, outcomes, diagnostics, exits, and exact ZIP inventories.
The thirteen original unscored Church searches are bounded misses at both
budgets. Carrier-given Church completions and E2 closure remain separate work;
the earlier seven archives keep their original scope.

## Source provenance

Article cases cite
`docs/proposals/11-further-improvements/sections/01-evidence.tex`, Table 2, by
probe number. The Lean examples were checked against the installed
`leanprover/lean4:v4.34.0` source, without copying an external synthesis corpus:

| Cases | Core source equations |
| --- | --- |
| List map | `Init/Data/List/Basic.lean:477-478`, `map_nil`, `map_cons` |
| List head | `Init/Data/List/Basic.lean:385-386`, `head?_nil`, `head?_cons` |
| List tail | `Init/Data/List/Basic.lean:422-423`, `tail_nil`, `tail_cons` |
| Option map | `Init/Data/Option/Basic.lean:57-58`, `map_none`, `map_some` |
| Option default | `Init/Data/Option/Basic.lean:54-55`, `getD_none`, `getD_some` |
| Option present | `Init/Data/Option/Basic.lean:73-74`, `isSome_none`, `isSome_some` |
| Natural successor | `Init/Data/Nat/Basic.lean:152`, `succ_eq_add_one` |
| Natural predecessor | `Init/Data/Nat/Basic.lean:909-910`, `pred_zero`, `pred_succ` |
| Natural addition identity | `Nat.add_zero`, used by the right-identity instance at `Init/Data/Nat/Basic.lean:140` |

Except for the last universal proof target, these are concrete instances of
the source equations. Every full reference term and exact input/output
observation is recorded in `tests/benchmarks/extended.json`.
