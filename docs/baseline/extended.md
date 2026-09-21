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
| Sixteen article probes | 9 | 0 | 7 |
| Lean core List/Option/Nat | 8 | 0 | 1 |
| Negative controls | 0 | 4 | 0 |
| Total | 17 | 4 | 8 |

`TOTAL passed/21` covers the required capabilities and controls; `OPEN solved/8`
reports the remaining searches separately. Case selection changes the
denominators to the selected cases. An open search can exhaust its budget or
search bounds, or refute all proposed candidates. An exception, malformed or
incomplete output, process timeout, bad replay, or candidate satisfying the
literal `False` contract fails the run even in the open group. Because all
positive fixtures have checked reference inhabitants, a claim of uninhabitedness
or impossible contract for one of them also fails the run. A negative control
requires `provably no program satisfies the contract`; silence or timeout does
not establish the control.

The seven open article probes are power of two, indexed vector map, maximum,
dropping zeros, tree flattening, `Fin (n+1)`, and order transitivity. Natural
predecessor is the additional open core example. These classifications are
fixed expectations, not a list silently derived from whichever cases pass.
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

The nine protocol tests cover missing replay, named and unnamed Lean errors,
stderr and process failure, certified rejection versus timeout, executable
counterexamples, missing or duplicated query blocks, impossible claims on
inhabited open cases, and replay markers without candidates. Fixture validation
passed with Lean v4.34.0 during implementation. A preliminary seven-case run
against the original executable reproduced the list-sum compilation failure;
it is diagnostic evidence, not a completed 29-case acceptance receipt.

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
