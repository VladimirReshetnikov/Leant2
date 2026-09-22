# Synthesis from a Lean metaprogram

The full library, native test, and executable build passes all 68 jobs.
Focused API, local-proof, and contract-refutation checks pass, and the exact
example below has compiled and run successfully. The complete
[API checkpoint](baseline/library-api-2026-09-21/README.md), tested at
`9ec21c81471a10dd72e56a1f330d502cfb19465d`, passes 832/832 external checks across
13 harnesses at both 10,000 and 5,000 ms. The API's native regression tests belong
to the aggregate build gate, separately from those external checks. The earlier
frontend archive remains evidence for `69221f1` and its original scope.

`Leant2.synthesize : Query → MetaM Outcome` accepts a closed, elaborated query
and returns native Lean expressions. Import `Leant2.API` for this entry point;
`import Leant2` also exports it. The smaller import does not require the command,
term, tactic, result-alias, or compiler-presentation modules.

Use this API when another metaprogram needs to inspect a candidate or proof.
For synthesis directly inside a declaration, use the separately documented
[`synth%` term or `leant2` tactic](../README.md#synthesis-inside-lean-declarations).

## Query inputs

| Field | Meaning | Default |
| --- | --- | --- |
| `target : Expr` | The closed type to inhabit | Required |
| `contract : Option Expr` | Optional closed expression of type `target → Prop` | `none` |
| `profile : Profile` | Axiom policy for accepted programs and evidence | `.standard` |
| `providers : Array Name` | Explicit ordinary-provider names | `#[]` |
| `budgetMs : Nat` | Cooperative search budget in milliseconds | `20000` |
| `maxCandidates : Nat` | Maximum accepted candidates; must be positive | `12` |
| `graceMs : Nat` | Additional enumeration allowance after the first result | `400` |

Preflight instantiates assignments already present in the input expressions.
The resulting target and contract must contain no unresolved expression or
universe metavariables, free variables, loose bound variables, or sorry terms.
Named universe parameters are supported. The target must be a well-formed type;
the contract must have the exact function type above. Unknown provider names
and a zero candidate limit are input errors.

The API does not elaborate syntax, infer missing types, generalize unresolved
caller universe holes, or automatically close the ambient local context. Search
runs at a fresh metavariable depth with an empty local context and local-instance
array. To supply hypotheses, construct a closed function type explicitly and
retain the matching argument map when reopening the result. Native
`mkForallFVars` is useful for this. The existing frontend local-query bridge has
its own policy for lets, hypotheses, instances, and original-goal replay; the
closed library API does not silently apply that policy.

Provider names do not constitute a whitelist of all constants that proof search
may use. The engine filters ordinary providers and orders the surviving entries
by explicit arity. It does not automatically add the frontend's curated or
session inventory. Native introduction, constructors, instance search, local
application after binders are introduced, proof tactics, and the engine's other
rules still operate. In particular, `providers := #[]` is not a promise that
library theorems or native search primitives are unavailable.

The existing `runQuery` remains a lower-level engine entry point. Its callers
are responsible for input preparation and state management; it retains the
command frontend's flexible-universe behavior. It is not interchangeable with
the frozen-input, caller-state-restoring `synthesize` boundary.

## Reading an outcome

Consume `Outcome` directly rather than parsing display text.

| Outcome | Interpretation |
| --- | --- |
| `.verified candidates ledger` | Ranked accepted terms, replayable at their recorded actual types |
| `.negative .impossible (some certificate) ledger` | Checked proof of `target → False` |
| `.negative .contractImpossible (some certificate) ledger` | Checked proof that every program at the target type violates the contract |
| `.negative .grammarExhausted none ledger` | The configured bounded search ended without an accepted result |
| `.negative .budgetExhausted none ledger` | A recognized resource bound ended the search without an accepted result |
| `.refutedAll rejected ledger` | Proposed programs were rejected; this is not a universal impossibility theorem |
| `.preflightError message` | Malformed input rejected before search |

The two semantic negative rows require checked certificates. Their presence is
different from a bounded miss. Grammar exhaustion, budget exhaustion, and
rejection of the proposed programs do not establish that the requested type or
contract has no inhabitant. Missing or wrong evidence for a semantic negative
is an output-validation exception; it must not be returned as certified
impossibility. There is no resumable-search token in this API.

The engine's upfront contract-refutation path gates the proof with
`query.profile`, retains the certificate, and replays it in the original
environment after temporary tactic state is restored. Focused native
[contract-refutation tests](../tests/Leant2Tests/ContractRefutation.lean) cover
strict, standard, and project-relative policies, portability, raw universe
placeholders, state restoration, and cancellation. Failure to obtain such a
certificate falls through to ordinary search. The preceding `69221f1`
implementation instead used `.standard` for that path and discarded its
certificate. Its archived complete acceptance does not establish this fix.

For lower-level raw queries, this probe generalizes remaining universe holes
once and keeps them rigid throughout proof search and replay; it does not
specialize the negative claim or assign the caller's placeholders. Expression
holes or pending universe equations conservatively skip the probe. The proof
portfolio is incomplete: rejecting a proof with forbidden axioms can leave a
bounded miss even when some permitted proof exists.

An `Accepted` value has the following fields:

| Field | Meaning |
| --- | --- |
| `program : Expr` | The accepted term; for a negative certificate, the refutation proof itself |
| `programType : Expr` | The actual type checked for that term |
| `levelParams : List Name` | Universe parameters needed when replaying its expressions |
| `proof : Expr` | Evidence for the program's behavioral contract, or `True.intro` when no separate contract was supplied to the gate |
| `axioms : Array Name` | Audited transitive axiom inventory for the program and proof |
| `classical : Bool` | Whether that inventory contains `Classical.choice` |

For contract impossibility, read `certificate.program` as the proof of
`∀ f : target, ¬ contract f`; `certificate.programType` is that statement.
`certificate.proof` is the trivial `True.intro` field, not the refutation.
The same distinction applies to a type-impossibility certificate.

Always inspect `candidate.programType`. A classical engine lane can specialize
universe parameters to `Prop`; the returned program is checked at that actual
specialized type, not relabelled as an inhabitant of the original polymorphic
query. A consumer assigning an existing goal must independently check the
original goal type with caller holes kept rigid and replay the program there.

The public export boundary accepts the original **target/contract pair**, or
the pair obtained by simultaneously replacing named universe parameters with
zero in both expressions, preserving successor and other level structure. It
independently rechecks the program and contract proof against the chosen pair;
an output matching neither pair is an output-validation error.

A universe parameter may occur only in the contract. Its specialization can
leave `programType` equal to the original target while changing the proposition
proved by `candidate.proof`. Matching `programType` alone therefore does not
establish the original behavioral contract. A consumer requiring the original
query must replay both `candidate.program : originalTarget` and
`candidate.proof : originalContract candidate.program`, keeping the original
universes rigid. The type of the returned proof can also be inspected with
native `inferType`; the API does not relabel a specialized proof.

## Trust and state

`query.profile` applies to the returned term and its evidence:

| Profile | Allowed axioms |
| --- | --- |
| `.strictConstructive` | None |
| `.standard` | `propext`, `Quot.sound`, `Classical.choice` |
| `.projectRelative extra` | Standard axioms plus the explicitly named extras |

`classical = false` does not imply an axiom-free proof: a proof using `propext`
can have that value. Inspect `axioms` or use the requested profile. A provider's
presence does not exempt its dependencies from the profile audit.

The API restores the caller's complete Core and Meta states on success, input
rejection, output-validation failure, and exceptional exits. This includes the
environment, assignments, messages, caches, and name-generator state represented
in those snapshots. It publishes no declaration, result alias, compiler adapter,
or executable definition. Trace output, elapsed time, and external/global IO
work are not undone. The returned ledger describes work performed, not state
that the caller must commit.

Before restoration, export expands only newly introduced theorem bodies, with
a finite expansion limit. Returned programs, types, and proofs then replay in
the original environment, and their axiom inventories are recomputed. Fresh
axioms, data definitions, or opaque values are not silently exported. This is
why a proof that happened to check in a temporary tactic environment is not
enough to return a library result.

If an apparently accepted output cannot be transported or replayed, the API
raises an output-validation exception after restoring state. It does not
convert that failure into `preflightError`, a bounded negative, or a theorem of
impossibility. Native cancellation and unrelated internal/runtime exceptions
also propagate; recognized search limits retain their ordinary result meaning.

The budget is cooperative. Input preparation, the bounded upfront proof attempt,
ranking, export, and replay can add elapsed time. `budgetMs` is not a hard timeout
for the whole metaprogram or process. Consumers needing a hard process deadline
must enforce it outside this API.

## Example: a closed polymorphic query

This checked snippet constructs `∀ (A : Sort u), A → A` without unresolved elaborator holes,
requests a strict result, and independently replays it at the original target.
It neither declares the result nor compiles it.

```lean
import Leant2.API

open Lean Meta Leant2

run_meta do
  let target := mkForall `A .default (mkSort (.param `u))
    (mkForall `x .default (.bvar 0) (.bvar 1))
  match ← Leant2.synthesize {
      target, providers := #[], profile := .strictConstructive,
      budgetMs := 5000, maxCandidates := 1, graceMs := 0 } with
  | .verified candidates _ =>
    let some candidate := candidates[0]? | throwError "empty verified result"
    let .ok _ ← kernelCheckAndAudit `LibraryExample candidate.program target
        candidate.levelParams false
      | throwError "candidate is not an inhabitant of the original type"
    logInfo m!"checked term: {candidate.program}"
  | .negative .impossible (some certificate) _ =>
    logInfo m!"checked refutation: {certificate.program}"
  | .negative .contractImpossible (some certificate) _ =>
    logInfo m!"checked contract refutation: {certificate.program}"
  | .negative .budgetExhausted _ _ =>
    throwError "bounded search did not find a result"
  | .preflightError message =>
    throwError "invalid synthesis query: {message}"
  | _ =>
    throwError "no candidate within the configured search"
```

Kernel acceptance and executable publication remain different operations. A
returned recursor expression may need the frontend's checked presentation
machinery before it can be compiled by Lean. This API deliberately returns the
checked expressions without performing that publication step.

The [native API tests](../tests/Leant2Tests/LibraryAPI.lean) cover input rejection,
original and specialized target/contract replay, contract-only specialization,
auxiliary theorem export, profile checks, invalid negative certificates, and
interruption after search has mutated state. The exact example above produces
`checked term: fun A x => x` when compiled with the library.

The six earlier acceptance archives remain tied to their original revisions
and scopes. The API checkpoint records the new complete external runs and
aggregate native build; focused API tests and compilation of the exact example
remain separate, explicitly identified evidence.
