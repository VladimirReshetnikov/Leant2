# Implementation notes

How the engine in `Leant2/` relates to the unified proposal
(`docs/proposals/10-unified-proposal/Leant2.tex`), as of 2026-09-21. The
proposal is the design; this page records what is built, where it takes a
simpler route than the design, and what the measurements taught. Section
numbers refer to the proposal.

## Search (Part II, "search")

Built as designed: one continuation-backtracking search over a list of
obligations (`Leant2/Search/Core.lean`), exact `Expr` as the semantic
authority, `Meta.saveState`/`restore` around every alternative, per-goal depth,
iterative deepening.

Departures and refinements:

- **Depth counts applications with arguments.** Exact locals and nullary
  constructors (`[]`, `none`, `true`) are free at depth 0. Depth-d then means
  "at most d nested applications", and the same term is found one pass
  earlier than under the proposal's accounting.
- **Deferral is a scheduling policy with three limits**, not a queue with
  priorities: a hole typed by a bare metavariable waits up to three times, a
  type hole (or type former) twice, a rigid-headed open goal once. A
  non-class proposition whose type still mentions holes (the contract on a
  partial program) yields to every other obligation without counting, and is
  decided once the program is closed. Class goals keep the limits, because an
  instance determines its type arguments.
- **Type invention** for `Sort` holes uses the local type variables, the
  types of locals, one level of arrows over them, a fixed closed frontier
  (`Unit`, `Empty`, `Bool`, `Nat`, `True`, `False`) and `PUnit.{?u}`, which
  fits `Type 1`, `Sort u` and `Prop`. Type formers are filled through
  introduction (`fun _ => Unit`).
- **Rule 7a, application at the accumulator type.** Lean's `apply` cannot
  see that `xs (R -> R) step seed x` has one more argument than
  `xs R step seed`, so a polymorphic local is also applied at `T -> T` for
  the goal `T`. This is exactly the Church `reverse`/`foldl` shape and the
  only invented instantiation tried; a general frontier here multiplied the
  search by an order of magnitude. The rule applies only to recursive
  eliminators, those with a step argument that threads the result type
  (`A -> R -> R` of a list, `R -> R` of a numeral): trying it on Church
  maybes and eithers made the `maybeEither` probe ten times slower for
  nothing.
- **Eliminator consumption.** A local of Church shape `forall R, ... -> R`
  is not applied again inside its own continuation arguments (tracked as a
  `consumed` list on each goal, propagated to every child). Nested folds over
  the same datum were the dominant junk on the Church probes; `pure`-like
  locals whose result is `F R` are not eliminators and may nest.
- **Classes are never built by constructor.** An instance produced by
  `Choice.mk True.intro` leaves the class arguments undetermined; instances
  come from `trySynthInstance` on closed goals and from instance declarations
  used as providers (which fix the arguments by unification). Class
  instances in the context are taken apart by projection, not `casesOn`.
  Unresolved class inputs produce a deferred probe through Lean's documented
  `.undef` result; unrelated internal exceptions are not search failures.
- **Session providers** exclude compiler- and `deriving`-generated
  auxiliaries (`noConfusion`, `casesOn`, `sizeOf`, `injEq`, ...), instances of
  decision and printing classes, `it1`-style result bindings, and any
  declaration recorded with `sorryAx`. Including the auxiliaries once turned
  a 0.6 s query into a budget timeout.

## Elimination and retrieval

Providers are head-filtered (a constant-headed conclusion must match the
target head) or demand-filtered (a variable-headed provider needs a local
whose type head appears among its argument heads); `always` bypasses the
filter for `False.elim` and `Empty.elim`. Projections of local structures
are heads. Forward application names the result of a local function whose
arguments are all exact locals, and of argument-less structure-valued
providers (instance arguments scheduled first). Case analysis on
multi-constructor locals is bounded by `maxSplits = 2`. No term index or
retrieval cache is built; the corpus does not need one yet.

## Structural recursion (gate G4)

The original rule uses `g.induction fvar (mkRecName ...)` with a constant motive on a recursive,
index-free inductive local other than `Nat`; the induction hypotheses are
the recursive-call capabilities. Tried first at the outermost level under a
contract, and as a late alternative otherwise. Nested induction on the
hypotheses is not attempted (it exploded on `Nat`).

A separate late tier now allows one outer induction on `Nat` or a supported
single-index recursive family. It uses native `g.induction` motive inference
and dependency reversion, transports consumed locals through the returned
substitution, and rolls back unsupported index shapes. The permission follows
root function introductions and the program component of a root contract;
ordinary application and constructor subgoals cannot start another extended
induction. Indexed families are tried before natural numbers. Mutual and
nested families, multiple indices in search, and compound major indices are
not supported by this tier.

Partial residual pruning is disabled inside these indexed induction branches
because the existing delayed-assignment representation has no established
dependent-closure invariant. Closed candidates still prove the original
contract and pass the acceptance gate. Focused gates synthesize predecessor
without providers, powers of two with addition alone, and polymorphic vector
map without providers; universal equations check their recursive behavior.

## Contracts and residual evaluation (Part II, "behavior")

Before ordinary proof construction, the engine checks an exact closed root
contract when native `instantiateMVars` exposes a completed `Subtype.mk`
program. The actual subtype predicate must match the configured contract, and
the pending goal must be exactly that contract applied to the program. Program,
type, and predicates must be closed; nonempty local contexts and disabled
proof portfolios retain their existing paths. This check does not expose
partial delayed assignments or use the observation cache.

The original precomputed deciders return refuted, proved, or stuck. Refutation
rejects the closed program with query-local cache accounting. A proof runs the
unchanged continuation inside an alternative; rejection restores it and allows
ordinary proofs to be tried. This matters when a decider-derived proof uses a
classical axiom but reflexivity can satisfy a strict constructive profile.
Missing or opaque deciders preserve fallback. Focused tests cover those cases,
native partial roots, mismatched predicates and sibling goals, unresolved
universes, local contradictions, accounting, rollback, and cancellation.

Negative pruning also respects the applicable axiom profile. A synthesized
decider can reduce to `false` using a forbidden axiom even when ordinary
reflexivity proves the original proposition without axioms. Such evidence is
inconclusive: residual and observation evaluation continue, and generic proof
evaluation retains its tactic fallback. The unreduced predicate/decider
dependencies are inspected before their erased Boolean can discard work.
Unsafe declarations are refused independently of the axiom allowlist: an
unchecked unsafe decider can also reduce to `false` without using any axioms,
while its evidence would fail the safe kernel gate.
Closed schemas abstracted over the program allow trusted partial refutations
without requiring every program hole to be filled. Unsupported open evidence
conservatively declines pruning.

Dependency judgments are cached only for identical schemas, allowed axioms,
and the same immutable environment object. Raw observation reductions remain
separate and every cached `false` is reauthorized under the current profile.
This prevents a permissive result or a reused declaration name after rollback
from authorizing strict pruning. True-decider proof construction is unchanged
and still passes the final kernel/axiom gate. Native controls cover all three
entry points, all four false-decision paths, trusted partial pruning, later
conjuncts, policy changes, and environment replacement.

The proposal's CEGIS loop, observational buckets and domain plugins are not
built. What is built covers the whole corpus:

- **Decision by kernel reduction.** The contract is split into conjuncts
  once per query and each conjunct's `Decidable` instance is synthesized
  once, abstracted over the program. A closed program is decided by
  `Kernel.whnf` on `decide (C_i p)`; every `true` yields the proof
  `of_decide_eq_true ... rfl`, assembled along the contract's `And` tree.
  Meta-level `whnf` was ten times slower and per-node `synthInstance?` was a
  third of the search time.
- **Residual evaluation on partial programs** now has per-observation
  reports (proposal 11, R3 stage 1). Besides `And`, preparation recognizes
  `Bool.and`, finite `List.all`, named Boolean checkers and `decide P = true`.
  Expansion is bounded, with unsupported forms retained as single
  observations. The decision instance explicitly supplied to `decide` is
  preserved. The kernel reports satisfied, refuted, or stuck for each checked
  observation; observations after a refutation are marked unevaluated.
  Blockers conservatively include holes in residual proof/type arguments and
  need not be minimal. Each cached residual is guarded by its input and
  observation identity in the current metavariable state; backtracking or
  changing the surrounding program invalidates it. Partial residual evaluation
  remains disabled at depth 0; the exact closed-root check above can run there.
  Closed candidates still use the original
  contract's deciders and proof construction. Refuted closed programs are
  memoized per query.
- **Outcome when the type is inhabited but the contract rejects.** Closed
  programs that fail their contract are counted as rejections, so such a
  query reports "N program(s) of the type proposed, none passed the
  contract" (the result algebra's rejected category) rather than an
  exhausted search.
- **Upfront refutation.** Before any search, `forall f, not (P f)` is tried
  with the tactic portfolio under a small heartbeat budget; success is the
  outcome "provably no program satisfies the contract", with a retained
  `Accepted` certificate. The exact negative statement is frozen once: existing
  universe assignments are instantiated and remaining placeholders become
  rigid parameters without assigning the caller's holes. Fresh theorem bodies
  may be copied before full Core/Meta rollback; the proof then passes the kernel
  gate in the original environment under `query.profile`. Expression holes or
  pending universe equations conservatively skip this probe. One proof attempt
  is charged when the worker starts and survives failure or policy rejection.
  The bounded portfolio may find only a proof forbidden by the profile;
  rejection then falls through to ordinary search, without claiming that no
  permitted proof exists.
  Focused native checks cover strict/standard/project-relative policies,
  portable certificates, raw universe placeholders, extraction, and cancellation.
  The preceding archived `69221f1` path used `.standard` and discarded evidence;
  that historical acceptance result is not evidence for this correction.
- Conjuncts without a decider (quantified statements) fall to the tactic
  portfolio `first | rfl | decide | simp | omega` on the closed program.

## Bounded constructive guards (proposal 11, A1)

The first conditional rule enumerates a finite grammar over at most four
most-recent natural-number locals: one orientation of each pairwise order
comparison, followed by equality-to-zero tests. It tries no arbitrary literals
or compound predicates. Local types containing unresolved expression holes
are excluded without assigning those holes. Known positive or negative guard
hypotheses suppress repeated tests. Order predicates use the native `LE.le`
instance key so Lean can retrieve their constructive `Decidable` instance.

Only the actual root contract subtype constructor enables guards for its
program field. Computational construction and structural recursion carry
that permission; proof goals, type goals, class goals, and open targets clear
it before constructing children. A same-result provider cannot enable the
root permission for its arguments. Native `byCasesDec` introduces the branch
hypotheses and consumes one depth step and one shared split. Its children
lose both guard and extended-induction permission, while unrelated sibling
obligations retain their own metadata.

Each split and its complete continuation are one transaction. Rejection,
ordinary exceptions, cancellation, and resource exits restore speculative
assignments, declarations, and diagnostics; work charges remain monotone.
The initial guarded continuation disables partial residual pruning, because
the existing delayed-assignment representation has no general soundness
argument for dependent guard closures. The closed candidate must still prove
the original contract and pass the ordinary kernel and trust-profile gate.

This implements a bounded part of A1. Predicate abduction, example-driven
decision trees, arbitrary nested guards, and general conditional completeness
remain open. The separate guard manifest requires maximum, minimum, and
drop-zero results to satisfy universal post-checks and held-out execution;
the provider-free Lean fixtures additionally require native guarded recursion.
Those distinct checks must not be conflated with public generic-filter reuse.

## Scheduling (Part II, "scheduling")

Outer nonindexed program induction also has a bounded branch-composition
prefix. Only the actual root program path can enable it; free introduction and
invertible setup preserve permission, while ordinary applications, guards,
other splits, and extended Nat/indexed induction do not acquire it. The prefix
tries exactly one and then two application heads, sharing those credits across
all sibling arguments and also respecting ordinary depth. Its leaves are at
most eight matching local data values and nullary constructors. Heads are
constructors and the first sixteen matching constant-result providers with at
most two explicit arguments, in their existing stable order. Native application
may solve dictionaries; unresolved proof, class, type, and function arguments
fall outside this grammar. Local function application, new guards, and new
recursion are left to the original search.

Each invocation shares 2,048 native/validation attempts, 128 continuation
admissions, 4,096 continuation rule applications, and a cooperative time slice
of at most 500 ms or one quarter of the remaining lane deadline. The one-head
grade gets one quarter of each allowance, reserving the rest for the two-head
grade without restarting the clock. Counters include active continuation work
and are never refunded. Every completed body is scoped and natively checked
before resuming the original obligations and acceptance gate. This is a finite
ordering heuristic, not a complete branch grammar or a hard wall-time bound;
crowded sessions can displace a useful provider from its capped prefix.

Direct native tests establish shared head/depth bounds, native dictionary
handling, admission boundaries, rollback, inherited quota ownership, successful
stop preservation, and fallback. Separate actual-search tests establish flag
provenance and a second binary recursive algebra. Public gates independently
check two tree traversals through universal constructor equations and held-out
execution. A known-term publication fixture additionally checks exact native
term retention and universal equivalence after independently parsing the
printed source; that fixture does not claim unassisted synthesis.

Lanes under one wall-clock budget, no settings: a cheap constructive pass,
a cheap refutation pass (type-only queries), a shallow classical pass (only
when the target mentions a proposition), a deeper constructive pass that
resumes iterative deepening at the first depth the cheap pass did not
finish, deeper classical and refutation passes. Under a contract without
classical lanes the constructive pass takes the whole budget at once, since
nothing else would run in between. The grace period after the first
accepted candidate (400 ms) is a deadline the search itself checks, so a
pass stops rather than running to the lane deadline. Lane and depth timings,
ledger counters and inclusive/exclusive elapsed spans of the search steps print under
`set_option leant2.trace true`; `leant2.traceNodes` prints every node,
every failed alternative and every program checked; `leant2.skipRules`
disables named rules (`7a,7b,9,9b,9c,rec,guards,composition,residual`) for experiments, which is
how rule-ablation experiments are configured. Timer collection is
conditional on `leant2.trace`; ordinary searches avoid the profiling
clock reads and timer-reference updates, including at transaction boundaries.

Profiling data belongs to one query and lives outside backtrackable state.
Native finalizers record partial elapsed time on cancellation, deadlines, and
other exceptions. Each label reports inclusive nanoseconds, exclusive
nanoseconds after subtracting immediate child spans, normal returns, and
exceptional exits; recursive uses of the same label remain separate active
spans. Lane reports show differences between closed snapshots. The
`lane.search` root covers search and its acceptance callbacks, so its exclusive
time includes unlabelled search work and instrumentation overhead. It excludes
query setup, preflight, ranking, result publication, and replay. Inclusive rows
overlap and must not be summed. The earlier diagnostic label `self times`
described inclusive successful-call timers and did not establish a whole-query
unattributed percentage. Injected-clock tests check exact nesting, exceptions,
rollback, query isolation, and disabled collection. These semantics do not
establish a speedup or close the proposal's native-sampling and node-cost gates.

Speculative tiers can use `withScopedBudget` for a cooperative local quota.
Each scope owns a private exception token; only that owner can turn its quota
exit into ordinary failure. Real cancellation and lane/grace deadlines take
priority, and false or exceptional exits restore native Meta/Core state before
propagating or returning. Work counters stay in IO and are never refunded.
Admission counters are checked before starting another operation so the last
admitted operation may finish. A successful callback bypasses heuristic quota
checks on exit, preserving an accepted candidate's stop request, while still
checking real interruption and deadlines. Such success may overshoot a local
quota; this is not a hard time bound. The branch-composition prefix uses this
primitive. Deterministic tests cover nested ownership, rollback, active
continuation accounting, admission boundaries, and accepted-stop preservation.

When a classical lane runs, its `Prop` specialization first instantiates
existing universe assignments, then substitutes zero for remaining universe
placeholders and named parameters. It preserves successors, so a fixed `Type`
does not become `Prop`, and refuses this specialization while universe
equations remain pending. The target and contract are frozen together for
construction, residual checks, and final acceptance. The returned candidate
records its actual specialized type; it is not advertised at the original
universe-polymorphic type. The original query's level placeholders remain
unchanged. This closes the gap where auto-bound query universes stayed flexible
and forced the classical search through unnecessary alternatives.

## Acceptance (Part II, "acceptance")

As designed: universe metavariables are generalized jointly over program and
proof, the declaration is added with `addDeclCore` (kernel check), axioms are
collected and audited against the profile. The profile in the REPL is
project-relative: session axioms are accepted premises, `Classical.choice`
marks a candidate classical. A bounded local-context proof service now
complements the closed-contract portfolio. Joint-mode patches and proof-debt
scheduling remain unimplemented.

`Proof/Local.lean` tries assumption/reflexivity, `simp_all`, and `omega`, with
a fresh scratch goal for each tier. The target and all local types and let
values must have no unresolved expression metavariables. Incoming expression
and universe holes remain rigid; this first service does not jointly solve
program holes and proofs. It can use local hypotheses and instances, including
contradictory hypotheses when the target is `False` or a closed false equality.

Each tier restores the full Meta/Core state on every exit. Extraction rejects
unfinished proofs, sorry, escaped locals or universes, and reported errors.
Native tactics can introduce auxiliary theorems, so extraction recursively
copies only newly created theorem bodies, with a 64-expansion cap. New axioms,
definitions, and opaque declarations cannot escape through this path. The
extracted expression is then checked against the original goal in the original
environment after restoration. Only that goal's assignment is committed; the
closed candidate still passes the ordinary kernel and profile gate.

Preparation, each tactic tier, and replay have separate heartbeat bounds;
zero never disables a bound. Deadline and cancellation checks surround these
stages. Ordinary tactic failure and exhausted local resources leave search
unresolved, not logically refuted. Proof-attempt charges and lane deadlines
remain outside rollback.

Search transactions use result-aware finalizers so native cancellation and
resource exceptions restore state even when Lean's ordinary exception handler
skips them. `attempt` commits any successful value, including `false`, while
an `alternative` commits only `true`. Lane boundaries consume only recognized
lane/grace deadlines and native heartbeat/recursion limits; user cancellation
and unrelated internal exceptions propagate. The earlier of the lane and
grace deadlines determines whether the stop counts as a timeout. Upfront
contract refutation restores state and receives a fresh heartbeat origin.

## Ranking

Candidates are sorted by (unused explicit inputs, eliminators, size) and
de-duplicated by printed form. Instance binders do not count as inputs.
There is no learned or frequency-based ranking.

## Library API boundary

`Leant2.synthesize : Query → MetaM Outcome` adds a closed-input library boundary
over the lower-level `runQuery`. Input preparation instantiates existing
assignments, then rejects unresolved expression/universe holes, escaped locals,
loose bound variables, sorry, ill-typed targets/contracts, unknown providers,
and a zero candidate limit. Named universe parameters remain supported. Search
runs with an empty local context and local-instance array at a fresh metavariable
depth. This boundary does not replace the command frontend's flexible-universe
query preparation or the term/tactic frontend's local-context closure policy.

The explicit provider array supplies ordinary heads; native rules, instances,
and proof automation remain available. No curated/session inventory is added
automatically. A returned candidate retains its actual `programType`, which
may reflect the engine's `Prop` specialization. Transport checks both program
and proof at their captured types and re-audits them under `query.profile` in
the original environment. Public output must also match the original target and
contract together, or their simultaneous zero-universe substitution. The program
and proof are independently replayed against that chosen pair. Specialization
may affect only a universe parameter in the contract, leaving `programType`
unchanged. Consumers needing the original query must therefore replay both the
original target and its applied contract. Specialized evidence is not silently
promoted to the original polymorphic query.

The API restores complete caller Core/Meta snapshots on every exit and publishes
no aliases, declarations, compiler adapters, or executable definitions. Newly
created theorem bodies may be copied before restoration; fresh axioms, opaque
values, and data definitions cannot escape that way. A failed export or replay
raises an output-validation exception after restoration, distinct from malformed
input and bounded search failure. Semantic negatives require a present
certificate checked at the original refutation statement and selected profile;
the refutation is `certificate.program`, while its auxiliary `proof` field is
the trivial True witness. Budgeted misses carry no impossibility certificate.
Trace IO and work already performed are not undone by state restoration.

Focused native API, local-proof, and contract-refutation tests pass, including
actual `Prop` specialization, contract-only specialization, invalid-output
rejection, auxiliary theorem export, and interruption after search mutations.
At the API checkpoint, `lake build Leant2 Leant2Tests leant2` passed all 68 jobs.
The [library guide](library-api.md) records the full contract and an exact
example that compiled and ran successfully. The
[API checkpoint](baseline/library-api-2026-09-21/README.md) verifies `9ec21c8`
with all 832 external checks at both budgets and the aggregate native build.
The earlier frontend archive remains tied to `69221f1`.
Budgets remain cooperative, including the existing separate setup,
proof, ranking, and export work outside the search deadline.

## Publication of accepted results (proposal 11, E1)

The published declaration retains the exact certified kernel expression.
Primitive recursors for supported single inductive families
receive a generated structurally recursive definition derived from the
recursor's reduction rules. A separately kernel-checked equality theorem,
audited against the standard axiom profile, registers Lean's `csimp` compiler
rewrite. Compilation therefore gets executable equations while kernel
reduction and the recorded axiom inventory continue to refer to the original
term. Displayed supported recursors use `match` and local recursive functions.

Validated cases include list and Nat recursors, polymorphic map and
identity, a custom binary tree, nested uses of supported recursion, and
printed-source round trips that check for variable capture. Indexed adapters
support varying indices and the major premise after a fixed prefix of
parameters, motives, and branches. Tests include universe-polymorphic vector
map, a two-index family, and a dependent motive with proof fields; they check
execution and re-elaboration of printed source as well as kernel equality.
Proof terms are retained in printed dependent expressions. Mutual and nested
inductive-family adapters and providers without executable code can still
require a noncomputable binding, which is
explicitly reported without post-acceptance compiler errors. Cancellation
and runtime exceptions still propagate. Realization metadata is registered
for result definitions so subsequent simplification can unfold them.

`Frontend/Results.lean` publishes each batch under fresh immutable kernel
names, then atomically replaces transient aliases for `it1`, `it2`, ... and
bare `it`. Definitions that already refer to an earlier result retain that
meaning. A smaller batch removes stale numbered aliases; a well-formed
unsuccessful query clears the numbered batch but preserves bare `it`.
Preflight failures preserve both. Bare expression evaluation uses the same
publication gate and updates only `it` after successful evaluation. Command
state snapshots restore bindings on undo or failure. Namespace and root
qualified aliases are supported, user-name collisions are rejected, and the
generated declarations are excluded from session provider discovery. Aliases
are session state and are not exported when another module imports the file.

## Expected-type term and tactic frontends

`synth%` and `by leant2` use a shared local-query service. Preparation closes
accessible local declarations in dependency order, preserves genuine lets,
and generalizes nondependent `have` declarations as assumptions. Auxiliary
recursive placeholders and implementation details are excluded. Unresolved
expression or universe holes in the expected type or accessible context defer
term elaboration; the tactic requires them to be resolved already. Search runs
under a fresh metavariable depth and an empty local context, with the complete
native Core/Meta state restored afterward.

The postponement boundary is conservative: an inferred universe in a data
definition such as `(A : Sort _)` may be generalized only after Lean's final
no-postponement synthesis pass, so that form is rejected. An explicit named
universe works, and expression holes determined by later arguments can be
postponed successfully. The frontend does not guess or assign either kind of
incoming hole.

Candidates are visited in the engine's existing ranked order and independently
checked at the original closed type, then applied to the original local
arguments and checked again. The frontend rejects escaped locals, holes,
sorry, and new universe parameters. This original-type replay prevents a
classical lane's specialized answer from escaping at a polymorphic expected
type. The standard axiom profile accepts local hypotheses as parameters and
rejects arbitrary project axioms. The command and REPL profiles remain
project-relative. An unsuccessful bounded search reports a synthesis failure;
it does not certify mathematical impossibility of the enclosing goal.

The successful frontend returns the exact certified expression. Presentation
preparation also works from `TermElabM`: it uses synchronous native declaration
elaboration, supports private names and asynchronous declaration prefixes,
and restores the caller's elaborator state. Compiler rewrites created inside
an asynchronous declaration use local registration in that branch. Unsupported
adapters remain subject to Lean's ordinary computability checks. Frontend
failure and native cancellation restore Core, Meta, Term, and tactic state;
there are no result aliases or changes to user `it` declarations.

Source suggestions are speculative. They must elaborate without new errors,
solve the original goal, preserve sibling goals, and pass the original-type
and standard-profile check. When native `let rec` elaboration leaves pending
auxiliary holes, a fresh temporary declaration runs Lean's complete lifting
pipeline before the final check; no unfinished expression is accepted. All
temporary declarations and elaborator state are then discarded.
The actual emitted suggestion text is also tested
by the public harness in a second fresh file importing only Lean, so that
adapter declarations or the original elaborator state cannot hide a missing
dependency. A source-presentation failure does not invalidate an already
checked synthesis result. Contextual contract lifting and code actions are not
implemented. Closed whole-function sketches have a separate command below.

The 8 public frontend cases were integrated into `run_all.py`, bringing the
frontend checkpoint to 832 required checks across 13 harnesses. Their 13 fresh process stages
comprise 8 original files, 3 suggestion replays, and 2 separate
expected-error files. Both complete budgets now pass at the committed source,
as recorded in the [frontend checkpoint](baseline/frontends-2026-09-21/README.md). Positive declarations are audited through
opaque theorem bodies as well as definitions; the negative wrappers themselves
must also have complete, standard-profile proofs. The frontend runner retains
generated sources, JSON diagnostics, stderr, stage exit codes, and pre/post
hashes of source, native Lean, and compiled dependencies. The complete archive
additionally binds `leant2.exe` and external fixtures; its fresh frontend process
counts are separate from the legacy synthesis-query counts below.

Focused public runs passed all eight cases and thirteen stages at both 5 s and
10 s per search with identical captured inputs. The full 62-job native build,
39 Python tools tests, and 19 Python benchmark tests also passed. These focused
development results remain separate evidence from the complete archived runs.

## Closed whole-function sketches

`#leant2_sketch f : T := body where P f` completes zero to four explicitly
named holes in a supplied closed body. The optional contract constrains the
entire completed function. The identifier binds only inside that contract;
results use the existing `it1`, ... aliases. The [sketch guide](sketches.md)
contains examples and the supported boundary.

Preparation elaborates the real body in a fresh native metavariable depth,
owns each explicit pending goal, and checks its frozen type and local context.
Native delayed closures are inspected without treating their wrappers as
assignable holes. Anonymous, duplicate, type/motive/dictionary, and unresolved
context-dependent holes are refused. Registered expression-error obligations
are also inspected when elaboration erases their subterms. Newly introduced
declarations and unfinished recursive lifting are unsupported. Preparation and
its consumer restore complete Core, Meta, and Term state on every exit.

`enumerateInitialized` reuses the existing continuation engine with the
prepared expression as its actual root. Each depth restores the same complete
prepared snapshot. Program holes are ordered stably by telescope arity, followed
by the one whole-contract proof. All providers and every owned goal remain
available; a failed complete contract backtracks across the entire continuation.
Partial residual pruning is disabled for these native closure graphs, while
exact closed-root evaluation remains available. Both initialized and ordinary
enumeration deduplicate programs only after acceptance, preserving different
proofs of a program after an axiom-profile rejection.

Completed programs and proofs pass the selected gate, bounded theorem-only
transport, and an independent gate at the exact original target and unreduced
contract in the caller's original environment. There is no unconstrained or
Prop-specialized sketch fallback. Fixed fragments receive the same axiom audit
as synthesized ones. The command independently restores publication state on
exceptions, including actual cancellation after a provisional alias is bound.
Supplementary source for the first result is tested by fresh Lean-only replay;
its display alone does not establish replayability for arbitrary completions.

The promoted public sketch runner passes all seven cases at both 5 s and 10 s, with
identical captured inputs. Each run has ten public stages (seven originals and
three emitted-source replays) and one separate Lean-only reference/control
process. The reference process must pass but does not add a scored case.
Wrong complete bodies require a recorded rejection; malformed inputs require
the intended preparation error; fresh negative processes leave neither bare
nor numbered aliases. The configured aggregate is now 839 checks across 14
harnesses. The complete [sketch checkpoint](baseline/sketches-2026-09-21/README.md)
passes all 839 at both budgets on `c69f484`, with unchanged pre/post inputs and
independent reconstruction of actual emitted-source replays. The previous
832-check API checkpoint retains its own revision and scope.

The final source passes the 83-job aggregate native gate after serial module
builds, all 76 Python harness tests, and the exact guide/README examples with
three accepted sketch outcomes. An earlier parallel aggregate attempt exhausted
host resources; its failure log remains separate from the successful serial
rebuild. The unsafe-pruning regressions and public runs include the final
unsafe-declaration guard.

This is the initial closed command for E2. All thirteen original open Church
stretch searches remain unscored, and the proposed thirteen carrier-given
completions remain to be established separately. Contextual contract lifting,
term/definition sketch syntax, arbitrary dependent sketches, carrier invention,
and editor actions remain open.

## Initial next-phase coverage

Proposal 11's P1 is **partially implemented**, not closed. E1 publication,
R3 stage-1 reports, opt-in profiling, and an initial local E8 benchmark suite
are implemented. The suite reconstructs the sixteen article probes and adds
Lean-specific examples with independent executable replay; it does not yet
port the external benchmark collections. A proposed cache of local type
facts was removed after its performance benefit could not be established.
Sampling-profile attribution, per-local caching, the under-1-ms node-cost
gate, external benchmark ports, first-candidate timing, and reference ranking
remain open. See [the extended benchmark notes](baseline/extended.md) for
the precise measurement and replay boundaries.

## Measured

Implementation commit `87ed037` passed **787/787 scored cases** across
all seven harnesses at both 10 s and 5 s per query, with clean working trees
and an unchanged executable. The [2026-09-21 checkpoint](baseline/p1-2026-09-21/README.md)
records the full results and raw transcripts. The eight extended open
searches and thirteen historical Church stretch searches were unsolved at
both budgets; neither is counted in the required denominator. The baseline
checks synthesis outcome categories, while the extended suite independently
checks first-result binding and replay. Three ordinary-command errors in those
legacy transcripts were outside that baseline score.

Implementation commit `555236a` passed **805/805 required checks across nine
harnesses at both budgets**, including five new recursion gates, ten
result-binding sessions, and the three newly required original
predecessor/power/vector probes. Its full Lean build also passed the focused
induction, publication, and result-binding tests. The
[induction checkpoint](baseline/induction-2026-09-21/README.md) archives both
runs and verifies their source, executable, module, and input hashes against
a pre-run snapshot. Five extended open searches and thirteen Church stretch
cases were unsolved at that checkpoint. These scores include overlapping synthesis goals with
different acceptance checks, not 805 distinct benchmark problems. The targeted
legacy manual transcript now evaluates bare `it * 10` and refreshed `it2`
successfully. The Option call in `synth-prove` still omits the two explicit
type arguments required by its requested type, matching an error already
present in Leant's golden transcript; it is not a stale result binding.

Implementation commit `914680d` passed **813/813 required checks across ten
harnesses at both budgets**. The [local-proof checkpoint](baseline/local-proofs-2026-09-21/README.md)
adds the two required original Fin/transitivity probes and six independent
local-proof gates. The full Lean build includes adversarial proof extraction,
original-environment replay, cancellation and state rollback, and classical
universe-specialization checks. Both runs preserve the same source, executable,
compiled modules, and external inputs. The three remaining E8 searches and
thirteen Church stretch searches were unsolved at that checkpoint; neither group contributes
to the fixed score. The legacy baseline's documented ordinary Option-call
error is unchanged and outside its synthesis-category score.

Implementation commit `ce31d3a` passed **820/820 required checks across eleven
harnesses at both budgets**. The [constructive guard checkpoint](baseline/guards-2026-09-21/README.md)
includes required original maximum/drop-zero probes and five public guard
gates with universal post-checks and held-out execution. Separate empty-provider
Lean fixtures verify native guarded recursion, all three universal equations,
exact-term publication, and printed-source equivalence. Both complete runs
preserve the same 123 recorded source files, 27 compiled module artifacts,
executable, and 350 external inputs. Tree inorder was the only open E8 search
at that checkpoint; it and the thirteen Church stretch cases were bounded misses at
both budgets. The public drop-zero candidate reuses `List.filter` with a
synthesized guard predicate; the provider-free fixture establishes the
separate recursive construction capability.

Implementation commit `313a441` passed **824/824 required checks across twelve
harnesses at both budgets**. The [tree-composition checkpoint](baseline/tree-composition-2026-09-21/README.md)
includes all 29 original E8 cases and three additional tree gates. The positive
public gates check universal constructor equations and held-out execution with
ordinary providers, including `List.append`; separate native tests establish
the bounded tier's permissions and publication of a supplied recursor term.
The two runs preserve identical pre/post hashes for 130 source/configuration
files, 32 compiled module artifacts, the executable, and 350 external fixtures.
Each run retains 117 raw artifacts and 837 synthesis query records. The required
score counts 824 acceptance checks, with overlapping goals and 13 unscored
Church stretch queries; all thirteen remain bounded misses at both budgets.
The legacy baseline's two intended preflight diagnostics and one unscored
ordinary Option-call error are independently checked at their query boundaries.

Implementation commit `69221f1` passed **832/832 required checks across
13 harnesses at both 10 s and 5 s per search**. The
[frontend checkpoint](baseline/frontends-2026-09-21/README.md) adds 8 required
term/tactic cases and 13 fresh Lean process stages: 8 originals, 3 actual
suggestion replays importing only Lean, and 2 intentional error files.
Each budget separately retains 837 legacy synthesis-query records, including
22 REPL sessions, without counting frontend processes or source syntax occurrences
as legacy queries. All 29 E8 cases remain required; Church stretches remain
outside the score, with their actual per-budget outcomes recorded in the archive.

Both runs preserve identical pre/post hashes for source, `leant2.exe`, native
Lean, the complete recorded compiled-module inventory, and
external fixtures. The archive re-extracts emitted tactic text and reconstructs
fresh replay sources, reclassifies JSON diagnostics and process exits, and checks
exact stage inventories. It also reconstructs recursive/context/corpus/Church
and provider-session inputs and rescores their raw outcomes against the captured
expectations, including exact provider histories. This additional semantic audit
does not infer success from an old green summary and is separate from protocol
and denominator checks. Earlier archives retain their original scope.

Implementation commit `9ec21c8` passed **832/832 required external checks
across 13 harnesses at both 10 s and 5 s per search**. The
[API checkpoint](baseline/library-api-2026-09-21/README.md) repeats the complete
suite after the isolated library API and profile-respecting refutation changes.
The aggregate build passes 68 jobs, including API/refutation regression modules;
native test cases are not added to the external 832-check denominator.

Both runs retain the 837 legacy synthesis-query records and the separate
8 frontend cases/13 fresh-process stages per budget, including 3 actual
suggestion replays and 2 expected-error stages. Source, both executables,
all recorded compiled modules, and external fixture fingerprints are unchanged
before and after. The archive independently rechecks raw outcomes, provider
histories, generated replay files, diagnostics, exits, and exact ZIP contents.
The six earlier archives retain their own revisions and evidence boundaries.

Implementation commit `c69f484` passed **839/839 required external checks
across 14 harnesses at both 10 s and 5 s per search**. The
[sketch checkpoint](baseline/sketches-2026-09-21/README.md) retains the 837 legacy
synthesis-query records and 8 frontend cases/13 processes at each budget,
adding 7 sketch cases/10 public stages and one separate uncounted reference
process. Both full build logs record 83 successful jobs, including native
sketch, alternative-acceptance, and pruning-profile regressions.

Each raw ZIP has 202 files and 46 empty stderr streams. All three actual sketch
source replays, two expected preparation errors, rejection of the wrong fixed
body, and the certified False-contract category are independently rechecked.
The 173 source/configuration hashes, 57 recorded compiled-module hashes,
350 external-fixture hashes, and both native executable hashes are unchanged.
All thirteen original Church stretches remain bounded misses; the seven
earlier archives retain their Git trees and working bytes. The fixed-carrier
Church completion experiments remain a separate implementation track.

Historical measurements remain in `docs/baseline/`, labeled by their own
revisions and budgets. These acceptance runs and profiling parity tests are
not controlled performance measurements and do not establish a node-cost
target or a general speedup.
