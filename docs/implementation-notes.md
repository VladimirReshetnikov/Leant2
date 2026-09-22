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
  outcome "provably no program satisfies the contract".
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
ledger counters and self times of the search steps print under
`set_option leant2.trace true`; `leant2.traceNodes` prints every node,
every failed alternative and every program checked; `leant2.skipRules`
disables named rules (`7a,7b,9,9b,9c,rec,guards,composition,residual`) for experiments, which is
how the cost of each rule on a slow query is measured. Timer collection is
now conditional on `leant2.trace`; ordinary searches avoid the profiling
clock reads and timer-reference updates, including at transaction boundaries.

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

Historical measurements remain in `docs/baseline/`, labeled by their own
revisions and budgets. These acceptance runs and profiling parity tests are
not controlled performance measurements and do not establish a node-cost
target or a general speedup.
