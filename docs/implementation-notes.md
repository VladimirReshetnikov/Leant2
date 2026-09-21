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
  come from `synthInstance?` on closed goals and from instance declarations
  used as providers (which fix the arguments by unification). Class
  instances in the context are taken apart by projection, not `casesOn`.
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

`g.induction fvar (mkRecName ...)` with a constant motive on a recursive,
index-free inductive local other than `Nat`; the induction hypotheses are
the recursive-call capabilities. Tried first at the outermost level under a
contract, and as a late alternative otherwise. Nested induction on the
hypotheses is not attempted (it exploded on `Nat`).

## Contracts and residual evaluation (Part II, "behavior")

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
  changing the surrounding program invalidates it. There is still no
  evaluation at depth 0, and closed candidates still use the original
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

## Scheduling (Part II, "scheduling")

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
disables named rules (`7a,7b,9,9b,9c,residual`) for experiments, which is
how the cost of each rule on a slow query is measured. Timer collection is
now conditional on `leant2.trace`; ordinary searches avoid the profiling
clock reads and timer-reference updates, including at transaction boundaries.

## Acceptance (Part II, "acceptance")

As designed: universe metavariables are generalized jointly over program and
proof, the declaration is added with `addDeclCore` (kernel check), axioms are
collected and audited against the profile. The profile in the REPL is
project-relative: session axioms are accepted premises, `Classical.choice`
marks a candidate classical. The proof-service adapter, joint-mode patches
and proof-debt scheduling are not built; the portfolio above is the only
proof service.

## Ranking

Candidates are sorted by (unused explicit inputs, eliminators, size) and
de-duplicated by printed form. Instance binders do not count as inputs.
There is no learned or frequency-based ranking.

## Publication of accepted results (proposal 11, E1)

The published declaration retains the exact certified kernel expression.
Primitive recursors for supported single, non-indexed inductive families
receive a generated structurally recursive definition derived from the
recursor's reduction rules. A separately kernel-checked equality theorem,
audited against the standard axiom profile, registers Lean's `csimp` compiler
rewrite. Compilation therefore gets executable equations while kernel
reduction and the recorded axiom inventory continue to refer to the original
term. Displayed supported recursors use `match` and local recursive functions.

Validated cases include list and Nat recursors, polymorphic map and
identity, a custom binary tree, nested recursion, and printed-source round
trips that check for variable capture. This does not add natural recursion to
the search grammar. Indexed/mutual recursor adapters and providers without
executable code can still require a noncomputable binding, which is now
explicitly reported without post-acceptance compiler errors. Cancellation
and runtime exceptions still propagate. Realization metadata is registered
for result definitions so subsequent simplification can unfold them. Existing
`it1`, `it2`, ... names are preserved across queries; fresh-session replay is
required to avoid referring to an earlier binding with the same name.

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
searches and thirteen historical Church stretch searches remain unsolved at
both budgets; neither is counted in the required denominator. The baseline
checks synthesis outcome categories, while the extended suite independently
checks first-result binding and replay. Three ordinary-command errors in the
legacy transcripts remain outside that baseline score.

Historical measurements remain in `docs/baseline/`, labeled by their own
revisions and budgets. These acceptance runs and profiling parity tests are
not controlled performance measurements and do not establish a node-cost
target or a general speedup.
