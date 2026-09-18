# Implementation notes

How the engine in `Leant2/` relates to the unified proposal
(`docs/proposals/10-unified-proposal/Leant2.tex`), as of 2026-09-18. The
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
  search by an order of magnitude.
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
- **Residual evaluation on partial programs** uses the same deciders on the
  program with its open holes (including delayed assignments, substituted
  by `instantiatePartial`); the kernel is merely stuck on a hole, and a
  conjunct reducing to `false` abandons the branch. The holes the last
  evaluation got stuck on are remembered; while all of them are still open,
  re-evaluation is skipped. Refuted closed programs are memoized per query.
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
every failed alternative and every program checked.

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

## Measured

Everything in `docs/baseline/` and the harnesses in `tools/` (see the
README). The slowest scored case is the Church `maybeEither` probe at about
5 s; the partial operations Leant's ledger never accepted (`foldl1`,
`maximumBy`, ...) are reported as stretch cases and remain unsolved within
10 s.
