Leant2 is contemplated as exclusively Lean-oriented successor of Djex & Leant, implemented in Lean.

* https://github.com/VladimirReshetnikov/Djex (`C:\Djex\` locally)
* https://github.com/VladimirReshetnikov/Leant (`C:\Leant\` locally)

These tools allow to automatically generate implementations for a subset of Lean type signatures with optional additional behavioral constraints. But they are implemented in Haskell, internally use Haskell approximations of Lean types, and also Djex has a Haskell frontend and needs to remain compatible with it. All these put certain limitations on their Lean capabilities. We would like to create a successor (let's name it Leant2), which is implemented in Lean, has only Lean frontend, and is designed specifically to handle Lean types (+ behavioral constraints). Of course, it couldn't possibly be made to autogenerate implementations for *all* inhabited Lean types (because that's untractable and possibly undecidable problem); but still we would like it to be able to handle a large fraction of Lean types that occur in practice.

A sibling project (we might even merge them if they converge):

* https://github.com/VladimirReshetnikov/Forge (`C:\Forge\` locally)

We may freely borrow any Lean code and ideas from there.

## Design

The design is in `docs/proposals/`: nine independent proposals (`01-` to `09-`)
and the unified proposal `10-unified-proposal/Leant2.pdf` that consolidates
them. The implementation below follows the unified proposal; section numbers
in the source comments refer to it. The plan for what comes next, including
the open algorithmic problems and where outside expertise would help, is
`docs/proposals/11-further-improvements/Leant2-next.pdf`.

## Implementation status

[docs/implementation-notes.md](docs/implementation-notes.md) records how the
built engine relates to the proposal: what is implemented as designed, where
it takes a simpler route, and what the measurements taught.

Lean 4.34.0, core only (no Mathlib). `lake build` builds the library, the
tests, and the `leant2` REPL executable.

- `Leant2/Search/Core.lean`: continuation-backtracking search over
  obligations with per-goal depth, deferral of type and open holes, the rule
  set (introduction, invertible destructuring, exact locals, instance
  resolution, projections as heads, constructors, local application, local
  application at the accumulator type `T -> T`, forward application, case
  splits, structural recursion from recursor metadata, head- and
  demand-filtered providers, a proof portfolio on closed propositions and
  bounded proof search under local hypotheses,
  classical splits). Behavioral contracts are decided by kernel reduction,
  conjunct by conjunct, on partial programs as well (residual evaluation).
- `Leant2/Accept/Gate.lean`: the acceptance gate: universe generalization,
  synchronous kernel check, axiom audit against a trust profile.
- `Leant2/Proof/Local.lean`: isolated assumption/reflexivity, simplification,
  and arithmetic proof attempts under the original local context. Incoming
  holes remain rigid, temporary tactic state is restored, and an extracted
  proof must replay in the original environment before its assignment commits.
- `Leant2/Behavior/Observations.lean`: finite observations extracted from
  conjunctions, Boolean checkers and `List.all`, with per-observation kernel
  results and caches guarded against changes during backtracking. Acceptance
  still requires a proof of the original contract.
- `Leant2/Frontend/Presentation.lean`: executable presentations of certified
  recursor terms through generated structural definitions and kernel-checked
  compiler rewrite proofs. The published definition retains the original
  certified term; unsupported compilation is explicitly reported as
  noncomputable.
- `Leant2/Engine.lean`: the adaptive lanes under one wall-clock budget
  (constructive, refutation, deeper constructive, classical, deeper
  refutation). There is no engine-selection switch; legacy `:set` commands
  are ignored.
- `Leant2/Native/Transaction.lean`: cancellation-safe rollback and owned
  cooperative quotas for speculative search tiers. Failed scopes restore
  native state without refunding work; successful stop requests survive
  local quota exhaustion. The bounded branch-composition tier uses this
  primitive to share limits across its alternatives and continuations.
- `Leant2/Frontend/Command.lean`: `#leant2 T`, `#leant2 f : T where P`,
  `#leant2_check`, `#leant2_none`; results are bound as `it1`, `it2`, ...
  Each successful query refreshes the numbered names and bare `it` through
  aliases to immutable kernel declarations. Earlier definitions keep their
  original meaning, stale numbered results disappear, and undo restores the
  previous aliases. User declarations are never overwritten.
- `Leant2/Frontend/Term.lean`: `synth%` terms and the `leant2` tactic synthesize
  at the enclosing expected type, using accessible local hypotheses, data,
  genuine lets, and instances. Every answer is checked again at that original
  type under the standard axiom profile. These frontends do not publish result
  aliases. The tactic offers source suggestions only after replay validation.
- `Main.lean`: the compatibility REPL that consumes Leant transcripts
  (`:synth`, `:set` ignored, `:reset`, `:undo`, `:{ ... :}` blocks,
  `:providers`, `:prove`, declarations, `#eval`). Bare expressions evaluate
  through `#leant2_eval` and update `it` after successful evaluation.
  Comment-only input is ignored without consuming an undo entry.

A late search tier adds bounded outer induction on `Nat` and supported
single-index inductive families using Lean's native dependent induction.
Predecessor, powers of two, and polymorphic indexed vector map now pass
synthesis and universal equation checks with the corresponding library
implementations withheld. Executable publication also supports single-family
indexed recursors with multiple indices and dependent motives. These are
separate search and publication capabilities; arbitrary indexed, mutual, and
nested induction remain outside the search grammar.

Contract-directed program search also has a bounded constructive guard rule.
It can branch on comparisons between natural-number locals and on equality
to zero, using Lean's native decidable case analysis. The finite grammar
permits one guard on each enabled program path and keeps the original
closed-contract and kernel checks. Maximum, minimum, and recursive drop-zero
functions pass provider-free construction and universal correctness checks,
including executable publication and printed-source round trips. The rule
does not infer predicates from examples or implement general decision-tree
learning.

A bounded branch-composition tier gives outer nonindexed induction branches
an early search over one- and two-head expressions. It combines exact local
data, constructors, and a small prefix of ordinary providers; the original
search remains available afterward. Complete root programs also get an early
check of their exact original contract before ordinary proof construction.
Stuck checks retain proof search, and rejecting one computed proof still
allows an alternate proof to pass the trust profile. Tree inorder and a
second binary-tree traversal pass public synthesis, universal constructor
equations, and held-out execution at both existing budgets. The complete
tree-composition checkpoint below archives these results with all other
required harnesses.

### Synthesis inside Lean declarations

Import `Leant2` to use the expected-type frontends:

```lean
import Leant2

def identity (A : Sort u) (x : A) : A := synth%

def applyLocal (A B : Type) (f : A → B) (a : A) : B := by
  leant2

theorem implication (p q : Prop) (hp : p) (hpq : p → q) : q := by
  leant2
```

`set_option leant2.budgetMs 5000` changes the search budget. `synth%` requires
an expected type and can postpone until surrounding elaboration determines it.
Search never assigns unresolved caller holes. Named universe parameters stay
rigid, and a candidate must replay at the original expected type even if an
engine lane found an answer to a specialized type. Local hypotheses are accepted
premises; global axioms must pass the standard Lean axiom profile. This is
stricter than the command and REPL frontends' project-relative profile.

Use explicit universe parameters when Lean would otherwise generalize them
only after elaborating the body: `def id (A : Sort u) (x : A) : A := synth%`
works, while replacing `Sort u` with `Sort _` can leave a universe hole that
this frontend deliberately refuses. Later-resolved expression types, such as
the shared type in `(fun {A : Type} (x y : A) => (x, y)) synth% (7 : Nat)`, can
be postponed and synthesized once the type becomes known.

The returned term is the checked kernel expression. Supported recursion gets
the same checked compiler adapters used by command publication. The tactic's
`Try this` text is an independently checked source suggestion; successful
synthesis can still report that no replayable suggestion was available.
These are type-directed frontends; contextual behavioral-contract syntax,
partial-program sketches, and editor code actions remain future work.

### The baseline

The minimal acceptance baseline is Leant's `:synth` golden corpus
(`C:\Leant\test\synth-*.txt`), scored by outcome category rather than by
transcript text (unified proposal, Definition 1.5):

```bash
lake build
python tools/run_baseline.py --budget 10000
```

The harness runs every transcript through the REPL, writes the outputs to
`baseline-out/`, and prints per-fixture scores and a total. Recorded runs
are in `docs/baseline/`.

Further harnesses replay Leant's extended tiers through the same REPL,
each case once (Leant ran them per engine):

```bash
python tools/run_recursive.py --budget 10000   # Leant test-recursive, 9 cases
python tools/run_church.py --budget 10000      # Leant test-church, 28 scored probes + 13 open stretch cases
python tools/run_context.py --budget 10000     # Leant test-behavioral simplification + test-context production, products, selections, constructors, universes, scheduling: 95 cases
python tools/run_corpus.py --budget 10000      # Leant test-church signature corpus, 350 type-only queries
python tools/run_session.py                    # Leant session provider-identity suite (blocks, :undo, rejected declarations)
python tools/run_extended.py --budget 10000     # 29 independent sessions with typed and executable result replay
python tools/run_extended.py --manifest tests/benchmarks/recursion.json --budget 10000 # 3 recursion gates + 2 impossible controls
python tools/run_extended.py --manifest tests/benchmarks/local-proofs.json --budget 10000 # 5 local-proof gates + 1 impossible control
python tools/run_extended.py --manifest tests/benchmarks/guards.json --budget 10000 # 3 guarded-program gates + 2 impossible controls
python tools/run_extended.py --manifest tests/benchmarks/tree-composition.json --budget 10000 # 2 tree traversal gates + 1 impossible control
python tools/run_results.py --budget 10000      # 10 result-binding and evaluation sessions
python tools/run_frontends.py --budget 10000 --out baseline-out/frontends # 8 fresh-file term/tactic gates
```

`python tools/run_all.py` builds everything and runs the baseline and all
twelve additional harnesses, printing one summary table. It fails on a harness
process error as well as an incomplete score. The baseline also treats
missing query output as a failure instead of reducing its denominator, and
checks query diagnostics through explicit REPL completion markers. It still
scores synthesis outcomes; the extended suite separately checks execution.
Complete harness logs and a JSON summary are saved under
`baseline-out/run-all/` (override with `--out`). The secondary harnesses also
retain their raw input, stdout and stderr, require every expected query to
complete, and reject diagnostics even after a candidate has been printed.
Literal `False` controls require a certified contract refutation; silence
and timeouts do not pass them.

The configured aggregate now contains 832 required checks. The eight new
frontend cases add fresh Lean files, three independent replays of actual tactic
suggestions in files importing only Lean, and two separate expected-error
processes for impossible goals. This configuration is not a claim that a full
832-check run has passed; the latest complete archived run is recorded below.
Focused frontend runs pass all eight cases at both 5 s and 10 s per search,
including all thirteen process stages, with identical captured inputs. The
complete library, tests, and executable build also passes all 62 jobs.
The frontend runner requires a fresh output directory and records input hashes
before and after its processes. Build before running it directly; fingerprints
identify the artifacts tested and do not establish that they were rebuilt.

The previous checkpoint passed **787/787 scored cases** across seven
harnesses at both 10 s and 5 s per query on implementation commit `87ed037`.
Its eight extended open searches and thirteen Church stretch searches were
unsolved at both budgets. [The checkpoint receipts](docs/baseline/p1-2026-09-21/README.md)
include complete logs, source/executable hashes, and the precise score
boundaries. In particular, the baseline score does not validate every
ordinary command in the legacy transcripts.

The archived induction and result-binding checkpoint, implementation commit
`555236a`, passed **805/805 required checks across nine harnesses at both
budgets**. [The new checkpoint receipts](docs/baseline/induction-2026-09-21/README.md)
include complete raw outputs and hashes captured before the runs. Five extended
searches and thirteen Church stretch cases were unsolved at that checkpoint. The checks include
repeated goals tested at different boundaries; 805 is not a count of distinct
benchmark problems.

The new [extended suite](docs/baseline/extended.md) reconstructs the sixteen
probes in proposal 11, adds nine Lean-core examples and four negative
controls. All 29 sessions are now required after focused validation of the
last open tree-inorder case; the corresponding archived aggregate contains 824 checks.
Each query runs in a fresh session; a reported candidate must bind at the
requested type and pass executable replay. This is the initial local E8
benchmark work, not a port of the external synthesis benchmark collections.

The archived [local-proof and cancellation checkpoint](docs/baseline/local-proofs-2026-09-21/README.md),
implementation commit `914680d`, passed **813/813 checks across ten harnesses
at both 10 s and 5 s per query**. Fin and transitivity are now required in the
original E8 suite; six separate gates cover those goals, local contradictions,
a supplied list-length induction hypothesis, and a False-contract control.
The archive preserves complete outputs and verifies source, executable,
compiled-module, and external-input hashes against a pre-run snapshot.
Three E8 searches and thirteen Church stretch cases were unsolved at that
checkpoint.

The archived [constructive guard checkpoint](docs/baseline/guards-2026-09-21/README.md),
implementation commit `ce31d3a`, passes **820/820 required checks across eleven
harnesses at both 10 s and 5 s per query**. Maximum and drop-zero are required
E8 probes; five separate guard gates include universal post-checks for maximum,
minimum, and drop-zero. Empty-provider Lean fixtures separately verify native
guarded recursion, exact-term publication, and printed-source equivalence.
The archive preserves complete raw runs and unchanged pre/post input hashes.
Tree inorder was the only open E8 search at that checkpoint; the thirteen
Church stretch cases were also unsolved.

The latest complete [tree-composition checkpoint](docs/baseline/tree-composition-2026-09-21/README.md),
implementation commit `313a441`, passes **824/824 required checks across twelve
harnesses at both 10 s and 5 s per query**. All 29 original E8 sessions are
required and passing. Three additional tree gates verify universal constructor
equations, held-out execution on two binary datatypes, and an impossible-contract
control. Both full runs preserve the same source, executable, compiled modules,
and external fixtures; the archive contains complete raw outputs and checked
pre/post hashes. The thirteen unscored Church stretch searches remain bounded
misses. These counts include repeated goals checked at different boundaries,
and are not a count of distinct synthesis problems.

The Church harness imports the specifications from Leant's vendored Djex
directory (`C:\Leant\lib\Djex\test-church`), so every `:synth` carries the
spec's exhaustive `check_<op> f = true` contract.

Diagnostics: `set_option leant2.trace true` enables profiling and prints lane
and depth timings with ledger counters. Query-owned spans report inclusive
and exclusive elapsed time and record partial work on interrupted exits.
The `lane.search` root covers search and acceptance callbacks, not whole-query
setup or result publication; inclusive rows overlap. Ordinary searches do not
collect profiling timers. `set_option leant2.traceNodes true` prints every program
checked against the contract, plus observation statuses and cache reuse.

