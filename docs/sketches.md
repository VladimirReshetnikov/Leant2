# Completing a supplied program sketch

`#leant2_sketch` completes explicitly named holes in a supplied whole function.
Its target is a closed type, and an optional contract applies to the completed
whole function. Each accepted program and contract proof is checked by Lean's
kernel at the original target and contract before result publication.

```lean
import Leant2

set_option leant2.budgetMs 5000

#leant2_sketch f : List Nat → Nat :=
  (fun (step : Nat → Nat → Nat) (seed : Nat) (xs : List Nat) =>
    List.foldr step seed xs) ?step ?seed
where
  f [] = 1 ∧ f [2] = 3 ∧ f [2, 3] = 6 ∧ f [0, 4, 0] = 5

def offsetSum : List Nat → Nat := it1

example : offsetSum [5, 8] = 14 := by decide
```

The supplied traversal is fixed. Search fills `step` and `seed` together; neither
hole has `xs` in its local context. A wrong seed can force search to reconsider
the step. The four stated observations constrain the original query. The last
example is a separate held-out check and is not a theorem about every possible
list or every program satisfying those finite observations.

The identifier `f` names the function inside the contract. Completed results
use the ordinary `it1`, `it2`, ... aliases, and bare `it` refers to the first
result. The identifier is not itself a new definition. Existing definitions
that use an earlier alias keep their original immutable value.

Holes may occur under binders:

```lean
#leant2_sketch identity : ∀ A : Type, A → A :=
  fun (A : Type) (value : A) => (?body : A)
where
  ∀ (A : Type) (value : A), identity A value = value
```

The pending body sees its original local type and value. Native closure
construction closes the result after completion; caller metavariables are
neither captured nor used as search holes. The identity contract here is
universal, unlike the finite fold observations above.

## Supported boundary

- Supply a closed, fully elaborated target and contract. Explicit named
  universe parameters are retained. Unresolved expression or universe
  placeholders are refused rather than silently specialized.
- Use zero to four explicitly named program holes with unique source labels.
  Their types and local declaration types/values must already be determined.
  Zero holes checks a supplied complete body; it does not invent a replacement.
- Fixed applications, lambdas, constructors, and closed local values can form
  the body. Explicit native carriers such as `Option A` or `Int → A` can appear
  in those fixed expressions.
- Anonymous holes, repeated source labels, type/motive/dictionary holes, and
  unfinished dependencies between hole contexts are refused. Native expression
  error obligations and pending synthetic tasks outside the owned holes must
  be finished, including registered holes in erased subterms. Preparation
  that creates new declarations or leaves recursive definitions to lift is
  outside this initial boundary.
- A compatible macro expansion can repeat one already registered source hole;
  those occurrences share one pending goal. Distinct explicit occurrences with
  the same label remain a preparation error. Native context compatibility is
  checked rather than inferred from matching printed names.

Sketch search uses only the original universes. It does not fall
back to an unconstrained query. Completion depth measures the expressions
invented for the holes; the supplied body is guidance. The search grammar and
preparation bounds remain finite, and partial residual pruning is disabled for
these source-created closure graphs.

Holes with fewer function arguments are tried first, with source order breaking
ties. The whole-contract proof follows all program holes. This helps a small
initializer constrain a larger step while retaining every provider and the
same joint backtracking continuation. It is a search-order heuristic, not a
completeness guarantee.

## Results, failure, and trust

The command uses the same curated and session providers and project-relative
axiom policy as `#leant2`. A supplied fixed fragment is subject to the same
axiom audit as a synthesized fragment. Internal metaprogram tests use explicit
provider lists and profiles separately; an empty ordinary provider list still
permits native constructors, instances, and proof automation.

An accepted result contains the complete program and a proof of its original
whole-function contract. Axiom auditing retains the unreduced original contract
syntax, even when reduction could discard a dependency. A gate rejection of a
completed proof leaves other proofs of that program available. Auxiliary
theorems can be expanded for transport; fresh axioms,
definitions, and opaque values cannot silently escape into accepted results.

A false decision may discard a completion only when its predicate/decider
dependencies obey the selected policy. Forbidden false evidence is
inconclusive, leaving ordinary proof search available. Unsafe declarations
cannot authorize pruning, even when their axiom inventory is empty. This check
governs pruning; accepted programs and proofs still pass the kernel gate.

The source diagnostic for the first completion is supplementary. The certified
kernel expression remains authoritative. Independent replay uses the actual
emitted text in a fresh process; display alone does not establish replayability
or executable behavior for arbitrary generated terms.

Malformed input raises a preparation error and preserves prior aliases. A
well-formed unsuccessful query clears numbered aliases while retaining bare
`it`. Rejection of a supplied wrong body is a bounded completion result, not a
proof that every program fails the contract. A certified contract-impossibility
result proves the original statement about every program, independently of the
chosen sketch. Other bounded misses do not establish logical impossibility.

Caller Core, Meta, and Term state is restored around preparation and completion.
Only portable outcomes escape that scope. The command separately restores its
entire publication state on exceptions, including cancellation after an alias
was installed. External IO effects are not undone. Native cancellation and
unrelated internal/runtime failures retain their exception identities.

`leant2.budgetMs` is cooperative search control. Preparation, upfront contract
refutation, export, ranking, and publication are not covered by a hard
whole-call time limit.

Metaprograms can import `Leant2.Frontend.Sketch.Run` and call
``Leant2.Frontend.Sketch.synthesizeSketch : Query → TSyntax `term → TermElabM Result``
with elaborated closed query inputs and quoted body syntax. `Result` contains
the ordinary `Outcome` and a preparation report with hole names and counts.
This call restores its elaborator state and does not publish aliases or compile
results. Its query supplies the provider inventory and axiom profile explicitly.

## Evidence and remaining work

The [public sketch runner](../tools/run_sketches.py) has seven logical cases,
three emitted-source replays, and a separate Lean-only witness/control process.
The complete [sketch checkpoint](baseline/sketches-2026-09-21/README.md) passes
839/839 checks across fourteen families at both 5000 and 10000 ms on `c69f484`,
including all seven public sketch cases. Source, modules, both native
executables, and fixture fingerprints match before and after. Each sketch
run contains ten public process stages and one separate reference process;
the reference process is a prerequisite rather than an eighth scored case.

Native regressions separately cover preparation and closure ownership,
initialized continuation, exact original-query replay, axiom profiles,
caller-state restoration, and alias rollback, including real cancellation
after publication. They belong to the native build gate rather than the
external case denominator. The final aggregate build passes 83 jobs, and the
exact examples in this guide and the root README compile with accepted sketch
outcomes. The archive independently reconstructs each actual emitted term and
replay source, rechecks diagnostics and process exits, and preserves exact raw
outputs. Earlier focused checks remain separate evidence. See the
[implementation notes](implementation-notes.md) for the maintained validation
boundary and the remaining work.

This first closed command does not close proposal E2. All thirteen original
Church stretch searches remain a separate open-search track; the proposed
thirteen carrier-given completions also remain to be established independently.
Contextual contract lifting, term/definition sketch syntax, arbitrary dependent
sketches, carrier invention, and editor code actions remain later work.
