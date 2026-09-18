# Implementation gates

This checklist describes proposed production work. A completed experiment is not a completed production gate.

## 1. Query ownership and acceptance

- Freeze elaborated target, predicate, universes, local telescope, local instances, imports, and policy.
- Resolve input ambiguity before search; distinguish requested synthesis holes from accidental statement metavariables.
- Keep the candidate even when the contract ignores it.
- Check both program and proof in a controlled environment, then audit their dependencies.
- Keep logical acceptance, behavioral evidence, executability, and effects as separate fields.
- Add tests for hidden axioms, sorry in dependencies, changed overloaded instances, escaping locals, unresolved universes, and stale workers.

## 2. Native search

- Preserve exact Expr/LocalContext/MetavarContext ownership and full dependent application spines.
- Maintain alternatives until dependent continuations succeed.
- Restrict root assignments to synthesis-owned holes.
- Resolve fully qualified and namespace-relative names through Lean elaboration at the real frontend boundary.
- Use demand-driven type and universe instantiation; retain unresolved choices as explicit work.
- Make index retrieval conservative with wildcard/reducible-head fallback.
- Record exact dictionary terms, not just class types.

## 3. Dependent elimination and recursion

- Compute transitive dependent-telescope generalization before cases/induction.
- Build actual motives and checked index transports, not textual substitutions.
- Discharge impossible branches through evidence, not heuristic unification failure.
- Register restricted recursive-call capabilities and checked structural templates.
- Generalize changing accumulator parameters and synthesize function/product/dependent carriers under bounds.
- Check final executable source form; the recursor/codegen regression in this package must remain a test.
- Treat well-founded recursion and synthesized invariants as later explicit capabilities.

## 4. Contracts and solver boundaries

- Expose proof, refutation, and unknown outcomes separately.
- Port the affine coefficient experiment into Lean with its generic certificate theorem.
- Retain candidates whose proof strategy timed out for fair later verification.
- Replay externally suggested models in the exact Lean interpretation before authoritative rejection.
- Specify overapproximation/underapproximation directions for each domain and pruning theorem.
- Never merge programs permanently from finite observations alone.

## 5. Resources and provenance

- Replace prototype depth-first recursion with bounded resumable cursors.
- Charge unification, normalization, elaboration, and failed branch work.
- Record beam evictions and omitted grammar alternatives.
- Use immutable cross-worker state and checked replay; never share mutable metavariable contexts.
- Cache failures with their real scope; timeout is not uninhabitability.
- Distinguish first verified, best encountered, and proved cost-minimal outputs.

## Prototype limitations to fix before adoption

`NativeCore.search` is an experimental mechanism test. Its fuel is derivation depth, not total work; it uses broad exception handling; it does not implement negative proofs; constructor/application search is not a complete Lean grammar; `leant2_with` requires exact global names; rule-level dependency extraction and concurrent state ownership are absent; and final validation is performed by ordinary surrounding Lean compilation rather than a standalone production finalizer. Only the tests described in the article were run.
