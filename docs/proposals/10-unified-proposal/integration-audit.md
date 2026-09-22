# Consistency audit against the maintained further-improvements proposal

This audit preserves proposal 10 as the historical synthesis of P1–P9. It corrects material conflicts with the later N1–N9 integration in proposal 11 without updating old prototype measurements into current implementation claims. The maintained proposal owns the detailed algorithms, proofs, and active research questions; this document records only the correction map.

## Corrections

| Topic and location in proposal 10 | Material issue | Correction and maintained authority |
| --- | --- | --- |
| README.md; Leant2.tex front matter | Historical prototype limitations could be read as current implementation status; approximate page count could drift | Explicit historical scope and link to proposal 11; removed approximate count. No new experiments claimed |
| 03-state-search.tex, scheduling allocation | Heuristic already disclaimed A* admissibility, but did not address shared-goal count | Added two-goals/one-assignment counterexample, same-objective proof requirement, and zero baseline; proposal 11 R1 |
| 03-state-search.tex, determinism | Ordering/seeds alone appeared to imply exact replay | Fixed environment, grammar, logical budgets, inputs, epochs and admission trace; wall-clock result sets can differ; proposal 11 R1/R9 |
| alg-scheduling.tex, checkedPrune result | Claimed raw completion set empty | Corrected to no contract-satisfying completion in the certified scope; proposal 11 common semantics/R3 |
| alg-scheduling.tex, aging | Aging alone claimed to prevent starvation | Aging is heuristic when competing scores grow; reserved FIFO service supplies fairness |
| alg-scheduling.tex, derived stopping rule | Comparing current queue costs implied best/optimal result | Requires validated lower bounds on the same frozen final objective, covering all deferred lanes and candidates; otherwise best found; proposal 11 R8 |
| alg-scheduling.tex, cost/frontier | Charged work, final ranking, and queue cost conflated; display cap could permanently delete observational alternatives | Separate objectives; archive candidates first and park only for display; cost-preserving checked replacement required for minimality; proposal 11 R8 |
| alg-scheduling.tex, performance mode | Suggested post-sorting makes racing results deterministic | Sorting stabilizes order only for an already selected set; cancellation changes membership; completed logical epochs or event replay needed |
| 06-behavior.tex; alg-scheduling.tex equivalence | Existing exact/observational distinction mostly sound, but finite-domain exception lacked all conditions | Explicit typed complete observations, future-context congruence, cost/feasibility preservation, unknown-not-equal and aligned fibers; proposal 11 R8 |
| 04-construction.tex, provider index | Discrimination-tree choice appeared to guarantee no omissions | No-under-return is a coverage obligation; unresolved dependent heads/universes require conservative fallback; proposal 11 R7 |
| alg-elim-retrieval.tex, abstractCompose | Ordinary paths forgot argument conjunction; every failed elaboration refined abstraction | AND-hypergraph, joint substitutions, reusable locals, explicit top, justified mismatch only, unknown/resource fallback, construction/bound simulation before hard exclusion; proposal 11 R7 |
| alg-behavior.tex, residual forms | Merely naming an untyped grammar “typed” omitted closure and semantic obligations | Explicit native type/scope, dependency-closed environment, telescope substitution, universe/index/instance identity, completion correspondence and erased-dependency retention; proposal 11 R3 |
| alg-behavior.tex, functional consistency | Equal hole/argument pair with incompatible outputs refuted without checking path guards | Same typed closure instance, certified argument equality, and both guards holding are required; otherwise retain guarded incompatibility |
| 06-behavior.tex; alg-behavior.tex, symbolic recursion | Blanket ban on symbolic hard pruning contradicted certified conservative angelic exclusion | Symbolic satisfiability is not realizability; certified unsatisfiability may exclude conservatively represented completions with contract-derived assumptions scoped correctly; proposal 11 R3/R5 |
| 05-recursion.tex, compiler boundary | Several historical recursor failures could be read as a universal compiler restriction | Explicitly confined to those artifacts/toolchains; kernel typing, correspondence, compilation and example execution remain separate; proposal 11 R5 |
| alg-acceptance.tex, worker loop | Catch-all conversion swallowed interrupts despite global rules | Classified local miss/local budget/interruption, restore before propagation, native check rethrows interruption, reject unresolved level metavariables; proposal 11 R6 |
| alg-acceptance.tex, frozen interface | One textual local per contextual hole could be ill-scoped or ill-typed; live returned goal outlived its locals | Closed dependency-aware interface schema with exact occurrence substitutions, native replay and completion correspondence. Refuting universal schema does not refute every filling; proposal 11 R3/R6 |
| alg-acceptance.tex, proof readiness | Every remaining program hole forced deferral, contradicting joint proof effects | Tier-sensitive readiness, cheap uniform/data-constraining proofs with holes, support/tier retry key and reserved service; proposal 11 R6 |
| alg-acceptance.tex, arithmetic | Tactic name suggested full decision-theory coverage | Pinned certified fragment and allowance conditions required; proposal 11 R6 |
| alg-recursion.tex, certifiedBranch | A failed proof semantically rejected the value and exhausted the branch | Unknown/unsupported attempts retain resumable proof debt; checked refutation scoped to value/invariant pair; fragment exhaustion and original-contract refutation separated; proposal 11 R6 |

## Existing statements retained

- The architecture already distinguished exact equality from finite observation buckets, required recoverable bucket members, audited dictionary identity, and used transactional native contexts. Those policies were retained.
- The high-level priority formula already explicitly disclaimed admissible A* status.
- The finite-certified-layer and dovetailing theorems already state essential finiteness, verification, grammar, and conservative-pruning assumptions; their historical status was preserved.
- Recursion already required logical and executable products plus correspondence or a direct executable contract proof. Only the scope of historical compiler failures needed clarification.
- No original P1–P9 experiment counts, transcripts, theorem inventories, or provenance labels were replaced by N1–N9 model results.

## Verification and remaining limits

Static validation checks all proposal-10 TeX references and citations, environment balance, source links, and whitespace. This audit adds no native Lean implementation, proof-service test, evaluator correspondence proof, retrieval simulation proof, performance measurement, or model experiment. Pseudocode remains a specification, including helper interfaces such as classified worker failure and closed interface abstraction. Proposal 11 gives the current proof obligations and open questions.

The corrected article was rebuilt in three serial final passes and every page was rendered and visually reviewed. The [architecture publication receipt](integration/architecture-review.md) records the source and PDF hashes, the precise visual coverage, and retained non-fatal warnings. These checks validate the document artifact, not its proposed Lean algorithms. Historical external API/toolchain assertions were not re-surveyed here; the maintained proposal's evidence ledger records the relevant source and version boundaries.
