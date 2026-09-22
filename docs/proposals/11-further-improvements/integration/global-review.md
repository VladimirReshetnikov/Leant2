# Global design and consistency review

This is the follow-up audit of the nine incoming packages' foundations,
executive recommendations, integrated plans, evaluation designs, conclusions,
and source-evidence qualifications. It complements the item-level topic ledgers
and `retirement.md`; it is not an independent audit of all 97 file identities
or a claim that any proposed native feature has been implemented.

Paths below are relative to `docs/proposals/`. Incoming line locations refer
to the ingested files; canonical section names and labels are the durable
destinations. The canonical comparison covered `11-further-improvements/`
main text, `02-classification.tex`, `02a-semantics.tex`, `14-roadmap.tex`, and
`17-integration.tex`, with relevant topic-section checks. The original
engineering/adaptation sections were then repaired under the coordinator's
explicit ownership assignment. No production code, incoming file, generated
PDF, or shared bibliography was changed by this worker.

## Package coverage

| Package and reviewed global source | Distinct global requirements and canonical disposition |
| --- | --- |
| N1: `new/1/sections/01-foundations.tex`, `10-plan.tex`, and source/evidence qualifications | Separate mathematical answers from implementation; first-class complete state; explicit evidence kinds; bounds and ablations; native certification versus compiled realization. Covered by `sec:semantic-boundaries`, `sec:roadmap`, and `sec:integration`. N1's nominal-model and induction-generalization precedents are retained in `sec:carrier-parametricity` and `sec:carrier-motives`; neither becomes a claim of a working Lean adapter. |
| N2: `new/2/Leant2_Expert_Answers/Leant2_Expert_Answers.tex`, executive/foundations lines 116–263, implementation 1585–1731, evaluation/conclusion 1732–1871, source audit 1920–1944 | Shared dependency service, explicit ownership of references beyond native saved state, baseline-preserving state refactoring, complete cost accounting, original-query checking, and separate supplied structure diagnostics. Covered by semantic/roadmap services and phases. The reference-oracle/examples-only and supplied-motive diagnostics at 1744–1748 prompted the roadmap correction below. |
| N3: `new/3/leant2-expert-answers/sections/01-foundations.tex`, `10-plan.tex`, and appendix source qualifications | One shared dependency/evidence substrate; budgeted asynchronous proof work; fixed-policy replay; positive, bounded-negative, and inconclusive results; trust-policy and publication distinctions. Covered by semantic/roadmap sections and the R1/R3/R6 topic sections. Aesop documentation remains a contextual rule-selection source, not an implementation result. |
| N4: `new/4/leant2_expert_answers/leant2_expert_answers.tex`, executive/foundations 122–326, implementation 1751–1901, validation 1902–2026, conclusion 2027–2054 | Explicit query/configuration identity despite a simple user surface; complete state/evidence boundaries; retrospective engineering/adaptation corrections; negative propositional abstraction bridge. Its E1–E8 critique at 1877–1894 is now reflected in 03/04; configuration identity at 1896–1899 is explicit in frozen policy Pi. Its validation retains the actual finite-model variant rather than being relabeled as a Lean benchmark. |
| N5: `new/5/leant2_expert_answers/sections/01_scope.tex`, `02_foundations.tex`, `12_roadmap.tex` | Native Expr/context authority, imported recipes allocating fresh destination metavariables, exact frozen query, acyclic checked helper declaration sequence, bounded service dispatch, and publication as its own stage. The helper-sequence requirement at `12_roadmap.tex:9` prompted the explicit declaration-DAG correction in recursion. The snapshotting precedent is preserved in `sec:search-experiments` with its external-process/in-process scope distinction. |
| N6: `new/6/leant2_expert_answers.tex`, executive/foundations 98–204, integrated plan/evaluation 1680–1879, conclusion 1880 onward, finite-check/source qualifications 1942 onward | Branch ownership, decisive checks for claimed finite exhaustion, accounting for work after rollback, relative grammar coverage, adversarial rollback/instances, and distinguishing invariant discovery from proof-template execution. Canonical semantics/roadmap cover these; the explicit supplied/invented invariant diagnostic around 1835 prompted the roadmap correction. |
| N7: `new/7/Leant2_Expert_Questions/article.tex`, executive/foundations 101–194, architecture/evaluation 850–975, conclusion 976 onward, source qualifications 1030 onward | Exhaustion needs a production/bound coverage manifest; best-first ordering alone does not prove final-ranking optimality; supplied-structure, remove-one-structure, and end-to-end tracks separate expressibility, discovery, and certification. Covered by semantics, search bounds, and roadmap. The paired diagnostic methodology at 924–932 is explicit in the roadmap after correction. Uncertainty reporting remains in the ranking/evaluation topic material. |
| N8: `new/8/leant2_expert_answers/article.tex`, executive/foundations 99–141, integrated design/evaluation 761–895, plan/conclusion 897–928 | Typed lifting experiment linking carriers, dependent motives, residual evaluation, and invariants; tiny exhaustive oracle; fixed-work and deadline studies; complete cold/warm and certification costs. Canonical phases and evidence matrix preserve these. The distinct minimum-state overfitting experiment at 825–849 was missing from the topic narrative and is now constructive text at `sec:carrier-minimum-overfit`, not only an archived script. Anytime/metareasoning references motivate policies without an allocation-optimality claim. |
| N9: `new/9/leant2-expert-answers.tex`, executive/foundations 122–239, integrated plan/evaluation/conclusion 1834–2070 | Explicit six guarantee axes, frozen acceptance query, service authority boundaries, robust baseline under proposal/ranking changes, context-sensitive recipes, proof versus executable publication, and grammar-relative experiments. Covered by semantic/roadmap sections and detailed topic proofs. Its stronger container and maximum-prefix-sum derivations are mapped separately in `search-carriers.md`; no global summary replaces them. |

## Findings resolved in the original engineering/adaptation text

These corrections preserve the original useful feature targets while removing
claims contradicted by the integrated answers. All old `sec:engineering` and
`sec:adaptation` labels remain intact.

| Finding and source basis | Canonical repair |
| --- | --- |
| Historical planning gaps were stated as current implementation facts, although the imported source inspections and profile are revision-bound. All nine packages distinguish historical inspection from new evidence. | 03/04 introductions and individual motivations now identify the original `33cec8b` planning snapshot. Old latency and coverage targets remain prospective exit criteria. No current implementation status is inferred. |
| E1 conflated kernel-valid terms, declaration binding, pattern-match printing, compiler acceptance, and executable correspondence. N4's engineering critique and N5's realization architecture make these separate obligations. | E1 now stages/rechecks declarations under the original telescope/universes, retains exact contract evidence, requires compilation plus correspondence or a direct executable contract proof, and labels logical-only export separately. `implemented_by` is not presented as a proof; noncomputable publication is not executable publication. Cross-references point to dependent/recursive realization obligations. |
| E2 called frontend integration nearly a wrapper, omitting foreign metavariable ownership, unresolved expected types, universe specialization, and the identity of tests associated with a declaration. | E2 now gives those adapters explicit obligations and requires original-context replay. Supplied-carrier sketches are a diagnostic target; their body-search success is not presumed. |
| E3 asserted that three timed two-second resumes should equal a six-second run and preferred a path recipe without full semantic-state accounting. N1–N9 R1 answers establish the deadline obstruction and full checkpoint conditions. | E3 compares identical logical checkpoints, distinguishes proof/search/publication replay, records policy epochs and pending work, and measures startup/reconstruction separately. Path reconstruction and persistent snapshots remain alternatives to compare. |
| E4 treated facts about a newly introduced local as permanently cacheable; local types can depend on later assignments, universes, transparency and instances. | E4 requires complete dependency keys, branch validity and rollback tests, and treats the original 10%/1 ms targets as measurements still needed. Inclusive/exclusive work and retained memory are explicit. |
| E5 treated isolated IO references and final sorting after first-found cancellation as sufficient for independence and determinism. N4 lines 1879–1883 and all R1 deadline analyses contradict that claim. | E5 audits ownership beyond references, uses stable task identities/logical quanta/canonical commits for replay, labels opportunistic cancellation separately, and requires factorization for AND-parallel subgoals. |
| E6 inferred a negative Lean result from a propositional countermodel without an interpretation bridge. N4 lines 1885–1894 gives the concrete atom-abstraction objection. | E6 separates calculus nonvalidity from a contextual Lean negation, requires positive reconstruction and checked negative transfer, and retains unsupported queries and latency hypotheses explicitly. |
| E7 blurred provider availability with integration and finite testing with universal validation. | E7 treats version-pinned tactic adapters as proposed work; a checked individual counterexample can refute universally quantified contracts, while passing examples cannot prove them. Unknowns, negative axiom policy and fair proof service are preserved. |
| E8 generalized saturation of a scored historical corpus to broader coverage and specified benchmark import counts without validating each source's actual task boundaries. | E8 preserves unscored stretch tasks, semantic-family deduplication, original helper/grammar/example scope, carrier/motive-given diagnostics, and full certification/publication costs. |
| A1 decision-tree branch mixing can destroy a relational contract even when each individual candidate satisfies selected whole conjuncts. | A1 retains typed call environments and correlated observations, requires justified decomposition or full assembled-contract validation, and calls a tree smallest only after exhaustive bounded optimization. |
| A2 described every nearby arithmetic hole as forcing unary computation and treated an outermost recursion tier as broad primitive-recursion coverage. | A2 preserves priority for outermost recursion, explicit literal encoding cost and future enumeration bounds, truncated subtraction, and measured closed/partial arithmetic semantics. Its restricted scope is explicit. |
| A3 finite signatures were treated as a congruence from groundness alone; normal-form restrictions and commutative reordering lacked coverage/cost hypotheses. | A3 requires interchangeability in all admitted surrounding contexts or recoverable reference alternatives, documents typed normal-form scope, checks symmetry laws, and preserves a candidate-objective-aware representative policy. |
| A4 inferred parametricity from a surface polymorphic type and a universal syntax-size testing bound from finite canonical inputs. N1–N9 R2 answers give exact naturality/length boundaries and counterexamples. | A4 cites the conditional container/position theorem, handles dictionaries and fibers, limits length-N observations to length-N behavior, and keeps the missing small-model theorem explicit. Canonical probes and displayed behavior groups remain useful without claiming equality. |
| A5 claimed retrieval time independent of index/output size and assumed persistence alone solved rollback. | A5 accounts for wildcard branches and candidate output, pins transparency/environment identity, preserves broad variable-head matches, requires recall evidence for stronger filters, and tests cache/context validity. |

## Additional missing details found and verified repaired

1. **Frozen configuration identity.** N4's foundations and its final
   architecture paragraph (`new/4/...tex:1896`) distinguish no user settings
   from no configuration identity. `02a-semantics.tex:15–25` now includes Pi:
   ranking objective, logical resources, transparency/equality, search and
   proposal admission policy, and their versions. This makes the already
   scattered search/replay conditions one explicit query identity; the search
   section additionally spells out model/seed/tie-breaks and checkpoint state.
   Verified on disk after the coordinator's repair.
2. **Helper declaration ordering.** N5 `12_roadmap.tex:9` requires an acyclic
   checked declaration sequence. `09-recursion.tex:179–188` now names the DAG,
   topological checking, prior dependency closure, and separately supported
   mutual bundle realization. A provisional self-reference or a future mutual
   recursion feature does not bypass that audit. Verified on disk.
3. **Diagnostic benchmark axes.** N2 `...tex:1744–1748`, N6's Evaluation and
   proof paragraph, and N7's Separate expressibility, discovery, and
   certification subsection distinguish reference access, motive/invariant
   discovery, and body/proof search. `14-roadmap.tex:93–101` now has
   oracle/examples-only and supplied/invented motives/invariants, alongside
   carrier/helper and trace axes. Existing scheme/carrier diagnostics in
   recursion were preserved. Verified on disk.
4. **A minimum machine can overfit.** N8's length-exactly-two experiment has a
   four-state cyclic minimum fitting lengths 0–5 but failing at 6; the refined
   four-state machine has an absorbing final state. `sec:carrier-minimum-overfit`
   retains both machines, the separating clique and `min(n,3)` induction. The
   source's oracle and finite Python checks remain separate from the written
   invariant proof, sparse-example identification and native Lean evidence.

## Evidence, alternatives, and remaining uncertainty

Checked canonical main/02/02a/14/17 preserve the distinction between historical
profile `33cec8b`, incoming source inspection `784664f`, the integration
checkout/revision, and rerun Python evidence. The finite receipts are not
native API smoke tests, Lean proofs, compilation results, performance studies,
or implementations of proposed services. A different unary alphabet/output
model or initial-state convention is not silently aggregated into one count.

The following apparent disagreements are intentional alternatives, not lost
recommendations: reconstruction recipes versus persistent snapshots;
first-found interactive publication versus canonical committed logical
prefixes; a fast incomplete proposal lane versus a fairly serviced reference
lane; supplied structure versus full invention; finite machine minimization
versus typed carrier synthesis; and logical certification versus executable
publication. Their stronger claims retain their hypotheses in topic sections.

The global pass found no remaining unique global algorithm or obligation
missing from the reviewed passages after the repairs above. This is scoped
to those passages and does not replace the individual topic ledgers or the
retirement auditor's file/bibliography disposition checks. Active unknowns
remain the native rollback/ownership audit, sound and useful dependencies,
bounded grammar coverage and proof-check termination, low-cost conservative
evaluation, effective carrier/motive/helper discovery, publication adapters,
and end-to-end empirical gains. The revised question lists ask for these
remaining artifacts rather than repeating the answered historical questions.

Supplied literature pointers `snapshot`, `nominal`, `inductiongeneralization`,
`anytime`, and `aesopreadme` were added where relevant in 03/04/05/06; the
coordinator's contracts section cites `anytime,metareasoning` for its qualified
scheduling motivation. No new external source verification is claimed here.

## Validation and handoff

The owned TeX files are 03, 04, 05 and 06; the two owned integration ledgers are
this file and `search-carriers.md`. Static verification checks braces,
environment nesting, unique labels, resolved cross-references/citations, and
the four R1.N plus five R2.N active question counts. Whitespace is checked with
`git diff --check`. The coordinator owns aggregate document validation,
compilation, PDF visual inspection, retirement of incoming files, and commits.
No native build or PDF build was run by this worker.
