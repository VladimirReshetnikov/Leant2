# Evaluation, dependent-type, and recursion integration coverage

This ledger covers **R3, R4, and R5 in all nine incoming packages**, integrated into sections/07-evaluation.tex, 08-dependent.tex, and 09-recursion.tex. N1–N9 are incoming-package identifiers, distinct from the earlier P1–P9 architecture corpus. The existing labels sec:evaluation, sec:dependent, and sec:recursion remain stable.

There are **99 incoming question instances**: eleven historical questions in each of nine packages. Repeated material appears once at the canonical labels below. Source-specific qualifications, examples, algorithms, proofs, alternatives, and limitations remain attributable here. Original answered questions were removed from the active lists and replaced by R3.N1–4, R4.N1–4, and R5.N1–4. The new question wording lives only in the respective canonical topic section.

No incoming directory, shared bibliography, PDF, production source, or other agent's section was changed by this worker. No native Lean process or document build was run. Source inspections and Python countermodels are historical design evidence, not current engine behavior or performance.

## Historical question-to-answer map

N1/N5/N9 use Q spellings (R3.Q1 etc.); N2/N3/N4/N6/N7/N8 use R3.1 etc.

| Historical question | Answered boundary and unresolved scope | Canonical labels | Replacement agenda |
|---|---|---|---|
| R3.1: higher-order/dependent examples | Higher-order Smyth and sparse traces exist; typed substitutions, fibers, relational alternatives specify a Lean adaptation whose implementation/proof remains open. | sec:evaluation-closures, sec:evaluation-observations | R3.N1 |
| R3.2: incremental normalization | Read-set consistency and persistent identities answer safe reuse; efficient complete Lean dependency tracking remains open. | sec:evaluation-cache, prop:evaluation-cache | R3.N2 |
| R3.3: conservative evaluator | Checked evidence, completion coverage, substitution stability, and native/certified backend choices answer the trust boundary; fragment proofs and total costs remain open. | sec:evaluation-certification, prop:evaluation-refutation, sec:evaluation-deployment | R3.N1, R3.N3 |
| R3.4: top-down angelic guarantees | Explicit finite fair refinement theorem; no unrestricted termination claim. | sec:evaluation-angelic, thm:evaluation-bounded | R3.N4 |
| R4.1: motive enumeration | Scoped finite templates are exhaustible with total checking; maximal occurrences do not cover every useful motive or fresh accumulator. | sec:dependent-motives, sec:dependent-recipe, prop:dependent-motives | R4.N1 |
| R4.2: transports | Typed restricted normalization and reconstruction answer practical handling; no general cheap equality quotient. | sec:dependent-transports | R4.N2 |
| R4.3: unfolding | External policy evidence and a phase-sensitive ladder are explicit; optimal thresholds/benefit remain unmeasured. | sec:dependent-unfolding | R4.N3 |
| R4.4: native motive API | Pinned APIs exist with preconditions; transactional integration and cost require validation. | sec:dependent-adapter | R4.N4 |
| R5.1: interpreter agreement | Propositional simulation is general; some encodings compute definitionally. Closed simulation is weaker than open pruning; publication is separate. | sec:recursion-capabilities, sec:recursion-simulation, prop:recursion-simulation, eq:recursion-fuel, sec:recursion-publication | R5.N1, R5.N4 |
| R5.2: top-down angels | Typed correlated constraints, helper-seed distinctions, scoped nogoods, and final realization specify a coherent approach; implementation/sharing remain open. | sec:recursion-angels, sec:evaluation-angelic | R5.N2 |
| R5.3: recursion basis | Overlapping staged portfolio, with explicit coverage measurements; no canonical optimum or transferable percentage. | sec:recursion-basis, sec:recursion-evaluation | R5.N3 |

## Input-by-input integration

Every entry denotes integration of substantive content; repeated arguments are deduplicated at the stated destination. No R3/R4/R5 answer is rejected wholesale.

### N1

Sources: new/1/sections/04-evaluation.tex, 05-dependent.tex, 06-recursion.tex; supplemental index/source notes in 11-appendices.tex.

- R3.Q1: Smyth implementation/core distinction; typed telescopes and vector fibers; unknown inversions, lawful BEq, relational calls → sec:evaluation-closures, sec:evaluation-observations.
- R3.Q2: complete-read-set theorem; assigned dependencies/universes/delayed links/instances; ABA, safe global invalidation, blockers outside snapshots, qualified global false cache → sec:evaluation-cache, prop:evaluation-cache.
- R3.Q3: step-proof versus reflection alternatives; telescope-quantified residual certificate and conditional assumptions; preprocessing scope; Lean4Lean limits; tests not proof → sec:evaluation-certification, sec:evaluation-deployment.
- R3.Q4: correlated calls, guesses versus necessary equations; finite oracle/grammar/solver/fairness/progress conditions; unbounded semidecision only → sec:evaluation-angelic, thm:evaluation-bounded.
- R4.Q1: 2^k templates, bounded fresh state/products, fixed vector-map parameters, type-independent changing accumulators → sec:dependent-motives, sec:dependent-recipe.
- R4.Q2: proof-producing index normalization, n+0 correction, heterogeneous/setoid reconstruction, proof display cost versus cast work and replay → sec:dependent-transports.
- R4.Q3: Canonical aliases/reducible/instances/indexed support; sauto selective/forced unfolding and red/ered defaults; measured ladder → sec:dependent-scope, sec:dependent-unfolding.
- R4.Q4: three pinned APIs, variable-index preconditions, structured transactional outcomes/diagnostics/resources → sec:dependent-adapter.
- R5.Q1: dependent capability, successful-fuel simulation, depth versus total fuel, three trust profiles, logical/compiler boundary and end-to-end accounting → sec:recursion-capabilities, sec:recursion-simulation, sec:recursion-publication.
- R5.Q2: assumption store/call keys/shared-hole invalidation, priority-first angels, checked relations, Cataclyst comparison → sec:recursion-angels, sec:recursion-scope.
- R5.Q3: polynomial paramorphism algebra, Para, function/product state, zip/merge/gcd, metadata for mutual/nested, parameterized helpers, supplied/invented tracks → sec:recursion-basis, sec:recursion-evaluation.

### N2

Source: new/2/Leant2_Expert_Answers/Leant2_Expert_Answers.tex, R3.1–R5.3.

- R3.1: one unknown shared by contextual occurrences; finite function applications and compatible dependent fibers/native expression authority → sec:evaluation-closures.
- R3.2: Canonical-min suspension; observation statuses/watchers; immutable branch identities including delayed/universe assignments → sec:evaluation-cache.
- R3.3: conjunction/list/decide reflection, disjunction alternatives, lawful Boolean equality, stable-certificate proof, correct approximation direction, preprocessing/Lean4Lean caveats → sec:evaluation-observations, sec:evaluation-certification.
- R3.4: finite symbolic/oracle alternatives, exact total checks, failed guess is not failed body, contract-derived values separately tagged → sec:evaluation-angelic.
- R4.1: direct motive first, failed-IH generalization, finite products/functions/dependent pairs, indexed accumulator telescope → sec:dependent-motives, sec:dependent-recipe.
- R4.2: commuted vector indices, cast composition, proof irrelevance limits, positive secondary bounds, replayed display → sec:dependent-transports.
- R4.3: head exposure/selective escalation, index normalization without full open-recursion expansion, local failure not incompatibility → sec:dependent-unfolding.
- R4.4: signatures/free-variable restrictions, full transaction/memo key, high-level native operation first → sec:dependent-adapter.
- R5.1: full state including mutual tags; uniqueness by well-founded induction and body pointwise congruence; extensionality audit; speculative decrease obligations → sec:recursion-capabilities, sec:recursion-simulation.
- R5.2: symbolic outputs/disjunctions; r1+r2=5 counterexample and same-call equality; typed hybrid components → sec:recursion-angels.
- R5.3: structural/parameter/tuple/continuation/course-of-values/measure order; overlapping Fibonacci/zip encodings; held-out tracks and failure causes → sec:recursion-basis, sec:recursion-evaluation.

### N3

Sources: new/3/leant2-expert-answers/sections/04-evaluation.tex, 05-dependent.tex, 06-recursion.tex; index/models in 11-appendices.tex.

- R3.1: finite application trees; contextual fibers; unknown function+argument remains relational; sufficient inversion is not necessarily exhaustive → sec:evaluation-closures.
- R3.2: A/B/A-with-irrelevant-change model; immutable reads/theorem; hidden globals/class reads; semantic caches versus monotone ledger → sec:evaluation-cache, prop:evaluation-cache.
- R3.3: stable reduction versus abstract outcome inclusion; substitution argument; beta/constructor/projection/recursor fragment; checked hints; exact relational contract → sec:evaluation-observations, sec:evaluation-certification.
- R3.4: forced/abstract/guessed results; conditional refutation distinction; finite fair refinement, infinite-domain limit → sec:evaluation-angelic.
- R4.1: nonmaximal n inside n+k counterexample, three recipe dimensions, actual indexed exclusion, behavioral generalization/fallback → sec:dependent-scope, sec:dependent-motives.
- R4.2: affine index normalizer, family/source/target obligations, 0+n correction, positive grade, setoid compatibility → sec:dependent-transports.
- R4.3: Canonical generalized principles/predicates; sauto no-induction clarification; demand ladder and alias failure cache → sec:dependent-scope, sec:dependent-unfolding.
- R4.4: APIs plus ElimApp.mkElimApp/setMotiveArg context caveat; native reversion already present; structured failure/interrupts and pinned compilation → sec:dependent-adapter.
- R5.1: WellFounded.fix_eq/non-rfl equations, one-way simulation proof versus adequacy, Nat.recCompiled/csimp and axiom inventory → sec:recursion-simulation, sec:recursion-publication.
- R5.2: Smyth top-down sparse traces versus Burst; contextual relations, typed component reuse, guidance-first → sec:recursion-angels.
- R5.3: structural/generalized/product/deeper/measure/tagged basis; explicit capability bounds and overlapping encodings, cheapest verified scheme → sec:recursion-basis, sec:recursion-evaluation.

### N4

Source: new/4/leant2_expert_answers/leant2_expert_answers.tex, R3.1–R5.3.

- R3.1: Scrybe, complete closure version/fiber, delayed context proof boundary, staged first-order/higher-order/dependent adaptation → sec:evaluation-closures, sec:evaluation-certification.
- R3.2: residual DAG/guard theorem, local values/equations/options and hash collision checking, blockers/ledger lifetimes, illustrative rollback model → sec:evaluation-cache.
- R3.3: actual CBV entry points/of_decide_eq_true, equation proofs versus conversion, axioms/dependent-position limitation, four backend comparison → sec:evaluation-certification, sec:evaluation-deployment.
- R3.4: concrete execution included in angelic store; loose correlations versus unsafe restrictions; finite derivations/failing-candidate progress → sec:evaluation-angelic, thm:evaluation-bounded.
- R4.1: three operations, finite terminals/local types/constructors with universe/binder bounds, scoped rather than textual occurrences, exact checks → sec:dependent-motives, prop:dependent-motives.
- R4.2: congrArg family cast, policy certificates/receipts, CBV dependent congruence limits, registered family/index first → sec:dependent-transports.
- R4.3: head/demand/broad policy, compact provider names, matched-work/growth/resource-loss measurements → sec:dependent-unfolding.
- R4.4: helper responsibilities, exclusions belong to search, prepared indices, complete structured failures → sec:dependent-adapter.
- R5.1: dependent full-state capability, finite simulation premises, none is unknown, checked/native trust distinction and compiler bridge → sec:recursion-capabilities, sec:recursion-simulation, sec:recursion-publication.
- R5.2: both directions' strengths, typed pool and checked context renaming, assumption tags, splitting behavior buckets → sec:recursion-angels.
- R5.3: Trio comparison, tier obligations, overlap/append diagnosis, supplied-carrier/scheme/full tracks and larger-grammar fallback → sec:recursion-scope, sec:recursion-basis, sec:recursion-evaluation.

### N5

Sources: new/5/leant2_expert_answers/sections/05_evaluation.tex, 06_dependent.tex, 07_recursion.tex; index/evidence in 13_appendices.tex.

- R3.Q1: shared map-hole closures/suspended eliminations, necessary constructor inversion versus noninjective relations, proof-dependent reduction/cast endpoints → sec:evaluation-closures.
- R3.Q2: Canonical-min mechanization caveat, ABA/watcher/new-observation identities, closed→branch→cross-branch rollout and memory metrics → sec:evaluation-cache.
- R3.Q3: three deployment levels, quantified D→not C proof, value/suspended/rejectHint/refuted/resource outcomes, necessity versus assembly, exact unconventional BEq → sec:evaluation-certification, sec:evaluation-deployment, sec:evaluation-observations.
- R3.Q4: no invented symbolic inequality; finite strict-decrease refinement theorem, failed guess/timeout limitations, typed summaries split as observations grow → sec:evaluation-angelic, thm:evaluation-bounded, sec:evaluation-checks.
- R4.Q1: Fin-dependent telescope, repeated/compound equations, finite syntax versus timeout, new invariant/state dimension → sec:dependent-motives, sec:dependent-recipe.
- R4.Q2: typed composition proof, runtime erasure versus conversion/meaning, zero-cost loops, Nat.zero_add orientation → sec:dependent-transports.
- R4.Q3: names retained while reasoning unfolds; state policy, transitive provider expansion caution/metrics → sec:dependent-unfolding.
- R4.Q4: subgoal substitutions/universes, replay recipe not dead MVarIds, all failure categories and dependent test families → sec:dependent-adapter.
- R5.Q1: dependent body functional, Lean4.27 natural-measure exception, simulation/adequacy, csimp publication, pointwise/direct-contract alternatives and execution → sec:recursion-capabilities, sec:recursion-simulation, sec:recursion-publication.
- R5.Q2: shared equation IR/guards/termination holes, typed version spaces, Smyth/Burst/Cataclyst scope → sec:recursion-angels, sec:recursion-scope.
- R5.Q3: structural/state/measure tiers, one helper, merge/gcd/quicksort proofs, elementary/unresolved/adversarial groups and withheld witness diagnosis → sec:recursion-basis, sec:recursion-evaluation.

### N6

Source: new/6/leant2_expert_answers.tex, R3.1–R5.3.

- R3.1: explicit telescope/environment/type, Church application observations, guard/preimage alternatives and dependent staging → sec:evaluation-closures.
- R3.2: Canonical-min/Adapton, DAG/non-reused assignment identity, first-divergence proof equivalent to retained trace proof, option/equation reads and charges → sec:evaluation-cache, prop:evaluation-cache.
- R3.3: native CBV/decide_cbv, proved equations not conversion, axiom/dependent-position limits, closed abstraction instead of open proof MVars → sec:evaluation-certification, sec:evaluation-deployment.
- R3.4: full tuple and contract-relative refutation; finite oracle/body/well-founded/exact-solver/fair-state theorem, infinite values → sec:evaluation-angelic.
- R4.1: local values as dependencies, compound equality retained, native/minimal/strengthened/wider ladder and honest heuristic status → sec:dependent-motives, sec:dependent-recipe.
- R4.2: provenance, proof caching instead of arbitrary equality-proof enumeration, typed paths, positive penalty/exact display → sec:dependent-transports.
- R4.3: N6 did not verify sauto defaults, retained explicitly; exact policy evidence attributed to other responses. Opaque constants and purpose-specific escalation → sec:dependent-unfolding.
- R4.4: induction signature/fields/substitution, no global temporary declarations, changed locals in residuals, cheap failure unmeasured → sec:dependent-adapter.
- R5.1: full state, native equation/casts, fuel theorem, selected realization/equation cache, no global recursive axiom → sec:recursion-capabilities, sec:recursion-simulation.
- R5.2: field/guard/call-argument watchers; zero-or-one plus positive example; observed/ranking/certified progression → sec:recursion-angels.
- R5.3: difference-list/product/parameter alternatives, depth-two syntax only, bounded measure/proof grammar and trace/provider/proof dimensions → sec:recursion-basis, sec:recursion-evaluation.

### N7

Source: new/7/Leant2_Expert_Questions/article.tex, R3.1–R5.3.

- R3.1: wrong-fiber vector, proof/dictionary environment, necessary implication versus assembly → sec:evaluation-closures, sec:evaluation-observations.
- R3.2: named Adapton/from-scratch consistency, branch-owned watchers, demand reads/irrelevant changes, extra dependencies safe/missing unsafe → sec:evaluation-cache, prop:evaluation-cache.
- R3.3: source-available CBV not performance, closed/open certificates, fragment over-approximation theorem subsumed by certificate/coverage conditions, exception tests → sec:evaluation-certification, sec:evaluation-checks.
- R3.4: full explicit/implicit tuples, independent angels loose not automatically unsound, finite state graph includes proof plans, no repeat/fair/exact decisions, literal/helper bounds → sec:evaluation-angelic, thm:evaluation-bounded.
- R4.1: transactional motive equality, three dimensions, Nat/index search exclusions, failed-IH dependency closure → sec:dependent-scope, sec:dependent-motives.
- R4.2: definitional/propositional/observational distinction, typed local equality graph, orientation/provenance, ranking does not erase typing → sec:dependent-transports.
- R4.3: documented unfold/unfold!/red/ered and no induction; four-tier policy; F(?n) narrowing versus scheduling; version/cross-assistant limits → sec:dependent-unfolding.
- R4.4: save more than goals, sort/index diagnostic categories, failed trials leave next unchanged → sec:dependent-adapter.
- R5.1: capability/finite derivation, no interactive uniform fuel, checked negatives and logical/executable boundary → sec:recursion-simulation, sec:recursion-publication.
- R5.2: hash-consed typed calls, three evidence levels, assumption-scoped nogoods, sparse/full-trace comparison → sec:recursion-angels, sec:recursion-evaluation.
- R5.3: joint-state/nested alternatives, total cost, proof-plan restricted measures, mutual/generated declarations, coinductive/partial outside total profile → sec:recursion-basis, sec:recursion-evaluation.

### N8

Source: new/8/leant2_expert_answers/article.tex, R3.1–R5.3.

- R3.1: neutral application resumed with lambda, speculative index fiber invalidation, closed prefix mismatch/open tail, exhaustive alternatives → sec:evaluation-closures.
- R3.2: hash-consing/demand queue/persistent roots, dynamic versus syntactic dependencies, retained-world memory and stronger instance/transitive tests → sec:evaluation-cache.
- R3.3: compact delayed certificate checking/cached summaries, rigid mismatch/arithmetic certificates, lawful equality, uncertified native pruning forfeits coverage → sec:evaluation-certification, sec:evaluation-deployment.
- R3.4: infinite-result guessed sets, conditional cache facts, finite theorem with helper/instance/retrieval/proof qualifications → sec:evaluation-angelic.
- R4.1: dependency subsets/suffixes, proof-carrying vector, recipe with transports and distinct outcome classes → sec:dependent-motives, sec:dependent-adapter.
- R4.2: certified normalizer boundaries, distinct normal forms not universal inequality, consistent provider/constructor cast placement, typed deferred transport → sec:dependent-transports.
- R4.3: distinct phase policies, resumable escalation, per-constant budgets and cycles → sec:dependent-unfolding.
- R4.4: recipe/principle/transport adapter and functional induction, near ill-scoped control, instantiation-versus-search metrics → sec:dependent-adapter.
- R5.1: Lean4.27 exception, successful-fuel versus eventual success, direct certified template versus per-trial declaration, environment/accounting → sec:recursion-simulation, sec:recursion-capabilities.
- R5.2: interface-abstracted pool, assumption/spec-indexed counterexamples, no global input ban, omitted-internal-calls test → sec:recursion-angels, sec:recursion-evaluation.
- R5.3: Para 59 benchmarks/list equations, structural/state/nested/measured basis, provider-hidden complexity, reference/oracle/automatic tracks, worklist limits → sec:recursion-basis, sec:recursion-evaluation.

### N9

Source: new/9/leant2-expert-answers.tex, R3.Q1–R5.Q3.

- R3.Q1: typed contextual closures, erased vectors insufficient, metamorphic f(0)=f(1), registered necessity-proof inversions → sec:evaluation-closures.
- R3.Q2: full environment/telescope/policy/read key and hash checking, ledger/blocker lifetimes, timeout only cost estimate → sec:evaluation-cache.
- R3.Q3: three routes, infinite quantification symbolic, representation covers every completion, substitution/preprocessing obligations, replay costs can erase gain → sec:evaluation-certification, sec:evaluation-checks.
- R3.Q4: consistent existential oracle, strict pair-count decrease proof as bounded theorem instance, infinite helpers/unfolding/results, helper argument distinction → sec:evaluation-angelic.
- R4.Q1: mandatory versus optional generalization, finite-combination theorem, fresh compound indices retain equalities → sec:dependent-motives, prop:dependent-motives.
- R4.Q2: commuted-index vector, endpoints/provenance, bounded orientation, hard dedup versus grouping fingerprint → sec:dependent-transports.
- R4.Q3: provider head remains atomic in compositions, low-stage failure cannot eliminate later-stage grammar, Coq-specific external controls → sec:dependent-unfolding.
- R4.Q4: exact prefix/induction signatures, FVarSubst consumed, pinned diagnostics/resources, inspection is not compiled integration → sec:dependent-adapter.
- R5.Q1: frame-scoped capability, dependent derivation simulation, elaboration/templates alternatives, native reduction blacklist → sec:recursion-capabilities, sec:recursion-simulation.
- R5.Q2: universe/frame/environment keys, shared call observations, seed-only helper facts, reopen helper/carrier alternatives → sec:recursion-angels.
- R5.Q3: overlapping structural/state/generalized/measure tiers, actual decrease proofs, witness then scheme+carrier/scheme-only/unassisted tracks → sec:recursion-basis, sec:recursion-evaluation.

## Supplementary items and deduplication with existing documents

- Existing proposal11's four evaluation shortcomings and 45% profile remain explicitly historical in sec:evaluation-scope. Closed differential testing remains useful, but the old suggestion that it establishes open conservativity is superseded by the certificate/substitution requirements.
- Existing Smyth first-order/trace-completeness assertions are corrected. The old active question lists are deleted.
- Existing R4 narrowing remains in sec:dependent-unfolding; n+0 is corrected to 0+n; the original two-cast bound remains an explicitly grammar-restricting experiment. Unsupported general claims about other tools' lack of indexed/generalized induction are corrected.
- Existing R5 simultaneous-argument/Fibonacci necessities are corrected to alternative encodings. The one-helper bound, original ten-second probes, regression preservation, and full original contract remain explicit.
- Proposal10's detailed recursor-metadata procedures, proof-carrying motives, branch substitutions, vector-map/zip/lookup traces, final specialization, and two-product lowering remain existing authoritative specifications. Proposal11 refers to them rather than repeating full traces. New response-specific conditions/native API evidence/simulation/publication precedents are integrated here.
- All nine source question-index tables repeat the historical mapping above. Their source/validation scope is retained in the root evidence ledger.

## Executable model evidence associated with these topics

Root preserves and reruns the supplied scripts/results. This section maps their conceptual payload, not a new Lean validation claim.

| Package | Topic model item | Canonical interpretation |
|---|---|---|
| N1 | rollback identity; inconsistent same-call angels; one failed angel; Fibonacci pair invariant on 31 inputs | sec:evaluation-cache, sec:evaluation-angelic, sec:recursion-basis |
| N2 | branch-blind cache and transitive assignment dependency; finite observation agreement | sec:evaluation-cache, sec:evaluation-closures |
| N3 | A/B/A-with-unrelated-change gives true/false/true with two evaluations and one hit; concrete outputs {0,1}, guessed {0}, desired {1} | prop:evaluation-cache, sec:evaluation-certification |
| N4 | stale raw value zero versus branch-B value one | sec:evaluation-cache |
| N5 | stale false cache versus true sibling, versioned branch distinction | sec:evaluation-cache |
| N6 | reused generation-one ABA; Fibonacci pair versus fast doubling on 61 inputs | sec:evaluation-cache, sec:recursion-basis |
| N7 | two inconsistent Boolean angel pairs versus zero equal-call pairs satisfying inequality | sec:evaluation-angelic; lack of correlation is a loose abstraction, not automatically unsound pruning |
| N8 | ?x+1 gives stale 1 versus correct 2; proposed local-instance/type-index/transitive variants remain integration tests | sec:evaluation-cache |
| N9 | included models concern reverse, unary machines, and prefix summaries, with no separate native R3–R5 validation | Carrier/evidence integration owns numerical receipts; these sections retain only design claims |

## Reconciliations and rejected overclaims

1. Reject the old categorical first-order/trace-complete Smyth description; retain core-versus-implementation and dependent-port boundaries.
2. Reject tests-as-conservativity-proof. Preserve countermodels/validation artifacts without promoting them to Lean or engine measurements.
3. Exact oracle semantics correlates equal calls. N4/N6/N7/N8 clarify that a declared relaxation may omit correlations safely but weakly; it cannot count angelic success as a real program. Unjustified correlations/value restrictions are the dangerous exclusions.
4. Contract-derived call assumptions remain conditional. Their contradiction excludes contract-satisfying completions, not every arbitrary execution.
5. Reject both universal interpreter definitional agreement and the opposite universal nonreduction claim. N5/N8's Lean4.27 natural-measure exception remains.
6. N4/N6/N7's concrete CBV backend refines the fragment-evaluator proposal; neither alternative nor its axiom/dependent-position limits is deleted.
7. N6 did not verify sauto defaults. Exact controls from N1/N3/N7/N9 are attributed to documentation, not timing or induction-discovery evidence.
8. The 2^k motive bound covers a finite scoped construction only; nonmaximal occurrences/new state/strengthening require additional dimensions. Timeouts do not prove exhaustion.
9. Reject unrestricted cast erasure and zero-cost enumeration; retain low proof display weight under typed reconstruction and a finite/graded/canonical syntax discipline.
10. Para's 59 tasks, handwritten witnesses, and Python examples do not establish automatic Leant2 coverage or ten-second discovery.

## Bibliography coordination

New consolidated keys used: selfadjust, adapton, canonicalmin, scrybe,
leaninduction, leancbv, leantactics, leannat, lean427, leanrecursion, lean4lean,
lean4lean2026, sautodocs, para, cataclyst.
Existing keys retained: hazel, smyth, myth, lambda2, frankle16, burst, huet75,
miller91, abelpientka11, cockx, canonical, agsy, sauto, sizechange, trio, synquid.
The requested leanreccompiled alias was merged into leannat because both refer
to the same pinned core source. Root owns the bibliography itself.

## Current agenda locations

- R3.N1–R3.N4: sec:evaluation-checks, covering certified residual fragment, complete efficient cache dependencies, measured checked backends, and bounded relational oracles.
- R4.N1–R4.N4: sec:dependent-open, covering useful recipe grammar, certified transport theories, measured transparency, and complete transactional native adapter.
- R5.N1–R5.N4: sec:recursion-evaluation, covering typed interpreter realization/fuel, shared helper/oracle constraints, measured scheme portfolio, and proof-backed executable publication.

Canonical topic sections alone contain the full new question wording.
