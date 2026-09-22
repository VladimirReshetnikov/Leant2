# Contracts, retrieval, ranking, and learned-guidance integration

Scope: maintained sections 10-contracts.tex, 11-retrieval.tex, and 12-ranking.tex in proposal 11. The common semantic authority and result algebra live in root-owned 02a-semantics.tex; earlier unified-proposal proof-service and observational-bucket policies remain canonical for their base interfaces.

All nine incoming packages were read for historical R6.1–R6.4, R7.1–R7.3, R8.1–R8.2, and R9.1–R9.2. This ledger maps those 99 source-question answers to one maintained treatment each, then records source-specific additions, disagreements, rejected overclaims, and new questions. No incoming finite-model success is promoted to native Lean validation or a performance result.

## Source paths and complete question coverage

Paths below identify the original incoming source, even after root removes the completed incoming directory. N identifiers are the stable provenance names.

| Source | Original source and covered items | Canonical mapping |
| --- | --- | --- |
| N1 | new/1/sections/07-contracts.tex, questions R6.Q1–Q4; 08-retrieval.tex, R7.Q1–Q3; 09-ranking-learning.tex, R8.Q1–Q2 and R9.Q1–Q2 | All eleven rows in the shared mapping below |
| N2 | new/2/Leant2_Expert_Answers/Leant2_Expert_Answers.tex, sections R6–R9, questions R6.1–R6.4, R7.1–R7.3, R8.1–R8.2, R9.1–R9.2 | All eleven rows below |
| N3 | new/3/leant2-expert-answers/sections/07-contracts.tex, 08-retrieval.tex, 09-ranking-learning.tex, all eleven R6–R9 questions | All eleven rows below |
| N4 | new/4/leant2_expert_answers/leant2_expert_answers.tex, sections R6–R9, all eleven numbered questions | All eleven rows below |
| N5 | new/5/leant2_expert_answers/sections/08_contracts.tex, 09_retrieval.tex, 10_ranking.tex, 11_learning.tex, all eleven R6.Q1–R9.Q2 questions | All eleven rows below |
| N6 | new/6/leant2_expert_answers.tex, sections R6–R9, labels q:R6.1 through q:R9.2 | All eleven rows below |
| N7 | new/7/Leant2_Expert_Questions/article.tex, sections R6–R9, all eleven numbered questions | All eleven rows below |
| N8 | new/8/leant2_expert_answers/article.tex, sections R6–R9, q61–q64, q71–q73, q81–q82, q91–q92 | All eleven rows below |
| N9 | new/9/leant2-expert-answers.tex, sections R6–R9, R6.Q1–Q4, R7.Q1–Q3, R8.Q1–Q2, R9.Q1–Q2 | All eleven rows below |

For EACH N1–N9, the following is the exhaustive source-question-to-canonical mapping. Repeated arguments are merged, not reproduced nine times. “Partial” describes what remains open, not an omission of incoming content.

| Historical question | Disposition and answer | Canonical label(s) | Replacement active questions |
| --- | --- | --- | --- |
| R6.1 Value/proof interleaving | Answered as dependency-sensitive readiness, uniform/assigning/conditional proof effects, finite checked predicate abstraction, contextual adapter; implementation remains open | sec:contract-boundary; sec:contract-readiness | R6.N2 |
| R6.2 Recognizable induction class | Partial: explicit sufficient certificate grammar and proof established; arbitrary invariant discovery not solved | sec:contract-local-certificates; prop:contract-local-certification; eq:contract-vc-base/step/finish | R6.N1 |
| R6.3 Usable induction automation | Partial: source-level native facilities and service plan identified; task coverage, lemma invention, and bounded integration unmeasured | sec:contract-induction-service; sec:contract-open | R6.N1–N2 |
| R6.4 Proof-debt policy | Partial: fair deterministic policy and restricted independent-job exchange argument; no optimal policy for correlated search | sec:contract-proof-debt | R6.N3 |
| R7.1 Dependent abstraction | Partial: typed AND-hypergraph, worked counterexamples, refinement loop, and simulation proposition; useful granularity/native certificate unimplemented | sec:retrieval-hypergraph; prop:retrieval-simulation; sec:retrieval-loop | R7.N1 |
| R7.2 Type classes in TYGAR | Answered yes; explicit dictionary adaptation and cache requirements integrated | sec:retrieval-boundary; sec:retrieval-dictionaries | R7.N2 |
| R7.3 Data-goal selection and corpus | Partial: pinned API capability answered; behavior-conditioned relevance and end-to-end effects need experiment | sec:retrieval-corpus | R7.N3 |
| R8.1 Ranking objective | Partial: valid declared MDL/preference objective and stopping theorem; empirical agreement with user intent unknown | sec:ranking-objective; sec:ranking-stopping; prop:ranking-stop | R8.N1; R8.N3 |
| R8.2 Candidate equivalence | Answered as four layers with dependent typing and congruence boundaries; useful certified quotient fragment remains open | sec:ranking-equivalence | R8.N2 |
| R9.1 Model proposal accuracy | Unmeasured: no transferable numerical result; exact success events and study protocol integrated | sec:learning-measurement | R9.N1 |
| R9.2 Determinism and auditability | Answered architecturally by bounded data proposals, distinct audit objects, full recorded stream, grammar accounting; implementation open | sec:learning-interface; sec:learning-replay | R9.N2–N3 |

## Source-specific substantive dispositions

### N1

- R6.Q1: kept the uniform/equality-constraining proof counterargument, support over types/instances/hypotheses, finite certified predicates, map subtype example, and specific free-variable rejection in proofPortfolio. Canonical contract-boundary/readiness. Repetition in other reports merged.
- R6.Q2 and theorem thm:vc: retained explicit base, step, and observation implication plus the structural-induction proof; bounded rewrite/decision-theory recognition and reverse/sorting limits. Canonical contract-local-certificates.
- R6.Q3: retained MVarId.induction and functional induction distinction, moving manual versus pinned toolchain qualification, native leaf solvers, optional Aesop/Canonical/hammer separation, and timeout semantics. Canonical contract-induction-service. No source-only API observation is described as integration-tested.
- R6.Q4 equation (9): merged benefit/setup-cost score, correlated-arm caveat, resumable jobs, support fingerprints, fair reserve, logical epochs and equal-work evaluation into contract-proof-debt.
- R7.Q1 proposition prop:retrieval: merged into retrieval-simulation with stronger explicit construction/bound correspondence; retained copying/weakening example, justified-only refinement, universes and fallback.
- R7.Q2: retained direct positive Hoogle+ answer, full context/assignment cache identity, and computational dictionary semantics in retrieval-dictionaries.
- R7.Q3: retained data-goal lookup example, observation-conditioned adapter, training from elaborated component use, answer leakage audit, API-versus-body tracks, standalone-component mismatch limit in retrieval-corpus/loop.
- R8.Q1 equation (10): retained frozen grammar prior, runtime/proof preferences, soft input use, exact-versus-semantic reference rank and frontier inclusion of proof/retrieval alternatives in ranking-objective/stopping.
- R8.Q2: retained alpha identity, transactional conversion, transports, unknown observations, reversible groups and congruence requirement in ranking-equivalence.
- R9.Q1: retained four distinct success stages, family-held-out evaluation, one-batch hypothesis and broader 2026 synthesis study as nontransferable adjacent evidence in learning-measurement. No percentage imported.
- R9.Q2: retained proof/search/model replay distinction, immutable integer-ranked artifacts, restricted syntax, full provenance and finite-time versus exhaustive reordering distinction in learning-interface/replay.

### N2

- R6.1: explicit cons proof congArg Nat.succ and the existing closed-goal service gap are kept in contract-readiness/boundary; no generic tactic success substituted for local construction.
- R6.2–R6.3: structural branch-certificate proof, Presburger fragment conditions, synthesized equation provenance, named versus anonymous functional induction, and exact unresolved outcomes merge into local-certificates/induction-service.
- R6.4: retained the full first-rejection expected-cost derivation, then its scope limit, active-debt suspension and fair aging in contract-proof-debt; unified with N3's first-success derivation.
- R7.1: retained hyperedge argument conjunction, reusable locals, actual abstraction refinement versus mere filtering, path-three limit and fallback in retrieval-hypergraph/loop.
- R7.2: retained Hoogle+ higher-kinded limitation, native transactional instance assignments, full cache expression and dictionary behavior in retrieval-dictionaries.
- R7.3: exact Selector/Config shape and absence of default core engine merged into retrieval-corpus, along with permitted-body dependency labels, chronological/family splits and optional-network accounting.
- R8.1: uniquely retained derivation probability versus program probability and canonical/minimum derivation choice, all-cost objective, pending frontier coverage and margin scope in ranking-objective/stopping.
- R8.2: retained Empty/Unit non-equivalence, contract-probe inability to separate accepted answers, finite-bucket counterexample and typed identity in ranking-equivalence.
- R9.1: retained isomorphic sufficient carriers, equal provider/profile conditions, useful helper only after realization, all latency and failure records in learning-measurement.
- R9.2: retained digests/signatures as provenance rather than logic, arbitrary-command side effects, grammar-expansion epochs and independent certificate replay in learning-interface/replay.

### N3

- R6.1: retained three-stage cheap propagation/local proof/global debt, existential holes versus universal binders, instance special role, and finite certified predicate domain in contract-readiness.
- R6.2: generalized constructor algebra with one invariant hypothesis per recursive child, dependent fibers, quantified changing accumulators, and involution's second traversal are kept in contract-local-certificates.
- R6.3: source audit of evalFunInduction/fun_cases, anonymous recursor limitation, native cancellation limits and isolated optional service are kept in contract-induction-service. Historical ambient-heartbeat implementation details are not prescribed as future semantics.
- R6.4: retained full independent-proof p/t exchange derivation and failed-tier/setup-cost qualifications in contract-proof-debt.
- R7.1: shared List A -> Option A counterexample, index patterns, output-sensitive discrimination-tree cost and refinement requirements in retrieval-hypergraph/loop.
- R7.2–R7.3: full dictionary cache state, output-parameter assignments, selector hint may be ignored, concrete caller tag and separate retrieval tracks in retrieval-dictionaries/corpus.
- R8.1: explicit noiseless posterior-prior equation, helper/carrier cost, stable serialized tie and top-k semantic-class stopping distinction in ranking-objective/stopping.
- R8.2: natural cutoff example, dependent fiber comparison and extensional equality versus implementation cost (quadratic/linear reverse) in ranking-equivalence.
- R9.1: oracle opportunity, top-k validity versus expressibility versus useful-at-budget, task-family resampling and paired equal total time in learning-measurement.
- R9.2: uniquely explicit four audit levels (proof, realization, search, model), bounded proposal forms, grammar extension and absence of model as no negative evidence in learning-interface/replay.

### N4

- R6.1: debt records owning candidate/context/snapshot and local subtype example merge into contract-readiness.
- R6.2: retain distinction between Presburger theory and particular capped omega/grind implementations; failure outside certified rules never refutes original program. Canonical contract-local-certificates.
- R6.3: retain version-specific adapters, lookup before repetitive induction and twenty-or-more hand-classified quantified-contract experiment in induction-service/open.
- R6.4: information-value term, warm-context batching, logical rounds and changed-support retries kept in contract-proof-debt.
- R7.1: explicit A -> B -> C conjunction counterexample, dependent telescope index correlation, higher-order introductions and query-scoped refinement retained in retrieval-hypergraph/loop.
- R7.2: direct dictionary-passing history, local priorities and resolution options merge into retrieval-dictionaries.
- R7.3: transitive forbidden reconstruction audit, external oracle separation, provider-given/retrieval/helper tracks and downstream-versus-recall metrics retained in retrieval-corpus.
- R8.1: proper distribution or declared subprobability/prefix encoding, nonfree hidden helper bodies, separate execution status and stable identity retained in ranking-objective.
- R8.2: proof-insensitive display versus typed structural collision check, guarded future-context congruence retained in ranking-equivalence.
- R9.1: guidance-only versus grammar-expanded arms plus carrier oracle retained in learning-measurement.
- R9.2: raw response and parsed representation, absence/cancellation as input events and logical admission points retained in learning-replay.

### N5

- R6.Q1: three legitimate effects of proof jobs, relational-contract coupling, predicate joins forget unsupported facts in contract-readiness.
- R6.Q2: explicit finish implication, carrier/invariant/finisher separately budgeted and finite theory boundary in contract-local-certificates.
- R6.Q3–Q4: core/optional deployment distinction, non-Boolean proof-service outcomes, cooperative/hard timeouts, fair growing quanta, generalized helper proof reuse, precondition-bearing shared counterexamples in induction-service/proof-debt.
- R7.Q1: vector append A/n/m/(n+m) sharing counterexample and function/constructor/cast coverage obligation in retrieval-hypergraph.
- R7.Q2: 291 components/44 queries historical scale, dictionary laws as explicit evidence, contraction and weakening in retrieval-boundary/dictionaries.
- R7.Q3: controlled environments, body oracle separation, definition-family split, primitive/API/indexed tracks in retrieval-corpus.
- R8.Q1: all helper costs, finite-grade grammar with zero-cost-cycle concern, separate proof/presentation cost, explicit acceptance versus preference in ranking-objective.
- R8.Q2: parametric length-cutoff counterexample, recoverable representatives, cost-preserving congruence in ranking-equivalence.
- R9.Q1: explicit direct model-program comparison arm kept separate from carrier-only guidance, k=1/3/10 and export/compilation endpoint in learning-measurement.
- R9.Q2: size/grammar/scope validation, resource limits on malformed proposals, optional-private-data policy, immutable query and exact universes, explicit native grammar membership in learning-interface/replay.

### N6

- R6.1: productive dependency-triggered wakes versus repeated unchanged proof attempts in contract-readiness/open.
- R6.2: invariant input retained and separate finish condition; explicit “template applicable but invariant missing” outcome in contract-local-certificates.
- R6.3: hand-classified proof suite and no transfer from hammer retrieval to induction coverage in induction-service/open.
- R6.4: task continuations versus nonresumable tactic internals, cache valid preprocessing and count wake/retry/debt events in proof-debt.
- R7.1: symbolic universe relations, top for unknown indices, lost-information failure classes in retrieval-hypergraph/loop.
- R7.2: EqD method/list-instance worked translation and positive dictionary replay in retrieval-dictionaries.
- R7.3: Selector fields, cloud cold-start accounting, dependency-label ambiguity and sufficient-component recall in retrieval-corpus.
- R8.1: full carrier/finisher/helper representation cost and explicit Natarajan/Mayer PBE ranking/disambiguation precedent in ranking-objective.
- R8.2: first-order pointwise DSL as a potentially valid congruence setting, contrast with new higher-order input in ranking-equivalence.
- R9.1: prompt information-condition distinctions, unknown combinations and alternative sufficient carrier representations in learning-measurement.
- R9.2: content-addressed full manifest, model bytes independent of replay, zero-score starvation and grammar extension in learning-replay.

### N7

- R6.1: proof assignments are branch choices; dependent input validity for counterexamples in readiness/proof-debt.
- R6.2: finite proof-plan grammar and branch equality-transport composition; plan receipts as useful labeled data retained in local-certificates (plan/invariant/failed-condition provenance).
- R6.3: HipSpec-style conjecture bank, no unproved rewrite rules, generated theorem names in scratch environment in induction-service.
- R6.4: time-to-certified versus time-to-unproved gap, switching/reconstruction costs, old-debt fair baseline in proof-debt/open.
- R7.1: F(?b) changing Nat/Bool head example and function-valued argument distinction in retrieval-hypergraph.
- R7.2: functional dependencies in Hoogle+, local instance priorities and environment/index identity in retrieval-dictionaries.
- R7.3: body-erasure leakage via compiler helpers and proofs, observed-spec origin, cold/warm and applicability metrics in retrieval-corpus.
- R8.1: computational/type/proof input roles, blinded preference/edit-distance/time-to-satisfactory metrics in ranking-objective.
- R8.2: type-former structural/elimination summaries and observer absence, reversible groups in ranking-equivalence.
- R9.1: trace-completeness by carrier-knowledge matrix, renamed entities insufficient for contamination control, cold/resident/remote cost tracks in learning-measurement.
- R9.2: complete proposal boundary, scoped hard-prune records and CoqHammer reconstruction analogy in learning-replay.

### N8

- R6.1: existing Engine root Subtype pairing is retained explicitly; recursive motive extension is the actual new work. Canonical contract-boundary/readiness.
- R6.2: critical original-contract versus failed invariant-pair distinction, finite-coefficient arithmetic and branch-specific solver admission in contract-local-certificates.
- R6.3: historical functional-induction and induction-oriented try? observations treated as pinned-integration leads, not demonstrated performance in induction-service.
- R6.4: starvation when proof work waits for idle enumeration, separate logical quotas and deadline, shared-context batching in proof-debt.
- R7.1: abstract initial terms and construction simulation with complete concrete grammar in retrieval-simulation.
- R7.2: actual dictionary semantics, completeness of even closed negative resolution not presumed, contextual cache in retrieval-dictionaries.
- R7.3: exact Selector API/hint semantics; upstream documented 10–20s preparation explicitly historical and not measured here; noncomputable corpus exclusions and sufficient-component-set metric in retrieval-corpus.
- R8.1: PBE ranking of a suitable alternative rather than one syntactic target, noisy-likelihood cannot weaken hard contracts in ranking-objective.
- R8.2: 0 versus n(n-1) counterexample, typed dependent observers and no universal type-value observer in ranking-equivalence.
- R9.1: explicit Wilson interval and nonindependent task-family caveat retained in learning-measurement.
- R9.2: frozen-query gate hardening distinguished from observed current engine correctness, ephemeral-name canonicalization, grammar membership versus top-k restriction in learning-interface/replay.

### N9

- R6.Q1: proofs may enable recursive capabilities; failed local invariants reopen carrier/stronger predicate choices; finite tests do not change universal contract in readiness/local-certificates.
- R6.Q2: returned failed local obligation feeds generalization, retrieval, or proof job in local-certificates.
- R6.Q3: separate induction-planner and leaf-solver resources, static pinned API evidence not compiled integration in induction-service.
- R6.Q4: weighted round-robin/deficit policy, geometrically increasing quanta, near-deadline certification reserve and hidden unproved survivors in proof-debt.
- R7.Q1: precise construction-bound simulation, unknown universes/indices and complete prerequisite/reuse accounting in retrieval-hypergraph/loop.
- R7.Q2: dictionary assignment can determine output parameters, evidence-sensitive identity and scoped failures in retrieval-dictionaries.
- R7.Q3: data-goal Selector, dependency-state adapter, provider-policy checks, before-target environment and public pretraining contamination in retrieval-corpus.
- R8.Q1: nonnegative weights, deterministic operation counts or frozen measured features, full auxiliary cost in ranking-objective.
- R8.Q2 and stopping subsection: unknown observations never equality; complete deferred-lane/grammar-extension frontier; objective mismatch and grace period limits in ranking-equivalence/stopping.
- R9.Q1: ordinary/function/option/tuple/indexed/helper strata, motive/helper oracle and regressions on previously solved queries in learning-measurement.
- R9.Q2: deterministic asynchronous admission checkpoints, absence events, environment artifact and local-instance digests, canonical scratch names in learning-replay.

## Replaced claims and non-adopted shortcuts

| Previous or incoming shortcut | Disposition | Maintained resolution |
| --- | --- | --- |
| Proof search with holes is meaningless; always defer proofs last | Rejected | Three proof effects, dependencies and contextual transactions; contract-readiness |
| Root subtype pairing is wholly new work | Corrected | Existing root packaging versus recursive proof-carrying motive; contract-boundary |
| Pointwise subtype solves arbitrary relational contracts | Rejected | Multi-call/involution/homomorphism need stronger invariants or global proof |
| Failed local invariant proves candidate wrong | Rejected | Reject program–invariant pair only unless original contract refuted |
| Calling omega/grind proves complete Presburger support under caps | Rejected | Completeness requires a declared certified solver fragment and operational conditions |
| Pay all expensive debt only when search idle; fixed milliseconds are deterministic | Rejected | Positive logical service, resumable tiers, separate deadline and calibration |
| Ordinary type-head path witnesses multi-argument composition | Rejected as witness | AND-hyperedge; graph may remain a coarse over-approximation |
| Every failed concrete elaboration is a refinement theorem | Rejected | Justified mismatch only; timeout/open constraints remain unknown |
| Hoogle+ has no class treatment / its experiment proves huge Lean-library scale | Corrected | Dictionary passing already exists; reported 291/44, narrower type language |
| Cache instances by class and one type / erase computational instances | Rejected | Full contextual goal and actual dictionary evidence |
| Selector hint implies learned example understanding | Rejected | API capability separate from measured data-goal backend |
| Full-task mismatch refutes a useful intermediate component | Rejected | Behavioral features are ranking absent a compositional necessity proof |
| Shortest/reference/input-using program is necessarily intended | Rejected | Frozen preference model; human/task evaluation |
| Printed equality or finite fingerprints imply semantic equality | Rejected | Four typed layers, collision checks, reversible grouping |
| Parametricity removes all finite-sample length limits | Rejected | Length-cutoff counterexample retained |
| Cost frontier/grace period alone proves displayed optimum | Rejected | Same-objective bound and all deferred candidates, top-k scope |
| Existing model/proof success percentages transfer to carrier invention | Rejected | Exact task experiment, no invented accuracy |
| Temperature zero/seed alone guarantees reproducibility | Rejected | Recorded streams and separate model regeneration |
| Only-reorder preserves identical finite-budget results | Corrected | Fixed finite exhaustive grammar plus fairness; deadlines differ |
| Arbitrary new carrier/helper is only a reorder | Rejected | Membership test or explicit extended grammar and scope |
| Final kernel gate makes arbitrary generated commands safe | Rejected | Restricted bounded data proposals, isolated elaboration, frozen authority |

## Active expert agenda

The authoritative question wording appears once, in the maintained topic sections:

- R6.N1–R6.N3: 10-contracts.tex, sec:contract-open.
- R7.N1–R7.N3: 11-retrieval.tex, sec:retrieval-open.
- R8.N1–R8.N3: 12-ranking.tex, sec:ranking-open.
- R9.N1–R9.N3: 12-ranking.tex, sec:learning-open.

The historical-question table above records which unresolved part each question replaces. The global expert-contact section references these IDs rather than duplicating their wording.

## Bibliography and evidence handoff

The three sections use existing bibliography keys synquid, aesop, canonical, leanhammer, sypet, hoogleplus, leandojo, deepcoder, probe, dreamcoder and the root-added canonical keys leaninduction, leanfuninduction, leanlibrary, hipspec. The following distinct original references were retained by the final bibliography pass; their historical origin is preserved without claiming a new external survey:

- Pinned Lean 4.34 source: N3 references.tex entries leanfuninduction (src/Lean/Elab/Tactic/Induction.lean) and leanlibrary (src/Lean/LibrarySuggestions/Basic.lean); N1 references.tex leaninduction.
- HipSpec: N6 bibliography hipspec, Claessen/Johansson/Rosen/Smallbone, CADE 2013, DOI 10.1007/978-3-642-38574-2_27.
- Natarajan et al., Learning Natural Programs from a Few Examples in Real-Time, AISTATS 2019, PMLR 89:1714–1722; N6 ranking-study.
- Mayer et al., User Interaction Models for Disambiguation in Programming by Example, UIST 2015, DOI 10.1145/2807442.2807459; N6 pbe-interaction.
- Singh/Gulwani, Predicting a Correct Program in Programming by Example, CAV 2015; N8 ranking.
- Zilberstein, Using Anytime Algorithms in Intelligent Systems, AI Magazine 17(3), 1996, DOI 10.1609/aimag.v17i3.1232; N8 anytime.
- Bhatia/Svegliato/Nashed/Zilberstein, Tuning the Hyperparameters of Anytime Planning: A Metareasoning Approach with Deep Reinforcement Learning, ICAPS 2022, DOI 10.1609/icaps.v32i1.19842; N8 metareasoning.
- N8 premise-selection README source for historically reported 10–20s session preparation; no new timing experiment.
- N1/N3 Lean proof validation and N7 CoqHammer reconstruction documentation for proposal-code versus proof-artifact boundary.
- The canonical LeanHammer entry preserves the supplied later 2026 revision/conference metadata in place of the earlier preprint-only entry. Do not claim new publication verification from these local reports alone.

Validation performed by this agent: read and mapped all 99 assigned incoming question answers; inspected the existing unified proposal's proof-service, CEGIS, ranking, caching, and bucket policies; source-checked the current Engine root subtype/printed dedup and Search/Core proofPortfolio free-variable guard; static QA passed for all three edited sections: balanced TeX environments, all citation keys and cross-references present in current proposal source, 31 labels, 12 active new questions, no answered historical questions left in active lists, and no diff whitespace errors. The three sections contain 6,588 whitespace-delimited words in total. No Lean compilation, model experiment, performance run, PDF build, source-package deletion, commit, or push by this agent. Root owns global build, rendered verification, evidence preservation, deletions, commits and push.
