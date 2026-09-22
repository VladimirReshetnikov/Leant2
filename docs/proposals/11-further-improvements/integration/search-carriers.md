# Search and carrier integration coverage

This ledger covers R1 and R2 from **all nine incoming packages**, integrated into `sections/05-search.tex` and `sections/06-carriers.tex`. N1–N9 are the incoming-package identifiers used by the canonical source ledger. Historical source question IDs are provenance, not the active expert agenda. The answered historical questions have been removed from that agenda and replaced by R1.N1–N4 and R2.N1–N5 below.

The integration preserves the original section labels `sec:search` and `sec:carriers`. Repeated arguments appear once at the canonical labels listed below; the source variants remain attributable through this ledger and the central archived evidence. No incoming directory was deleted by this integration worker. No production Lean change, native validation, PDF build, or new performance result is claimed here.

## Historical question-to-answer map

The source spelling is `R1.Q1`/`R2.Q1` in N1, N5 and N9 and `R1.1`/`R2.1` in N2, N3, N4, N6, N7 and N8. Each row below maps the corresponding question in **every** N1–N9 package; there are 81 incoming question instances in this topic range.

| Historical question | Disposition of the question | Canonical answer labels | New active question |
|---|---|---|---|
| R1.1 / R1.Q1: organization and independence | Conditional factorization is answered; effect analysis, cost and scalable implementation remain open. | `sec:search-factorization`, `prop:search-factorization` | R1.N1 |
| R1.2 / R1.Q2: admissible heuristic | Zero, maximum, cost partition and simulation theorem answer admissibility; a useful cheap concrete abstraction remains open. | `sec:search-bounds`, `prop:search-abstract-bound` | R1.N2 |
| R1.3 / R1.Q3: learning and ranking | Fixed objective versus priority, fairness, rekeying and frontier certificates answer the semantic distinction; matched empirical benefit remains open. | `sec:search-learning` | R1.N3 |
| R1.4 / R1.Q4: wall-clock invariance | Unconditional requirement refuted by a proof; deterministic logical prefixes answer the achievable alternative. Practical replay and cancellation protocol remains open. | `sec:search-deadlines`, `prop:search-deadline` | R1.N4 |
| R2.1 / R2.Q1: minimal carrier from samples | Exact finite-state and bounded-package problems answered constructively; unrestricted intended minimal type is not identifiable/decidable by those procedures. Native integration remains open. | `sec:carrier-package`, `sec:carrier-quotient`, `thm:carrier-quotient`, `sec:carrier-finite`, `thm:carrier-finite-machine`, `sec:carrier-lower-bounds`, `prop:carrier-capacity` | R2.N1, R2.N4 |
| R2.2 / R2.Q2: polymorphic alphabet | Naturality gives the shape–position theorem and bounded-length consequence. Provider certification, indexed extension and a syntax-to-test-depth theorem remain open. | `sec:carrier-parametricity`, `thm:carrier-containers`, `eq:carrier-position-test` | R2.N2 |
| R2.3 / R2.Q3: backwards fusion and auxiliaries | Section-based construction, feature separation, closure and bounded completeness answer restricted variants; efficient sparse-contract invention remains open. | `sec:carrier-lifting`, `prop:carrier-section-fold`, `eq:carrier-feature-closure`, `sec:carrier-worked`, `sec:carrier-prefix-sum`, `prop:carrier-prefix-monoid` | R2.N3, R2.N4 |
| R2.4 / R2.Q4: complete motive enumeration | Bounded typed templates and fair increasing bounds answer relative coverage; no universal small/efficient grammar is established. | `sec:carrier-motives` | R2.N4 |
| R2.5 / R2.Q5: transfer of generalization | Structured failure proposals and conjecture–test–prove discipline are specified; reliability and proof-debt tradeoffs remain open. | `sec:carrier-motives`, `sec:carrier-experiments` | R2.N5 |

## Input-by-input integration

### N1

Sources: `new/1/sections/02-search.tex` and `03-carriers.tex`; topic coverage corroborated against `11-appendices.tex`.

- R1.Q1: interface-conditioned relations, transitive dependencies including universes/local values/delayed assignments, factorization proof, Aesop correction, non-snapshot external state and cache identity → `sec:search-factorization`, `prop:search-factorization`, `sec:search-experiments`.
- R1.Q2: shared assignment and zero-cost exact counterexamples, maximum versus cost-separated sum, abstraction proof and infinite zero-cost frontier → `sec:search-bounds`.
- R1.Q3: fixed description cost, epochs, queue rekeying, fairness, correlated-observation caution → `sec:search-learning`.
- R1.Q4: deadline proof, prefix replay, canonical parallel merge, limits of calibration and Luby assumptions → `sec:search-deadlines`.
- R2.Q1: residual quotient proof, infinite/undecidable quotient caveats, finite tables, incomplete-row graph bound, three-state modulo example → `sec:carrier-quotient`, `sec:carrier-finite`, `sec:carrier-lower-bounds`.
- R2.Q2: naturality via `Fin n`, repeated and empty inputs, nominal/register control versus payload, no unproved small-model theorem → `sec:carrier-parametricity`.
- R2.Q3: AutoLifter/Eguchi precedents, invariant initialization/preservation/finish, Fibonacci, continuation reversal, explicit defaults, finite feature vocabulary → `sec:carrier-lifting`, `sec:carrier-worked`.
- R2.Q4: typed telescope motive grammar, joint seed/observer/invariant obligations, outermost recursion as a tier and Para precedent → `sec:carrier-motives`, `sec:carrier-lifting`.
- R2.Q5: changing accumulators, tupling, recurring features and typed helpers, proof failure is not refutation, three benchmark tracks → `sec:carrier-motives`, `sec:carrier-experiments`.

### N2

Source: `new/2/Leant2_Expert_Answers/Leant2_Expert_Answers.tex`, R1 lines 264–402, R2 lines 404–723 at ingestion.

- R1.1–R1.4 merge into the common search answers. Distinct retained points: Canonical-min blockers, behavioral coupling despite independent types, lazy solution streams, canonical names/ties, grammar extension versus reordering, proof/dictionary-free abstract actions → `sec:search-factorization`, `sec:search-bounds`, `sec:search-learning`.
- R2.1: all-seed count formula; finite sample machine via reversed-word trie; greedy coloring gives an upper bound; four-state nine-word witness; direct-tail versus general-finisher counterexample → `sec:carrier-finite`, `sec:carrier-lower-bounds`.
- R2.2: lifted finite position types for higher universes, empty types, non-natural classical subsingleton family → `sec:carrier-parametricity`.
- R2.3: weighted collision cover, backtracking feature choices, update closure, explicit reversal cost summation/invariant → `sec:carrier-lifting`, `sec:carrier-reverse`.
- R2.4: dependent arrows and Sigma summaries versus ordinary arrows/products → `sec:carrier-motives`.
- R2.5: shared schema service, actual failure environments, bounded features and invariant proof → `sec:carrier-motives`.

### N3

Sources: `new/3/leant2-expert-answers/sections/02-search.tex` and `03-carriers.tex`; `11-appendices.tex` repeats the topic map.

- R1.1–R1.4: effect confinement and future joins, retained frontier memory, guarded contextual solution families, abstraction proof including fractional covering, inconsistent-heuristic reopening, enlarged grammar metadata, deterministic checkpoint comparison → common search labels, especially `sec:search-bounds` and `sec:search-experiments`.
- R2.1: optimize all four package components, identity-fold degeneracy, table-to-term distinction, Option Bool for a three-state result and exact reversal correction → `sec:carrier-package`, `sec:carrier-finite`, `sec:carrier-lower-bounds`, `sec:carrier-reverse`.
- R2.2: container/shape position maps, Mulleners–Jeuring–Heeren precedent, equality dictionaries, length threshold counterexample → `sec:carrier-parametricity`.
- R2.3: feature collision refinement and polynomial functor constructor algebras using all recursive children → `sec:carrier-lifting`.
- R2.4–R2.5: dependency-closed motive family, nesting bounds, Fibonacci, typed anti-unification and a program/proof strengthening service → `sec:carrier-motives`, `sec:carrier-worked`.

### N4

Source: `new/4/leant2_expert_answers/leant2_expert_answers.tex`, R1 lines 327–512, R2 lines 514–803 at ingestion.

- R1.1: explicit read/write frame inequalities and proof, unknown effects, guarded memo family → `sec:search-factorization`.
- R1.2–R1.4: final objective versus transition costs, complete frontier stopping inequality, deterministic integer/rational update option, interactive/replay services → `sec:search-bounds`, `sec:search-learning`, `sec:search-deadlines`.
- R2.1: forbid major-input capture; Unit-carrier degeneracy; type universe/context policy; emitted table separate from grammar realization; parity and modulo table variants → `sec:carrier-package`, `sec:carrier-finite`, `sec:carrier-lower-bounds`.
- R2.2: finite tests versus a monomorphic-testing theorem, bounded-length identity/cutoff example → `sec:carrier-parametricity`.
- R2.3: full-specification fusion needs reachable-state or invariant coverage; constructive Weber/Caldwell antecedent; finite algebra and homomorphism boundaries → `sec:carrier-lifting`, `sec:carrier-prefix-sum`.
- R2.4: complete nondependent primitive-recursive schema via full function result type, syntax-size cap not a theorem, separately charged nesting/numerals → `sec:carrier-motives`.
- R2.5: isolated dependency-closed generalization, Canonical supplied-rule versus rule-discovery distinction → `sec:carrier-motives`.

### N5

Sources: `new/5/leant2_expert_answers/sections/03_search.tex`, `04_carriers.tex`, and model/obligation details in `13_appendices.tex`.

- R1.Q1: dynamic components split as well as merge, union–find limitation; shared resource/provider limits; cost-indexed streams and incremental rollout → `sec:search-factorization`, `sec:search-experiments`.
- R1.Q2–R1.Q4: normalization versus positive structural grade, inconsistent heuristic reopening, work/objective/priority separation, grace time not optimality, three timed resumptions not one logical continuation, external versus in-process snapshot regimes → common search answers.
- R2.Q1: exact quotient proof, finite-cardinality versus infinite set-theory boundary, nontransitive partial rows, fixed-seed four-state experiment counts → `sec:carrier-quotient`, `sec:carrier-finite`, `sec:carrier-lower-bounds`.
- R2.Q2: subsingleton counterexample to surface-type parametricity, finite equality partitions, symbolic payload not finite carrier → `sec:carrier-parametricity`.
- R2.Q3: Fibonacci, continuation invariant and cost assumptions, alternative left-fold scheme → `sec:carrier-worked`.
- R2.Q4: joint motive/carrier/term/scheme grade and explicit later tiers → `sec:carrier-motives`.
- R2.Q5: Hipster's conjecture/test/prove precedent, typed anti-unification, bounded rippling metadata and extra proof-debt measurement → `sec:carrier-motives`, `sec:carrier-experiments`.
- Appendix four-state sample uses all 15 short words, unlike the minimal nine-word table; fixed-seed table counts 2/64/5832 are retained as a distinct convention. No historical receipt is relabeled or combined with another package's witness-test range.

### N6

Source: `new/6/leant2_expert_answers.tex`, R1 lines 205–370, R2 lines 372–677 at ingestion.

- R1.1–R1.4: fixed separator, conditional commutation, shared-hole term duplication versus erased syntax, held-out quality versus training observations, deterministic ledger/checkpoint identity → common search answers.
- R2.1: unobserved-word counterexample to intended minimal state; bounded exhaustive proof; exhausted versus resolved distinction → `sec:carrier-quotient`, `sec:carrier-finite`.
- R2.2: provider observation/effect classes, index/fiber-aware tokens → `sec:carrier-parametricity`.
- R2.3: **constructive section-based fold theorem with proof**, polynomial-functor analogue, explicit finite transition/output constraints, actual finite invariant capacity → `prop:carrier-section-fold`, `sec:carrier-lifting`, `sec:carrier-finite`, `sec:carrier-lower-bounds`.
- R2.4: dependent carriers and joint initialization, Option A insufficiency assumption for arbitrary left association, beam/top-k is incomplete without fallback → `sec:carrier-package`, `sec:carrier-motives`.
- R2.5: HipSpec, typed failure record and closure of both strengthened components → `sec:carrier-motives`, `sec:carrier-lifting`.

### N7

Source: `new/7/Leant2_Expert_Questions/article.tex`, R1 lines 195–275, R2 lines 277–446 at ingestion.

- R1.1–R1.4: independent replay frame, actual final ranking versus rule-cost A*, perturbation tests, bounded services/worker cancellation and restart-versus-resume measurement → common search answers and `sec:search-experiments`.
- R2.1–R2.2: finite graph proof, nine-word K4 and all-seed counts, input positions with empty type, lawful equality partitions → `sec:carrier-lower-bounds`, `sec:carrier-parametricity`.
- R2.3: **weighted feature set cover followed by update closure**, induction proof, closure-distinction refinement and retention of alternative feature sets; general initial-algebra equation → `sec:carrier-lifting`, `eq:carrier-feature-closure`.
- R2.4: motive, parameter generalization and result strengthening as distinct grammars, proof-justified deduplication → `sec:carrier-motives`.
- R2.5: program/proof two-level loop; changing accumulator versus missing reassociation lemma; no established turnkey Lean HipSpec/rippling component → `sec:carrier-motives`.

### N8

Source: `new/8/leant2_expert_answers/article.tex`, R1 lines 142–207, R2 lines 209–325 at ingestion.

- R1.1–R1.4: interface relations, explicit cache policy fields, minimum-cost/LP cover relaxation, objective/preference/admissibility distinctions, checkpoint contents and reserve for final checking → common search answers.
- R2.1: **prescribed carrier X and empty-list Unit observation reduces to closed inhabitation of X** → `sec:carrier-finite`; separate efficient-carrier track → `sec:carrier-experiments`.
- Evaluation section's distinct worked **minimum four-state machine overfits length exactly two, then refines after the length-six counterexample**, with the reached-state invariant `min(n,3)` → `sec:carrier-minimum-overfit`. This constructive counterexample is retained in addition to the general finite-sample nonidentifiability argument.
- R2.2: tagged multiple-input positions and sharing, index/witness-preserving renaming, transition caching requires equivariance → `sec:carrier-parametricity`.
- R2.3: **H = pair(h,b) and H ∘ in = alpha ∘ F(H)**, invariant proof architecture, reference-counterexample versus sparse-example distinctions → `sec:carrier-lifting`.
- R2.4: product grammar axes and diagonal bounds, preserve successful T→T priority, subtree cost rather than type count → `sec:carrier-motives`, `sec:carrier-experiments`.
- R2.5: failed-proof feature vocabulary, supplied generalized principle versus discovering one, preserve old branch → `sec:carrier-motives`.

### N9

Source: `new/9/leant2-expert-answers.tex`, R1 lines 240–417, R2 lines 419–770 at ingestion.

- R1.Q1–R1.Q4: three reuse levels, union of products over separator assignments, rule/provider read sets, objective versus failed work, all-production abstraction obligation, fair baseline prerequisites and controlled event stream → common search answers.
- R2.Q1: **finite sample construction with at most suffix-count+1 states and bounded minimization proof**, fixed-seed formula, unrestricted finisher inhabitation reduction, unary modulo enumeration → `thm:carrier-finite-machine`, `sec:carrier-finite`, `sec:carrier-lower-bounds`.
- R2.Q2: **general container shape–position theorem and proof**, tagged multiple inputs, maps preserving dictionary observations → `thm:carrier-containers`, `sec:carrier-parametricity`.
- R2.Q3: Synduce caveat and concatenation lifting; **maximum-prefix-sum scalar right fold versus paired segment homomorphism**, lost-information example, associative operation, reachable invariant, restricted identity and its counterexample with full derivation → `sec:carrier-lifting`, `sec:carrier-prefix-sum`, `prop:carrier-prefix-monoid`.
- R2.Q4–R2.Q5: joint finishing/motive obligations, active recursion frame limits, consumers backtrack when guessed helper fails, structured failures rather than tactic strings → `sec:carrier-motives`.

## Deduplication, corrections and boundaries

- Nine versions of the component factorization proof, abstract-cost bound and deadline obstruction are consolidated into one argument each, retaining the strongest explicit hypotheses (future effect confinement, all-rule cost simulation and progress-sensitive publication).
- The direct-fold characterization and the general hidden-carrier quotient are kept distinct. No semantic impossibility is inferred from missing append or a shallow step grammar. The list-tail counterexample shows why adding a finisher changes the existence problem.
- The original statement that a shallow enumeration's discovered values bound a type's capacity is rejected. Only actual finite capacity or a proved invariant bounds possible reachable states.
- The original claim that auxiliary-state synthesis has no relevant literature is withdrawn. AutoLifter and the additional precedents have their actual stronger inputs and incomplete/fragment-specific guarantees stated; none is presented as a turnkey Lean solution.
- Reversal's ordinary list fold, continuation fold and left-fold alternative are retained as different expressibility/cost choices. The original R2 table's ambiguous `foldl1`/`reduce` grouping is replaced by explicit left/right association and optional-state versus continuation distinctions.
- Incoming finite table counts use different alphabets, initial-state labeling, sample sets and witness-test depths. Both count conventions and both minimum-nine-word/extended-fifteen-word K4 samples are described. Evidence receipts must remain separate; no synthetic aggregate native or performance result is claimed.
- A generic finite machine may be emitted as Fin k when the allowed fragment supplies enumeration/equality, but this does not imply that an arbitrary Lean carrier grammar or body bound admits the same machine.
- The syntactic and semantic questions are not silently unified: finite grammar exhaustion with total checks, heuristic proof timeout, universal contract proof, current implementation behavior, and compiled publication remain different claims.
- Existing useful historical designs remain as proposals: local/constructor/provider/split/recursion/accumulator weights, fail-first goal ordering, a bottom-up component lane, T→T priority, and the ten-second/factor-two Church evaluation target. No claim of present implementation success is made from the imported reports.
- Existing unified proposal 10 already covers joint snapshots, fair reference lanes, dependent motives, invariants and recursion acceptance. These sections refine its assumptions and provide the detailed incoming derivations; common completion/evidence semantics are referenced through `sec:semantic-boundaries` rather than reproduced as a separate foundation.

## Active new expert questions

The canonical wording appears once: R1.N1–R1.N4 in `sections/05-search.tex` at
`sec:search-new-questions`, and R2.N1–R2.N5 in `sections/06-carriers.tex` at
`sec:carrier-experiments`. The historical map above preserves each disposition
and its new question ID. The central expert agenda prioritizes these IDs
without maintaining another copy of their full wording.

## Integration verification and handoff

The owner checked the R1/R2 bodies in all nine source packages and the existing canonical 05/06 and unified-proposal search/recursion sections. All old `sec:search` and `sec:carriers` labels are retained. The initial R1/R2 edit stage changed only 05, 06 and this ledger; the subsequent authorized consistency repairs to 03/04 and global review are recorded in `global-review.md`. `git diff --check` on the owned section files passes. A read-only Python structural check also passed balanced braces/environments, uniqueness of every owned label across section files, resolution of every owned `ref`/`eqref`, and exactly four R1.N plus five R2.N active questions. Root owns bibliography completion, central source/evidence mapping, TeX compilation, PDF visual review, deletion of integrated incoming directories and publication.

New literature is linked with the bibliography keys agreed with root: `canonicalmin`, `angluin`, `autolifter`, `weber`, `containers`, `eguchi`, `para`, `hipspec`, `hipster`, and `synduce`. Supplied-source pointers `snapshot`, `nominal`, `inductiongeneralization`, and `anytime` preserve distinct contextual precedents identified by the retirement audit. Root supplies those bibliography entries. Nominal/register automata are mentioned as a possible model, without claiming an existing Lean implementation. Existing citation keys are retained for the earlier literature. These supplied citations were not independently reverified against external publications in this integration pass.
