# Leant2: a unified architecture proposal

`Leant2.tex` consolidates the nine independent proposals in the sibling
directories `01-` to `09-` into one design. `Leant2.pdf` is the compiled
article. This preserves the architecture synthesis of proposals 01–09.
The [maintained further-improvements proposal](../11-further-improvements/README.md)
integrates later expert answers and supplies the current detailed obligations
and research agenda. Corrections here reconcile material semantic claims
without relabeling the original evidence as current implementation evidence.
See [the consistency audit](integration-audit.md) for the correction map.

Part I (architecture) keeps the consensus of all nine as its core (exact Lean
expressions as semantic authority; whole-continuation backtracking; recursion
through typed schemas with call capabilities; graded behavioral authority; one
kernel-checked acceptance gate; qualified negatives; a non-refundable work
ledger), selects the best-developed treatment where the proposals differ, and
marks each idea with the proposals it comes from. Appendix A is the provenance
ledger.

Part II (algorithms, `sections/alg-*.tex`) gives the procedures as pseudocode
merged from the best-specified proposals, with the worked traces that recur
across them: the construction search and spine expansion; dependent
elimination, transport, retrieval, and carrier invention; recursion-schema and
motive synthesis, invariants, measures, and executable lowering; contract
propagation, certified counterexample-guided refinement, and certified
pruning; scheduling, memoization, and the completeness statements; proof
services, the constructive propositional lane, and the acceptance gate.

Part III covers evidence, evaluation, and the roadmap.

Two requirements come from the project owner rather than from the proposals:

- Leant2 has a single adaptive engine, with no engine switches and no
  user-facing settings at first.
- The minimal acceptance baseline is the Leant `:synth` golden corpus
  (`C:\Leant\test\synth-*.txt`, 30 transcripts, 278 queries), read
  semantically: match or exceed every recorded outcome; more or better
  candidates in a different order are allowed. Section 1.3 and Appendix B
  define this.

The article also records what to reuse from the sibling project Forge
(`C:\Forge`): its orchestration frontend with full rollback and proof-term
audit, its certificate checkers with proved soundness, its Kripke-countermodel
certificate for intuitionistic non-derivability, and two documented kernel
pitfalls (`debug.skipKernelTC`, asynchronous `addDecl`).

No new experiments were run for this synthesis or its consistency corrections.
The evidence section describes the original nine prototypes at their recorded
revisions, not the current implementation status. The corrected PDF was rebuilt
and visually reviewed; the [publication receipt](integration/architecture-review.md)
records its exact source identity and coverage separately from implementation evidence.

## Build

```sh
pdflatex -interaction=nonstopmode -halt-on-error Leant2.tex
pdflatex -interaction=nonstopmode -halt-on-error Leant2.tex
pdflatex -interaction=nonstopmode -halt-on-error Leant2.tex
```

A standard TeX installation with Latin Modern, TikZ, listings, booktabs,
longtable, and hyperref suffices. The bibliography is inline; no BibTeX run is
needed. Section sources are under `sections/`.
