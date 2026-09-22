# Leant2: design for further improvements

The maintained [77-page article](Leant2-next.pdf), built from
[Leant2-next.tex](Leant2-next.tex), integrates the nine expert-answer packages
formerly under `docs/proposals/new/` into one design. These N1–N9 responses
are distinct from the original architecture proposals P1–P9 in directories
`01-` through `09-`.

The responses addressed the same **31 original questions**. Their answers
now appear once in the relevant topic sections, preserving distinct
constructions, counterexamples, assumptions and evidence. The answered
questions have been replaced by **33 narrower questions**, whose full wording
appears only in their topic sections. The final expert agenda sets priorities
and preparation tasks by question ID.

- **Part I:** historical measurements at `33cec8b`, constraints and a shared
  semantic boundary separating certification, conservative pruning, bounded
  coverage, ranking, replay and executable publication.
- **Part II:** engineering and adaptation work, corrected where the responses
  exposed compiler, contextual-refutation, determinism and parametricity
  qualifications.
- **Part III:** integrated answers on coupled search, carriers, partial
  evaluation, dependent motives, recursive realization, proof obligations,
  retrieval, ranking and learned proposals; the remaining research questions
  are explicit.
- **Part IV:** a dependency-ordered P0–P5 roadmap, acceptance and ablation
  protocols, a focused expert agenda, and integration provenance.

This is a design document. The original engine profile belongs to `33cec8b`;
selected source audits in the incoming responses belong to `784664f`.
Neither is presented as a fresh measurement of the current engine. The
mathematical arguments have not been formalized in Lean by this integration.
Pinned source references and moving manual pages retain their distinct
version boundaries; bibliography consolidation uses the supplied responses,
without claiming a fresh external verification of every bibliographic fact.

## Integration and preserved evidence

- [Source inventory](integration/sources.json): all **97 original files**,
  original Git blobs and hashes, destinations and dispositions, pinned to
  `5c3a53c22c18e6acd8ff17eb0902ce4da354518a`.
- [Search and carrier coverage](integration/search-carriers.md): R1–R2.
- [Evaluation, dependent types and recursion coverage](integration/evaluation-recursion.md): R3–R5.
- [Contracts, retrieval, ranking and guidance coverage](integration/contracts-guidance.md): R6–R9.
- [Global consistency review](integration/global-review.md): foundations,
  engineering/adaptation corrections, the common roadmap and evaluation plan.
- [Package retirement audit](integration/retirement.md): complete file,
  checksum, bibliography and packaging dispositions for N1–N9.
- [Bibliography provenance](integration/bibliography.json): canonical choices
  and aliases for references consolidated from the responses.
- [Preserved evidence](evidence/README.md): **28 original files**, including
  all nine executable model suites and their historical results/provenance.
- [Model rerun receipt](evidence/rerun-2026-09-22/receipt.json): all nine suites
  passed in fresh copies; each decoded JSON result matched its archived
  result, every process exited zero with empty stderr, and original evidence
  remained unchanged. Raw process streams accompany the receipt.

Original articles, PDFs and package instructions remain recoverable from the
pinned Git revision. Their repeated prose and standalone build instructions
are superseded by this maintained article. Historical paths in provenance
ledgers identify retired sources; they are not active reading links.
Historical source manifests and checksum reports describe the original
packages and must not be used to validate this consolidated PDF.

The Python suites exercise finite constructions and countermodels. They do
not execute Lean or Leant2, certify general conservativity, or establish new
synthesis coverage or speedups.

## Reproduction

From the repository root, run the documentation checks and model suites:

```powershell
python -B tools/check_proposal_docs.py --require-retired
python -B tools/check_proposal_models.py --out baseline-out/proposal-models
```

The model output directory must be new. Use ordinary Python, without `-O`,
because the suites use assertions. The documentation checker validates
references, citations, local Markdown links, question IDs, the original Git
inventory and byte-for-byte evidence preservation. It is not a proof checker.

Build the article in this directory with MiKTeX or TeX Live, running the
following command **three times serially**:

```powershell
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape Leant2-next.tex
```

Inspect the final log for errors, undefined references/citations and overflow,
then render the resulting PDF and review every page. A successful TeX process
alone does not establish legible layout. The architecture article in
`../10-unified-proposal/` has its own build and must be regenerated whenever
its source changes.
