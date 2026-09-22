# Incoming-package retirement audit

This is the independent metadata, source-inventory, evidence, bibliography,
and package-instruction audit for N1-N9. It complements the topic ledgers and
global-review.md; it does not replace semantic integration review, the final
maintained-document build, rendered-page review, or publication checks.

## Authoritative inventory and independent checks

The authoritative input list is sources.json at original revision
5c3a53c22c18e6acd8ff17eb0902ce4da354518a. On 2026-09-22, the audit read all
97 recorded Git blobs with git cat-file and independently checked every
recorded byte count and SHA-256. All 28 preserved evidence destinations were
compared byte-for-byte with their original Git blobs. All still-present
incoming checkout files also matched their separately recorded checkout
hashes. There were no missing blobs, mismatched copies, or unrecorded edits.

Git line-ending conversion explains differences between blob bytes and
checkout bytes for text inputs. The preserved evidence uses original blob
bytes; it must not be normalized or judged against checkout-byte hashes.

| Package | Original files | Integrated TeX | Preserved evidence | Superseded PDF | Superseded README/build files |
|---|---:|---:|---:|---:|---:|
| N1 | 18 | 13 | 3 | 1 | 1 |
| N2 | 7 | 1 | 3 | 1 | 2 |
| N3 | 17 | 13 | 2 | 1 | 1 |
| N4 | 6 | 1 | 3 | 1 | 1 |
| N5 | 22 | 15 | 4 | 1 | 2 |
| N6 | 7 | 1 | 4 | 1 | 1 |
| N7 | 8 | 1 | 4 | 1 | 2 |
| N8 | 6 | 1 | 2 | 1 | 2 |
| N9 | 6 | 1 | 3 | 1 | 1 |
| **Total** | **97** | **47** | **28** | **9** | **13** |

Every file has an individual path, blob, hash, and disposition in sources.json.
The table groups those complete individual records; it is not a replacement
inventory.

## Per-package metadata and evidence disposition

All packages have passed this metadata/evidence audit. Their overall retirement
also depends on the topic and global prose reviews plus the final document
gates described below.

| Package | Retained files under evidence/package | Specific interpretation and retirement disposition |
|---|---|---|
| N1 | checks/check_models.py; checks/results.json; provenance.json | Preserve 31-question scope, inspected repository 784664f, historical measured 33cec8b, Lean 4.34 versus moving-manual version, 11 model checks and original PDF metadata. README build/package instructions are superseded; source bibliography and appendices map to the maintained foundations, topic ledgers, roadmap and source inventory. |
| N2 | experiments/check_claims.py; experiments/results.json; source_manifest.json | Manifest retains source paths, 31-question map, 34-page original PDF/23 references, source-only Lean inspection, and no compiler available. Original POSIX build script/README target the retired article. Model enumeration includes all seeds and is not conflated with seed-fixed experiments. |
| N3 | validate_models.py; model_results.json | No separate manifest was supplied. Original README/article contain the pinned review and no-Lean boundary; those originals remain recoverable by blob. Six model families remain executable evidence, including actual cache reuse and wrong approximation direction. Sectioned appendices/index are integrated via topic/evidence ledgers. |
| N4 | experiments/model_checks.py; experiments/results.json; source_manifest.json | Preserve original 38-page metadata, 31-question mapping, inspected native APIs and explicit unperformed work. Eight Python families are models, not reproduced engine bugs/timings. Original PDF render/overflow statements do not certify the maintained PDF. |
| N5 | checks/check_design_examples.py; checks/results.json; provenance.json; SHA256SUMS | Original checksum file independently matches all 21 listed Git blobs. It is valid for the original package, not the new directories or maintained article. Preserve 15-observation / 5,898-table experiment scope and no compiled Lean claim. Original shell build and font choices are superseded. |
| N6 | semantic_checks.py; semantic_results.json; SHA256SUMS.txt; source_manifest.json | Original checksums independently match all 6 listed blobs. Preserve 37-page original report/eight semantic groups, explicit lack of Lean and accuracy runs, native API paths and literature URLs. N6's refusal to confirm sauto defaults remains distinguished from other reports' documentation evidence. |
| N7 | question_index.json; sanity_checks.py; sanity_results.json; source_manifest.json | The 31-entry JSON retains original printed page numbers and immutable old source links, not maintained-document pagination. Preserve 42-page original metadata and finite enumeration/feature/call-consistency checks. Original source/appendix index becomes historical provenance while new active questions live in canonical sections. |
| N8 | model_checks.py; model_checks.json | No separate manifest supplied. Original README preserves inspected Engine/Gate/toolchain and no-Lean scope. Explicit model checks remain active under Python -O, but the common runner correctly avoids -O for other suites. The two successive finite-state machines and counterexample-refinement ledgers are both retained. Makefile/README are superseded packaging. |
| N9 | experiments/check_constructions.py; experiments/results.json; validation.json | Validation PDF and TeX SHA-256 values independently match the original Git blobs. Its 35-page/31-reference/31-question and pixel-matched original-PDF claims remain historical. It does not validate the consolidated article. Preserve reverse/unary-machine/prefix-summary models and no new Lean/performance claim. |

The original reports all concern the inspected repository snapshot 784664f and
Lean 4.34 source; historical benchmark figures are separately attributed to
33cec8b where reported. Moving manual pages, sometimes observed at 4.35.0-rc2,
are not silently treated as pinned 4.34 implementation evidence.

README statements that source snippets are pseudocode, paper proofs are not
Lean formalizations, model experiments are not Leant2 benchmarks, and PDF
regeneration can change bytes are preserved in the maintained evidence/semantic
boundary. Original page counts and font/build choices are archival metadata,
not design content requiring nine competing build trees. No source package
redistributes external research papers or fonts.

## Bibliography retirement

The maintained bibliography contains **82 unique keyed entries** after the
retirement pass. The source map in bibliography.json records the chosen
original path and key for every added or updated entry. An independent scan
of every incoming TeX bibliography found **zero unaccounted citation keys**:
each is now canonical, explicitly aliased, or given a source/metadata
disposition.

Twenty distinct references discovered by the retirement audit were retained:
names, snapshot, inductiongeneralization, nominal, leansearch, llmsynthesis,
pbeinteraction, rankingstudy, anytime, metareasoning, ranking, lean418, lean426,
leancompile, leandojov2, premisereadme, aesopreadme, leanvalidation,
librarysearch, and grind. Their bibliographic bodies were drawn from the
provided sources without changing author lists, titles, versions, or dated
access/verification claims.

Important distinctions:

- Incremental computation with names (2015) is distinct from Adapton (2014);
  both remain cited in the residual-cache discussion.
- Keep the Proof State Live is a state-snapshot precedent, not proof of the
  proposed Leant2 scheduler's semantics or cost.
- Induction with Generalization and nominal automata remain bounded external
  precedents; no automatic transfer of completeness is implied.
- LeanSearch and adjacent LLM-synthesis papers remain retrieval/model study
  precedents, not a carrier-invention accuracy estimate.
- Three ranking/PBE studies and anytime/metareasoning references retain their
  separate objectives and experimental settings.
- Lean 4.18/4.26 release notes and the 4.27 recursion note are version-history
  evidence; callable adapters still require the pinned toolchain tests.
- LibrarySearch implementation and LibrarySuggestions/Basic interface are
  distinct source files and have separate entries.
- The project premise-selection README is consolidated from N6/N8 with N6's
  inspected blob retained. Privacy, cache/runtime, and cold-start observations
  remain source-bound rather than current service guarantees.
- LeanDojo-v2 is retained as historical tooling-navigation metadata, not a new
  synthesis algorithm or a current migration instruction.
- Repeated project self-citations (Engine, Gate, Core, Transaction, toolchain,
  proposal topic files and historical evidence) are consolidated by frozen
  source inventory and preserved manifests rather than dozens of identical
  bibliography entries.
- Textbook addition examples and a rolling-manual introduction are given
  explicit dispositions; their facts and version caveats remain, while the
  pinned Nat source and relevant official manuals are the canonical technical
  citations.
- Different source keys for the same paper/API are aliases, not additional
  discoveries. Alias consolidation does not promote a rolling document to a
  pinned implementation claim; the original source manifest remains available.

The historical source bibliographies themselves are recoverable at their
pinned Git blobs. No source-only citation identity is silently lost merely
because its old key is absent from the maintained TeX.

## Semantic coverage and remaining gates

Topic integration is recorded separately:

- search-carriers.md: all 81 R1/R2 incoming question instances;
- evaluation-recursion.md: all 99 R3/R4/R5 instances;
- contracts-guidance.md: remaining R6-R9 instances;
- global-review.md: executive/foundations, architecture, roadmap/evaluation,
  conclusions, and original engineering/adaptation consistency.

The metadata audit found no remaining source-file, checksum, evidence-copy,
README/build-instruction, or bibliographic-accounting omission.
It does not itself assert that the task is finished. Before deleting packages,
root must finish the global semantic review and ensure no topic-specific
omission remains. After final edits, rebuild the maintained PDF, resolve
references/citations/layout issues, inspect the rendered result, validate
crosswalks/evidence, and publish the integrated sources/artifacts and incoming
directory deletions. Retired PDFs remain recoverable at their pinned revision;
they need not remain competing current deliverables.

This worker performed no directory deletion, no document build, and no Git
publication. The byte/hash findings above are verified current-state results;
original report claims remain explicitly historical.
