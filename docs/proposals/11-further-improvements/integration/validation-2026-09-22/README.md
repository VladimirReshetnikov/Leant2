# Completed proposal integration and validation

The nine expert-answer packages are integrated and their incoming directories
are deleted. The integration was published as
`29b796df2610e8222c23ea1bc065301a63ff95f1`, after merging the latest
`origin/main` and verifying a fast-forward push to that exact remote SHA.
This validation record is a subsequent documentation-only publication.

The [machine-readable receipt](receipt.json) records exact PDF identities,
all 35 TeX source inputs, normalized Git blob identities, final build logs,
review coverage and the evidence boundaries. The
[documentation check](documentation-check.json) is reproducible with
`python -B tools/check_proposal_docs.py --require-retired` from the repository
root.

| Requirement | Completed result |
| --- | --- |
| Integrate all incoming proposals | N1–N9 mapped through the three topic ledgers and the global review; all 279 answer instances to the 31 original questions are accounted for |
| Preserve distinct contributions and remove repeated explanations | One shared semantic boundary, canonical topic sections, one roadmap, and 82 bibliography entries; all 129 incoming bibliography keys have a canonical destination, alias or explicit disposition |
| Retire completed directories | All 97 original files are inventoried; no `docs/proposals/new/` directory remains; original Git blobs remain recoverable |
| Preserve executable evidence | All 28 preserved files match their original Git blobs byte-for-byte |
| Replace answered questions | 33 unique new questions in their topic sections; central agenda references their IDs without duplicating their wording |
| Reconcile the architecture | Twenty material corrections recorded in the architecture consistency audit, preserving historical P1–P9 evidence |
| Regenerate and review artifacts | Three serial final TeX passes for each article; all 180 resulting pages rendered and visually reviewed |

The [improvement article](../../Leant2-next.pdf) has **77 pages** and SHA-256
`55bb3fde941895f8211b8e687d949768b9e54dfdadde289799594ff881adc5d8`.
The [architecture article](../../../10-unified-proposal/Leant2.pdf) has
**103 pages** and SHA-256
`9e00503269a584cbb9ea60de0a2da8a1f0c853e18d8f0c6067936744473d9502`.

Both final logs have zero overfull boxes, zero undefined references/citations,
and zero multiply-defined labels. Retained non-fatal notices are explicit:
25 architecture and five improvement underfull boxes, three architecture
longtable glue notices, the improvement article's `h` to `ht` float adjustment,
and the expected epstopdf notice while shell escape is disabled.
The exact final logs and all six pass console logs accompany the receipt.

Visual review covered every page in contact sheets, with additional full-page
inspection recorded in the receipt. It found and resolved appendix-table
overflow, a lone work-item continuation, an orphaned result heading, and a
recipe listing whose caption and frame were split from its code. The final
77-page improvement article was rerendered in full after these repairs and
all pages were reviewed again. Local intermediate logs and rendered images
remain under `baseline-out/proposal-doc-build-01/`; the tracked PDFs and this
receipt identify the final artifacts.

The [nine-suite Python rerun](../../evidence/rerun-2026-09-22/receipt.json)
passed before consolidation: every process exited zero with empty stderr,
decoded results matched the archived JSON, and the original evidence stayed
unchanged. The final documentation checker independently rechecks the original
Git inventory and exact preserved copies after retirement.

These results establish document integration, evidence preservation, successful
artifact builds and the recorded visual inspection. They do not establish a
new native Lean build, a Lean formalization of the mathematical arguments,
current API compatibility, engine performance, or exact-commit remote CI.
Historical measurements at `33cec8b` and selected source inspections at
`784664f` retain those revision boundaries. The P0–P5 plan and 33 new questions
describe remaining implementation and research work.
