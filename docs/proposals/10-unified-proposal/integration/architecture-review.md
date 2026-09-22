# Architecture proposal publication receipt

Verified on 2026-09-22. This receipt covers the corrected historical architecture article, not an implementation or performance result. The semantic correction map is in [the consistency audit](../integration-audit.md).

## Artifact and source identity

- Final article: [Leant2.pdf](../Leant2.pdf), 103 pages, 1,354,882 bytes.
- PDF SHA-256: `9e00503269a584cbb9ea60de0a2da8a1f0c853e18d8f0c6067936744473d9502`.
- TeX source-bundle SHA-256: `7b67bc2fd0c5e2477beea5fa224a1e208903e076b900ca89ddda12f5e57dc690`.
- Bundle definition: the SHA-256 of UTF-8 compact JSON containing the following path/hash objects in lexicographic path order, with object keys sorted and separators `,` and `:`. Paths are relative to this proposal directory; each hash covers the exact source bytes. Only the 16 TeX inputs are included, not this receipt or the README.

| TeX source | SHA-256 |
| --- | --- |
| `Leant2.tex` | `272280befab240700c3f1abd0f65662e2a4be85472ac33ef3260730a2a03c07c` |
| `sections/01-scope-baseline.tex` | `b6ad4f1c7a1d64715096cad61bb49c22336bc7cb0cf6a31e989a7c06a22ed55a` |
| `sections/02-decisions-problem.tex` | `1a954cc3e5f2ae8c212e64a28eea76e44f15cf3b756099718023d74d38f8ca3b` |
| `sections/03-state-search.tex` | `e4a4477883b05d1d81d7e0ff83982eb55b24908261d7afb4a81c3599647b54c3` |
| `sections/04-construction.tex` | `6d0f04dc4eca0891ab0a4d7f78b9c3d0f80a0c831ea8ba14d098ed8cda936ad6` |
| `sections/05-recursion.tex` | `2fa07a71393a31fc6fae4c0dd3d02afdc326ad3c8ec5e0592d3e61dca5e1ddc4` |
| `sections/06-behavior.tex` | `3c09981c040588ecccdcdadf49a4458c68d520dbba4ea5eb6e450a6d06d5dc14` |
| `sections/07-acceptance-deployment.tex` | `08a7e41b8d5fb6c06519c41a48af61322ff94ecf41a6d1085570e2c4c8e7e780` |
| `sections/08-evidence-evaluation-roadmap.tex` | `ea394134f9f5cf3416505dfac29b3f382a778712d46d76b52ca1356c092dc852` |
| `sections/09-appendices.tex` | `eeed958289461e4bcfdbe01d23fa9f4fb55032338122d37ae2c80385ea085bcb` |
| `sections/alg-acceptance.tex` | `1a90ae407c745cba9484d3256a688782d5019e6575313e03b013c0c1ef6791ae` |
| `sections/alg-behavior.tex` | `a2373c7337c750c32c6a1c21d075a7dfe38222b32726e9239fb2aebdd505463c` |
| `sections/alg-elim-retrieval.tex` | `fabe5cc7227eb30f50dc5510f8c7ee39543ec2a23af498ec75a760010a838448` |
| `sections/alg-recursion.tex` | `5e2dac4f66f8edbffc907e8c7536b4b34ead8799178297f31b08802d3d005305` |
| `sections/alg-scheduling.tex` | `9ae9c4cd5c9a7d8a3c5838e9123fde464affab6961bc3e86882eb5d97eb3fc46` |
| `sections/alg-search.tex` | `f8f266719947fda8b0c5c16cbf9586b4ba7cbd89b92bceac9ac7463933c3841b` |

## Build and static checks

- Three serial final `pdflatex` passes exited 0, using `-interaction=nonstopmode -halt-on-error -no-shell-escape` and an absolute output directory. The entire `-output-directory=...` argument was quoted in PowerShell.
- Output directory: `baseline-out/proposal-doc-build-01/architecture/` from the repository root. Final pass console/log receipts are `layout-pass-1` through `layout-pass-3`; the earlier `pass-1` through `pass-3` are the pre-layout-fix build and are not the final receipt.
- The generated PDF was copied to the linked tracked path only after the final visual review. Its hash matches the output-directory PDF.
- All 16 TeX files passed environment-balance, duplicate/missing label, missing citation, and control-character checks: 128 labels, 151 reference occurrences, and two bibliography citation keys. `git diff --check` passed for this proposal.
- Final log: zero overfull boxes, zero undefined references/citations, 25 underfull box notices, three ignored infinite-glue notices in longtable page splitting, and the expected epstopdf warning because shell escape is disabled. This is a successful build with retained non-fatal notices, not a warning-free build.

## Visual coverage

- Poppler rendered every final page at 80 DPI into `render-stable/page-001.png` through `page-103.png`. PDF hashes captured immediately before and after rendering are identical to the final hash above.
- All 103 pages were inspected in nine 12-page contact sheets in `contacts-stable/` (the last contains seven pages).
- Full-page images were additionally inspected for pages 1, 16, 45, 53, 62, 63, 76, 77, 81, 84, 85, 86, 97, 98, 99, and 100, covering the front-matter clarification, changed algorithms, and appendix tables.
- No clipping, overlapping text, missing glyphs, or broken tables was visible at those review scales. The original appendix table widths caused six small overfull notices; slightly narrower final columns and removal of redundant center wrappers eliminated them. The original document style, numbering, and historical title date were preserved.
- `verification-receipt.json`, stable-render hash receipts, extracted text/page map, logs, and renders remain under the output directory. Earlier render folders are intermediate artifacts and are not the final visual receipt.

## Evidence boundary

These checks establish source consistency, successful TeX generation, and the recorded visual review. They do not compile the pseudocode as Lean, prove evaluator correspondence or retrieval completeness, validate a running proof service, repeat historical prototype experiments, or establish performance. Those obligations remain in the maintained proposal and its independent evidence ledger. No commit or push was performed by the architecture-audit worker.
