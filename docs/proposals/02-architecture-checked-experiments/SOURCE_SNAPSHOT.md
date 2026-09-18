# Source snapshot and evidence scope

Inspection date: September 17, 2026.

| Source | Revision |
| --- | --- |
| Leant default branch | `6bf05ad78c467989e68290f2d08bbed40802d485` |
| Djex default branch | `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5` |
| Djex submodule actually pinned by the inspected Leant | `e237e8667190aff38faaa590ce5b12afbffac452` |
| Lean source/API reference for checked prototype | `v4.34.0` |
| Actual remote experiment environment | `lean-4.34.0` |

The two Djex revisions are intentionally different. The article does not treat
current Djex documentation and Leant’s pinned engine as one identical checkout.
The exact submodule reference was read independently from the GitHub contents API.

Repository reads through the GitHub connector included the root READMEs, current
architecture/internals documentation, the behavioral-synthesis contract, the
fragment translator’s source header and datatype, the prior Lean-rewrite analysis,
repository commit metadata, and the relevant directory inventories. In particular:

- Leant: `README.md`, `docs/synth-internals.md`,
  `docs/behavioral-synthesis.md`, `src/Leant/Synth/Fragment.hs`, and
  `docs/Leant_Djex_Lean4_Rewrite_Analysis/Leant_Djex_Lean4_Rewrite_Analysis.tex`.
- Djex: `README.md` and `docs/architecture.md`.
- Lean 4.34.0: `src/Lean/Meta/Tactic/Assumption.lean`, including its exclusion of
  implementation-detail local declarations.

This was targeted architectural inspection, not a complete line-by-line code
review. Existing Leant/Djex suites were not rebuilt or rerun. Their historical
acceptance counts are not used as new measurements in this package. The original
compound integer-indexing and two-universe search gaps are not claimed solved by
the small Leant2 experiments.

Primary sources for Lean’s type system and recursive definitions, Aesop,
polymorphic refinement synthesis, hole refinements, Lean-SMT, and AXLE are cited
in the article’s bibliography. The online “latest” Lean manual reported
4.35.0-rc2; that is not the runtime used for these experiments. The checks used
the independently reported Lean 4.34.0 environment.

The uploaded tool archive was inspected for its AXLE submission clients. The
actual remote submissions used the Wolfram connector and UTF-8 JSON HTTP requests.
The new Python reproduction runner is supplied in this package, with separately
executed synthetic-response audit tests.
