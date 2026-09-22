# Baseline runs

Records of `tools/run_baseline.py` over Leant's `:synth` golden corpus
(`C:\Leant\test\synth-*.txt` at Leant revision `6bf05ad`), scored by outcome
category per the unified proposal's Definition 1.5. Each run names the Leant2
commit it was produced from and the per-query budget.

| Date | Commit | Budget | Score |
| --- | --- | --- | --- |
| 2026-09-17 | `f197fe0` | 10 s/query | 278/278 |
| 2026-09-17 | `56c307d` | 10 s/query | 278/278 (ranked candidates) |
| 2026-09-17 | `c8caa68` | 10 s/query | 278/278 (kernel-evaluated contracts; Church probes 21/21, recursive 9/9) |
| 2026-09-18 | `9fc3b91` | 10 s/query | 278/278 (upfront contract refutation; context harness 67/67) |
| 2026-09-18 | `0f67c4e` | 10 s/query | 278/278 (grace cuts passes, free leaves; context 90/90, Church 28/28, corpus 350/350) |

The `.log` file lists per-fixture scores and any failures; the `summary.json`
file lists every query with its golden and observed categories.

## P1 implementation checkpoint

The [2026-09-21 checkpoint](p1-2026-09-21/README.md) validates implementation
commit `87ed037` at both 10 s and 5 s per query: **787/787 scored
cases** in all seven harnesses at each budget. It includes the new 29-session
extended suite (21 required capabilities/controls, eight open searches),
complete raw logs, and source/executable hashes. The eight extended open
searches and thirteen Church stretch searches were unsolved at that checkpoint. The checkpoint
also records the difference between baseline outcome scoring and execution
of ordinary commands or newly returned results.

## Dependent recursion and session results checkpoint

The [next 2026-09-21 checkpoint](induction-2026-09-21/README.md) validates
implementation commit `555236a` at both 10 s and 5 s per query:
**805/805 required checks across nine harnesses** at each budget. Predecessor,
powers of two, and indexed vector map are now required E8 cases, leaving five
open searches. Five independent recursion gates check universal equations and
execution; ten result sessions check refresh, rollback, evaluation, and undo.
The denominator includes overlapping goals tested at different boundaries.

The archive preserves both complete raw runs, a pre-run snapshot of source,
executable, compiled modules, and external inputs, and verified receipt/ZIP
hashes. All five remaining E8 searches and thirteen Church stretch searches
were unsolved at both budgets. The checkpoint distinguishes search coverage
from indexed executable-presentation coverage and documents the one remaining
ordinary-command type error in the legacy baseline.

## Local proofs and cancellation checkpoint

The [local-proof checkpoint](local-proofs-2026-09-21/README.md) validates
implementation commit `914680d` at both 10 s and 5 s per query:
**813/813 required checks across ten harnesses** at each budget. Fin and
order transitivity are required E8 cases, leaving three open searches.
Six separate gates exercise local arithmetic proofs, contradictions, a supplied
induction hypothesis, and certified rejection of a False contract.

The full Lean build also verifies isolated proof extraction/replay, native
cancellation rollback, deferred typeclass inputs, and classical specialization
of flexible query universes. Both complete raw runs, pre/post input snapshots,
all receipt and ZIP hashes, and the exact archive helper are preserved.
The three E8 open searches and thirteen Church stretch searches were
unsolved at that checkpoint. The denominator includes goals checked at different boundaries;
this is not a count of 813 distinct synthesis problems.

## Constructive guard checkpoint

The [constructive guard checkpoint](guards-2026-09-21/README.md) validates
implementation commit `ce31d3a` at both 10 s and 5 s per query:
**820/820 required checks across eleven harnesses** at each budget. Maximum
and drop-zero are now required E8 probes. Five independent public gates check
maximum, minimum, and drop-zero through universal post-checks and held-out
execution, plus two certified impossible-contract controls. Separate
empty-provider Lean fixtures verify native guarded recursion, executable
publication, and universal equivalence of reparsed printed source.

Both complete runs preserve the captured source, executable, compiled modules,
and external fixtures. Each retains 115 raw artifacts and 834 synthesis query
records across scored and unscored families; the aggregate score counts
acceptance gates, not distinct problems or total queries. Tree inorder and
the thirteen Church stretch searches remain bounded misses at this checkpoint.
The archive also preserves and independently checks the legacy baseline's
two intentional preflight diagnostics and one unscored Option-call error.

## Tree composition and closed-contract checkpoint

The [tree-composition checkpoint](tree-composition-2026-09-21/README.md) validates
implementation commit `313a441` at both 10 s and 5 s per query:
**824/824 required checks across twelve harnesses** at each budget. All 29
original E8 cases now pass as required checks. Three separate tree gates add
universal constructor equations and held-out execution for two binary datatypes,
plus certified rejection of a literal-False contract.

Public searches retain ordinary providers, including `List.append`. Native
tests separately establish composition-route permissions, transaction behavior,
and executable publication of a known recursor term. The archive preserves
117 raw artifacts and 837 synthesis query records per budget, with identical
pre/post source, executable, compiled-module, and external-fixture hashes.
The thirteen Church stretch cases remain unscored bounded misses. Prior
checkpoint archives are unchanged; score, total query count, and unique
benchmark count remain distinct quantities.

## Expected-type term and tactic checkpoint

The [frontend checkpoint](frontends-2026-09-21/README.md) validates implementation
commit `69221f1` at both 10 s and 5 s per search: **832/832 required checks
across 13 harnesses** at each budget. The added 8 frontend cases exercise
typed local data/proofs, delayed shared type constraints, genuine lets/instances,
and indexed Vec mapping. They require 13 fresh Lean processes: 8 original
stages, 3 independently replayed actual tactic suggestions in Lean-only files,
and 2 deliberate error stages for impossible goals. Those process counts are
separate from the 837 legacy synthesis-query records retained per budget.

Both full runs preserve the captured source, `leant2.exe`, native Lean, the
complete recorded compiled-module inventory, and external fixtures. Complete
raw outputs, exact suggestion text and replay sources, receipt/ZIP hashes, and
pre/post snapshots are preserved. The archive additionally reconstructs the
secondary harness inputs and independently checks raw outcome categories and
session provider histories. All 29 E8 cases remain required; Church stretches
remain unscored, with actual outcomes recorded separately. The five earlier
checkpoint archives are unchanged, with their original revisions and evidence
boundaries. Required checks are not a count of distinct synthesis problems.

## Isolated library API and certified refutation checkpoint

The [API checkpoint](library-api-2026-09-21/README.md) validates implementation
commit `9ec21c8`: **832/832 external checks across 13 harnesses at both 10 s
and 5 s per search**. The aggregate native build passes 68 jobs, including
the API and contract-refutation regression modules. Those native tests are
separate from the unchanged external-family denominator.

The API checks exported programs and proofs in the caller's original environment,
restores native state, and distinguishes malformed inputs, bounded misses,
certified negatives, and output-validation failures. Upfront refutation honors
the selected axiom policy and retains its certificate. Focused checks also cover
original and specialized query pairs, contract-only specialization, auxiliary
theorem export, original-statement axiom dependencies, and cancellation after
real search work. The exact library guide example was compiled independently.

Both full runs preserve source, executable, native-module, and external-fixture
fingerprints. Complete raw logs, pre/post snapshots, receipts, actual tactic
suggestions and Lean-only replays, and audited ZIP hashes are retained. Each
budget has 837 legacy synthesis-query records, plus 8 frontend cases requiring
13 process stages. These counts overlap in the problems tested; they do not
describe 832 distinct synthesis problems. All 29 E8 cases remain required;
Church stretch outcomes remain unscored and are recorded separately. The six
earlier archives are unchanged.

## Closed program-sketch checkpoint

The [sketch checkpoint](sketches-2026-09-21/README.md) validates implementation
commit `c69f484`: **839/839 required checks across 14 families at both 10 s
and 5 s per search**. Each aggregate build records 83 successful jobs. Seven
new external cases exercise joint step/seed completion, polymorphic identity,
complete-body verification and rejection, malformed holes, and a False contract.
Native ownership, replay, profile, cancellation, and alias tests remain part of
the build gate rather than the external denominator.

Each budget retains 837 legacy query records, 13 frontend process stages, and
10 public sketch stages with three actual-source Lean-only replays. A separate
reference/control process must pass without adding a scored case. The archive
independently rechecks all raw outcomes, generated sources, diagnostics, exits,
and ZIP members; its 202 raw files per budget preserve the original bytes.
Source, both native executables, compiled modules, and external inputs match
the pre-run capture. All thirteen original Church stretch searches remain
bounded misses, and all seven preceding archives are unchanged.

## Typed sketch projection checkpoint

The [projection checkpoint](sketch-projection-2026-09-22/README.md) validates
source revision `3d29761`: **839/839 required checks across all fourteen
families at both 10 s and 5 s per search**. Each aggregate build records 87
successful jobs, including the new projection and integration modules. Native
tests remain separate from the unchanged external denominator.

Each budget preserves the original query inventory and all frontend/sketch
process stages, including actual printed-source replay, in 202 raw files.
Independent audits bind the raw outcomes and diagnostics to identical pre/post
fingerprints for 196 source/configuration files, 60 compiled artifacts, 350
external fixtures, and both native executables. All eight preceding archives
retain their Git trees and working bytes. The thirteen original unassisted
Church stretch queries remain bounded misses; the focused supplied-carrier
`at` and `foldr1` experiments retain their separate contracts and evidence.
