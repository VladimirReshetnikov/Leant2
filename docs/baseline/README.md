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
