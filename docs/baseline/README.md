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
searches and thirteen Church stretch searches remain unsolved. The checkpoint
also records the difference between baseline outcome scoring and execution
of ordinary commands or newly returned results.
