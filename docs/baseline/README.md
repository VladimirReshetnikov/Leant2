# Baseline runs

Records of `tools/run_baseline.py` over Leant's `:synth` golden corpus
(`C:\Leant\test\synth-*.txt` at Leant revision `6bf05ad`), scored by outcome
category per the unified proposal's Definition 1.5. Each run names the Leant2
commit it was produced from and the per-query budget.

| Date | Commit | Budget | Score |
| --- | --- | --- | --- |
| 2026-09-17 | `f197fe0` | 10 s/query | 278/278 |
| 2026-09-17 | `56c307d` | 10 s/query | 278/278 (ranked candidates) |

The `.log` file lists per-fixture scores and any failures; the `summary.json`
file lists every query with its golden and observed categories.
