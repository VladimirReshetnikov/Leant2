# Carrier-given `foldr1`: focused sketch projection evidence

The unchanged `church_case_039` sketch accepted at both 5,000 and 10,000 ms after
the typed partial-projection implementation. Each result passed independent
native replay at the exact original defaulted target and all 36 original
observations, under `strictConstructive`, with explicit query providers `#[]`.
All three holes—`step`, `init`, and `finish`—remained open when synthesis began.
The carrier `Option A` and its fold application were supplied by the sketch.

| Run | Query budget | Result | API elapsed | Whole process | Rejected | Candidates |
|---|---:|---|---:|---:|---:|---:|
| Earlier implementation, experiment 02 | 5,000 ms | bounded miss | 5,163 ms | 7,657 ms | 7,951 | 0 |
| Earlier implementation, experiment 02 | 10,000 ms | bounded miss | 10,241 ms | 12,620 ms | 15,423 | 0 |
| Projection enabled, experiment 03 | 5,000 ms | accepted | 3,934 ms | 6,621 ms | 419 | 1 |
| Projection enabled, experiment 03 | 10,000 ms | accepted | 3,943 ms | 6,576 ms | 419 | 1 |
| Same build, projection disabled, ablation 01 | 5,000 ms | bounded miss | 5,136 ms | 7,618 ms | 4,939 | 0 |
| Same build, projection disabled, ablation 01 | 10,000 ms | bounded miss | 10,189 ms | 12,616 ms | 8,290 | 0 |

These are individual bounded runs, not a statistical speedup estimate. The API
timer covers `synthesizeSketch`; process time also includes native startup and
imports. Cooperative budgets permit overrun. A bounded miss does not establish
impossibility. The ablation uses the identical source, compiled modules,
toolchain, query, controls, and budgets as accepted experiment 03; its only native
probe option change is `-Dleant2.skipRules=sketchProjection`.

Both accepted runs printed exactly this candidate:

```lean
fun A d combine =>
  (fun step init finish xs => finish (xs (Option A) step init))
    (fun a a_1 => some (Option.casesOn a_1 a fun val => combine a val)) none
    fun a => Option.casesOn a d fun val => val
```

The two accepted work ledgers are identical: 1,774 rule applications, 5,863
unifications, 432 proof attempts, one candidate, and 419 rejections. The raw
printed candidate text has SHA-256
`19425e63c37ff5f5a6f39258a5a8cf2c81ff4ba16b870d22cf19482d0dd8a86d`.
Native replay reported no axioms, direct constants
`[Option, Option.some, Option.casesOn, Option.none]`, and five transitively
reviewed program declarations. The probe rejects observer/reference/control
dependencies in the program. Native constructors and elimination remain
available when explicit query providers are empty.

## Preserved obligation and limits

The original binder order is type, default, combining operation, Church list:

```lean
∀ A : Type, A → (A → A → A) →
  (∀ R : Type, (A → R → R) → R → R) → A
```

The original corpus supplies 36 observations: 16 over `Int`, eight over `Bool`,
and 12 over `List Int`. The frozen generator imports the authoritative
`C:/Leant/lib/Djex/test-church/behavior_partial_spec.py`; its exact target,
contract, observations, and source identities are in [provenance.json](provenance.json).
The original query, template, controls, generator, and runner have byte-identical
hashes in both implementation snapshots. [audit.json](audit.json) records all
seven source-file differences and the 15 changed or added local module artifacts.

The 11 axiom-free controls ran in a separate Lean-only process. They include the
known witness, three separating wrong implementations, and a universal theorem
for the separately supplied reference carrier term on native-list encodings.
That reference theorem is **not a universal source-equivalence proof for the
synthesized candidate**. This result completes one carrier-given finite contract;
it does not infer the carrier or establish all 13 Church stretch cases.

## Evidence and source state

[evidence.zip](evidence.zip) preserves the original raw stdout/stderr bytes,
per-process results, top-level receipts, before/after snapshots, and corpus
provenance for all three experiments. Their snapshots include source files,
local modules, 12,592 toolchain module artifacts, 20 native artifacts, frozen
probe inputs, and 11 external provenance files. Accepted experiment 03 records
64 source/configuration files and 60 local module artifacts. Full snapshot JSON
is compressed rather than duplicated as large loose files.

[SHA256.json](SHA256.json) binds every other bundle file and every ZIP member.
The compact experiment/build receipts are unchanged copies. [audit.json](audit.json)
and [ablation-audit.json](ablation-audit.json) are independently recomputed from
the raw bytes with the frozen classifier. The original unmodified classifier
and the relocation adapter produced identical classifications during packaging.

The runs were performed in a dirty working tree based on
`9abfb3610caa5a31769a54e3b9c1c4be8c819069`. That base commit does **not** identify
the tested projection implementation. [source-state.json](source-state.json)
records the actual source hashes and their post-experiment comparison with the
working tree. There is no claim here of an exact tested implementation commit,
remote CI, or a new full 839-case acceptance archive. The earlier historical
archives remain unchanged.

Separate supporting evidence is summarized in
[validation-summary.json](validation-summary.json), with its original artifacts
also compressed in the ZIP:

- 60 serial module targets succeeded, followed by the aggregate
  `lake build Leant2 Leant2Tests leant2` reporting 87 jobs. All 61 invocations
  exited zero; source hashes were unchanged and match experiment 03.
- The seven public sketch gates passed at each budget, using ten public
  processes plus one independent reference process. Before/after and
  cross-budget fingerprints match; source/module hashes match experiment 03.
  The two preflight-rejection cases correctly use native exit code 1.
- Two guide examples and one README example accepted in two separate native
  processes. Their exact sources and outputs are retained.

The supporting public receipts are summarized and checked for the expected
native statuses; they do not substitute for the full multi-family archive audit.

## Re-audit without Lean or external repositories

From the repository root, run:

```powershell
python -B docs/experiments/sketch-projection-2026-09-22/verify_bundle.py
python -B docs/experiments/sketch-projection-2026-09-22/test_bundle.py
```

The second command includes all 13 unchanged wrapper tests plus the additional
bundle tests. Historical Lean diagnostic envelopes name the old absolute scratch
path. The audit adapter accepts that one recorded path only after checking the
archived `Probe.lean` hash, and preserves every original span/severity check.
It translates the path in an ephemeral dictionary; archived bytes are never
rewritten. The unchanged runner remains bound to its actual directory for new
native executions. Running the unchanged `test_run_probe.py` directly from the
relocated directory lacks this adapter; use `test_bundle.py` instead.

To additionally verify the authoritative corpus and regenerate the exact probe
text **in memory**, use `verify_bundle.py --check-reference`. This requires the
original external checkout at the absolute `C:/Leant/...` path recorded in the
provenance. The default audit is portable and does not require that checkout.

## Fresh native rerun

The frozen runner resolves `ROOT = HERE.parents[2]`. This directory intentionally
has the same depth below the repository root as the original scratch location.
Use this layout, the matching prebuilt local modules, pinned Lean 4.34.0, and the
exact external reference files at `C:/Leant/...`; the runner rejects differing
reference bytes. No native binaries are bundled. Build separately before a rerun
and serialize native work on memory-constrained hosts.

```powershell
python -B docs/experiments/sketch-projection-2026-09-22/run_probe.py `
  --lean 'C:\Users\vresh\.elan\toolchains\leanprover--lean4---v4.34.0\bin\lean.exe' `
  --out baseline-out/foldr1-fresh-rerun
```

Use `run_ablation.py` instead for the recorded projection-disabled variant.
Both require a fresh output directory and run independent controls first. They
never build or rewrite sources. Paths to Lean may be adapted to another matching
installation; the external corpus path is deliberately fixed by provenance.
Moving the probe changes hygienic names and process-location metadata; a fresh
rerun is new evidence, not a reproduction of historical raw bytes or timings.

`prepare.py`, `prepare_ablation.py`, and their generated sources are preserved
unchanged for provenance. Do not execute the generators in this sealed bundle:
they overwrite their local generated files. Their original draft/unvalidated
labels describe generation time; the experiment receipts above establish the
later native outcomes.
