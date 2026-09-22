# Actual printed `foldr1` source replay

The **actual printed target and program** from both accepted foldr1 budgets were
reparsed in a fresh Lean-only process. The process kernel-checked the original
finite contract, reported no axioms for either the program or contract theorem,
and compiled and executed the original checker with all **36 observations true**.

This is separate evidence from synthesis acceptance. The two accepted raw
target/program pairs are identical; this bundle independently reconstructs
the exact [foldr1.lean](foldr1.lean) bytes from those pairs and the unchanged
original observer prefix in the published
[projection bundle](../sketch-projection-2026-09-22/README.md).
It does not substitute the separately supplied reference implementation.

The native process exited zero, with no timeout, interruption, launch failure,
or stderr. Its recorded elapsed time was **12,278 ms**, including startup,
reparsing, theorem checking, and compiled execution. This is a replay-process
measurement, not synthesis time or a synthesis budget.

Exactly three information diagnostics occur at their expected source locations:

1. `ActualCarrierReplay.program` does not depend on any axioms.
2. `ActualCarrierReplay.originalContract` does not depend on any axioms.
3. `ALL_36_ORIGINAL_OBSERVATIONS_EXECUTED_TRUE` follows the compiled checker.

The replay imports only `Lean`. It uses the same pinned Lean executable hash as
the accepted synthesis runs. It neither imports nor invokes Leant2 synthesis and
does not import the reference/control implementation. Native constructors and
the copied original observer declarations are available.

## Evidence and verification

The bundle preserves these files byte-for-byte:

- [foldr1.lean](foldr1.lean), [raw stdout](foldr1/stdout.bin), and
  [raw stderr](foldr1/stderr.bin).
- The original shared [receipt.json](receipt.json). Its `at` row is retained only
  as provenance context; this bundle audits and claims the **foldr1 row only**.
- The original [generator](replay_carrier_sources.py.txt), retained as text to
  avoid accidental execution. It originally lived under `scratch/next-sketch`,
  uses that directory layout, starts native processes, and writes a fresh
  `baseline-out/sketch-carrier-source-replay-01` directory. It is not a portable
  launcher from this evidence folder.

[audit.json](audit.json) is independently recomputed from the sealed synthesis
raw outputs and the replay source/raw bytes. [SHA256.json](SHA256.json) records
all local file hashes and explicit pins for the required sibling projection
bundle. The local attributes rule disables Git text conversion, including for
itself, so original bytes survive indexing and checkout.

Run the pure audits from the repository root:

```powershell
python -B docs/experiments/foldr1-source-replay-2026-09-22/verify_bundle.py
python -B docs/experiments/foldr1-source-replay-2026-09-22/test_bundle.py
```

These commands do not run Lean, alter artifacts, or require `C:/Leant`. They
require the sealed sibling projection bundle in its published relative location.
The auditor checks that bundle's manifest and raw classifications, extracts both
accepted target/program pairs, reconstructs the replay source, and verifies all
three diagnostic payloads, positions, file names, source hashes, and executable
hashes. Adversarial tests cover substituted programs/types/checkers, extra or
changed diagnostics, incorrect native status, mismatched runtime/source metadata,
duplicate replay rows, and the deliberate exclusion of the shared `at` row.

For a new native replay, the retained `foldr1.lean` is a standalone Lean 4.34.0
input. Use the matching toolchain with its own `lib/lean` as `LEAN_PATH`, the
matching `LEAN_SYSROOT`, and `lean --json <path-to-foldr1.lean>` in a fresh
process. No Leant2 module is required. A relocated execution has different
diagnostic paths and constitutes new evidence; it must not overwrite this bundle.

## Scope

This establishes reparsability, kernel checking of the exact original finite
contract, two axiom-free audits, and compiled execution of all 36 original
observations for the actual printed candidate. It does **not** establish universal
source equivalence on all Church inhabitants or all native lists. The separate
reference-carrier universal theorem remains a theorem about that reference term.
This is not an additional synthesis run, a full 839-case acceptance archive,
an `at` replay claim, or remote CI evidence.

The origin bundle was published with projection milestone
`23e1f5eba596ed6afffc07f0a87198b9dc2b0e34`; the historical runs' dirty-source
provenance remains as recorded there. No original projection-bundle file was
changed to prepare this follow-up.
