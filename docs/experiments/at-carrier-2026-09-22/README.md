# Exact Church at: two-hole carrier completion

The supplied-carrier sketch for **`church_case_033` / `at`** completed at both
5,000 and 10,000 ms query budgets. Each run produced one accepted program and
independently replayed its exact original supplied-default type and all **168
original observations**, with no axioms. The carrier `Int → A` and outer fold
application were supplied; the two holes were synthesized. The sole explicit
provider was the specification's existing `BehaviorPartialNumeric.intCase`.

This is a focused, unscored finite-contract experiment. Together with the
separate [foldr1 experiment](../sketch-projection-2026-09-22/README.md), two of
the thirteen proposed carrier-given counterparts now have verified finite
completions; eleven remain unestablished. The **thirteen original unassisted
Church stretch queries remain open**. The historical
[839/839 acceptance checkpoint](../../baseline/sketches-2026-09-21/README.md)
and its source attribution are unchanged; this bundle adds no aggregate cases.

## Original query and restricted search inputs

The exact source is `at :: Int -> List a -> a`, Church.hs line 270, from the
existing `C:/Leant/lib/Djex/test-church/behavior_partial_spec.py` corpus. The
established Lean specification inserts an explicit element default immediately
after the type binder. The probe preserves binder order **A, d, n, xs**, the
original `Int` index, every observation and the complete generated predicate
`BehaviorPartial.check_at (f) = true`. Empty lists, negative indices and
out-of-range indices retain the supplied-default behavior.

[provenance.json](provenance.json) contains the exact original and defaulted
types, all 168 observation rows, primitive declaration, provider inventory,
known witness, source/specification hashes, and generated-file hashes. The
original normalized Church source SHA-256 is
`782e4edaa5bf813e30e39ae02d52278ab0566315ebc521401a947b98c44cfd11`.
No original fixture was removed or weakened.

The fixed skeleton was:

```lean
fun (A : Type) (d : A) =>
  (fun (step : A → (Int → A) → Int → A) (init : Int → A)
       (n : Int) (xs : ∀ R : Type, (A → R → R) → R → R) =>
    xs (Int → A) step init n) ?step ?init
```

The native preparation assertion confirmed exactly `step` then `init`, with
two original locals each: `A : Type` and `d : A`. Neither hole could see the
later `n` or `xs`. The query used `.strictConstructive`, one candidate, zero
grace, and precisely the original generic integer branch primitive. Native
constructors, elimination and proof rules remained available. There was no
session-provider discovery and no reference implementation provider.

[Controls.lean](Controls.lean) ran first in a fresh process importing **only
Lean**. It checked the original full witness, the original primitive-only
`Int → A` carrier witness, and the `always_default` and `ignores_index` wrong
controls. These definitions and their original checking theorems yielded eight
axiom audits. The primitive and its two original branch theorems yielded three
more. All **eleven** audits were axiom-free. No oracle/control declaration was
imported into either synthesis process.

After the sketch API restored search state, each accepted object independently
passed kernel replay at the original target and at the **unreduced original
contract application**. The candidate and both audits had no axioms. A
transitive traversal of the program's constant types and bodies, including
opaque bodies, rejected observer/oracle/control/probe namespaces. The exact
`BehaviorPartialNumeric.intCase` was the only exception, and its dependencies
were still traversed. Direct program constants were `Int` and that primitive;
the traversal reviewed **135** declarations. Observer dependencies in the
contract and proof were permitted, as required to express the contract.

## Retained outcomes

The complete original [receipt](sketch-at-experiment-01.receipt.json) and
independently recomputed [audit](audit.json) agree:

| Query budget | Actual outcome | API elapsed | Native process elapsed | Rule applications | Unifications | Proof attempts | Candidates | Rejected proposals |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 5,000 ms | Accepted | 1,169 ms | 5,240 ms | 533 | 1,736 | 239 | 1 | 237 |
| 10,000 ms | Accepted | 1,186 ms | 5,095 ms | 533 | 1,736 | 239 | 1 | 237 |

The controls process took 5,841 ms. All three native processes exited zero;
all three stderr streams were empty; no warning/error, cancellation, external
timeout or cleanup occurred. The wrapper exited zero with unchanged complete
input snapshots. These are individual observed times, not a general speedup
claim, benchmark distribution, or projection-enabled/disabled ablation.

Both queries printed exactly the same accepted expression:

```text
fun A d =>
  (fun step init n xs => xs (Int → A) step init n) (fun a a_1 a_2 => BehaviorPartialNumeric.intCase A a_2 d a a_1)
    fun a => d
```

This is preserved diagnostic text. In addition to kernel replay of the accepted
internal expression, a later **separate Lean-only process** compiled this exact
printed program and target, proved its original finite contract, and executed
the original checker successfully. The
[supplementary replay audit](replay-audit.json) reconstructs
[at.lean](source-replay/at.lean) byte-for-byte from both original raw query
transcripts and the unchanged checker/primitive prefix. It imports only Lean,
with no synthesis module or reference implementation.

That fourth native process took 3,074 ms, exited zero, printed two axiom-free
audits and `ALL_168_ORIGINAL_OBSERVATIONS_EXECUTED_TRUE`, and had empty stderr.
Its 1,042-byte stdout and source/executable hashes agree with the separate
[replay receipt](source-replay/receipt.json). The original synthesis receipt is
unchanged. The shared replay receipt and generator retain a foldr1 row for
provenance; this bundle audits **only their at portion**. The evidence does not
establish public result-alias/compiler-adapter publication, a universal equation
for the synthesized program, or behavior for all Church inhabitants. The 168
observations remain a finite contract.

## Reproducible evidence audit

Run these pure Python checks from the repository root; neither starts Lean:

```powershell
python -B -X utf8 docs/experiments/at-carrier-2026-09-22/verify_bundle.py
python -B -X utf8 docs/experiments/at-carrier-2026-09-22/test_bundle.py -v
```

With the original external corpus available, additionally reconstruct every
generated input byte from that authoritative source:

```powershell
python -B -X utf8 docs/experiments/at-carrier-2026-09-22/verify_bundle.py --check-reference
```

[evidence.zip](evidence.zip) retains the **entire original 14-file experiment
directory**: both input snapshots, source provenance, original corpus manifest,
top-level receipt, and all three per-process receipts/stdout/stderr pairs. The
six raw streams contain 7,404 stdout bytes and zero stderr bytes. Every ZIP
member is hash-checked and CRC-checked; exact member cardinality is required.
[SHA256.json](SHA256.json) covers every other bundle file and every ZIP member.
The archive-local [.gitattributes](.gitattributes) preserves exact bytes.

The six fingerprinted probe inputs and the original runner tests are copied
without changes. Their draft/unvalidated comments record their state before
the experiment; the native outcome is established by the separate receipts,
raw output and audit. The unchanged original classifier is imported by
[verify_bundle.py](verify_bundle.py). Only its envelope path check is adapted
in memory: the exact recorded original path may refer to the archived,
byte-identical Probe. The original source-span, severity, caption, ledger,
outcome and replay-marker checks remain intact. Neither raw bytes nor the
frozen classifier are rewritten.

The additional `source-replay/` files preserve the exact at replay source/raw
streams and unmodified shared receipt/generator. The generator is stored as
text and is not imported or executed by the verifier. The additive replay
audit checks source reconstruction, original-output binding, import isolation,
the actual three diagnostics and their source spans, and process/source/native
hashes. Its one process and two raw streams are separate from the original
three processes and six streams inside the ZIP.

The verifier also compares per-process commands/source/executable hashes,
raw byte lengths and hashes, exact control inventories, all stored
classifications, source provenance, and equal pre/post snapshots. Its pure
regressions reject stale green receipts after bounded misses or trailing
errors, missing/surplus queries, missing control audits, input/source drift,
wrong diagnostic paths/spans, bad member hashes, and incomplete ZIP inventories.
They also reject substituted replay programs and trailing replay errors even
when the accompanying raw-output hash has been updated.

The snapshots record **64 source/configuration files, 60 local compiled-module
artifacts, 12,592 toolchain module artifacts, 20 toolchain native artifacts,
six frozen probe inputs, and eleven original provenance files**, together
with the selected Lean and Python executables. These conservative inventories
do not claim every file was loaded. [source-state.json](source-state.json)
records a post-run comparison with the working source bytes and the Git HEAD
at packaging. The run occurred during implementation work; this is not an
exact-commit build receipt. The wrapper did not build. Fingerprints establish
identity at snapshot boundaries, not source/module correspondence or absence
of a transient change reverted between snapshots.

The original [run_probe.py](run_probe.py) is retained for review and fresh
future experiments with explicitly selected matching prebuilt Lean and a new
output directory. Rerunning it is a new native experiment, requires the shared
native slot, and cannot replace these preserved outcomes.
