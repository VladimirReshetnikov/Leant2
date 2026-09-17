# Leant2: Lean-native synthesis architecture

**Design proposal with remotely compiler-checked feasibility experiments.**
Prepared September 17, 2026. No existing repository was modified.

Start with `article/leant2.pdf`. Its modular LaTeX sources, references, and build
instructions are in `article/`. The article gives an architecture and concrete
algorithms for a Lean-only successor to Leant and Djex. It is not a claim that the
complete proposed system has been implemented.

## Main design

The general engine retains actual Lean expressions, universes, local contexts,
and metavariable constraints. It does not translate every query through a second,
approximate type system. Immutable search recipes support reproducibility, while
transactional native states support efficient dependent search.

Its construction mechanisms are focused term synthesis, demand-directed library
composition, recursor/termination schemas, program-and-proof co-synthesis, and
certified domain-specific lanes. The scheduler must retain the dependencies
between computational choices and their proof obligations: failure of a later
proof can require reconsidering an earlier witness. Tests guide search, but a
mandatory universal specification requires a checked proof.

The result protocol separates certified inhabitants, observed candidates,
certified noninhabitation, precisely scoped grammar exhaustion, and unknown
results. The article supplies a conditional relative-completeness argument,
explicit trust and execution policies, benchmark strata, adversarial tests, and
milestone acceptance gates.

## Contents

| Path | Purpose |
| --- | --- |
| `article/leant2.pdf` | The complete article |
| `article/leant2.tex`, `article/sections/`, `article/references.tex` | Rebuildable LaTeX sources |
| `prototype/Core.lean` | Native continuation-search tactic and dependent examples |
| `prototype/Behavior.lean` | Finite affine synthesis with universal certificates |
| `prototype/lean-toolchain`, `prototype/lakefile.lean` | Minimal pinned replay project |
| `evidence/*.receipt.json` | Selected final remote-check response fields |
| `evidence/attempt-history.json` | Failed and superseded attempts, including corrections |
| `evidence/Core-failed-index-binder.lean` | Preserved failed revision; **not** a build target |
| `experiments/affine_counts.py` | Independent Python enumeration-count mirror |
| `experiments/check_artifact.py` | Source/receipt consistency check; not a proof checker |
| `tools/` | The supplied AXLE clients and their original README |
| `sources.json` | Repository revision boundaries and primary-source URLs |

## What was actually checked

Both final `.lean` files were submitted through Wolfram's HTTP facilities to the
AXLE check endpoint with environment `lean-4.34.0`, `ignore_imports=false`,
`theorems_only=false`, and a 40-second request timeout. The service reported Lean
**4.34.0**, `okay=true`, no failed declarations, and no Lean or tool errors for
both final submissions. The returned source echoes matched modulo surrounding
whitespace, and the submitted source hashes match the included final files.

The receipts are **selected fields transcribed from the tool responses**, not
byte-for-byte raw HTTP archives. They retain request IDs, source identities,
executor identifiers, all named axiom audits, warnings, and whole-file timings.
Those timings are not isolated synthesis benchmarks. No independent local Lean
or comparator replay was performed during preparation.

### Native core

`Core.lean` fully synthesizes thirteen small declarations covering ordinary and
dependent functions, products/sums, dependent pairs, a constrained natural-number
witness, higher-rank arguments, independent universe parameters, strict implicit
binders, and supplied class data. Its search explores introductions, local
applications, constructors, reflexivity, and restricted case splits.

The vector-map example has an **author-supplied recursive skeleton and recursive
call**. Its branch bodies are synthesized. A separate **author-written induction
proof** certifies the map's universal list semantics. This is not automatic
recursion or invariant discovery.

Twenty declarations were audited. Nineteen reported no axioms; the vector-map
correctness theorem reported `propext`. The vector-map implementation itself
reported no axioms. Three expected-failure controls test the bounded tactic; they
are not completeness proofs. `uniformEmpty` is a separate author-written genuine
noninhabitation certificate.

The core is deliberately small: depth-first search with depth 30, no global
provider inventory, no production resource accounting or cancellation policy,
no general instance-search service, and no automatic recursive or indexed case
splitting. The simple `twoUniverses` example is **not** the predecessors' original
simultaneous two-box fixture.

### Behavioral lane

`Behavior.lean` enumerates 25 affine functions `f(n) = a*n+b` with coefficients in
`{0,1,2,3,4}`. Its mandatory specification is:

```
f 0 = 1  AND  for every natural n, f (n+1) = f n + 2
```

An author-written Lean theorem characterizes all natural affine coefficients
satisfying this specification. The certifier returns a proof-carrying candidate,
not just a Boolean acceptance signal. The final search selects `(a,b)=(2,1)`.
It visits 12 candidates, invokes the certifier 3 times, and rejects 9 via its
counterexample bank. These counts and the result were checked by Lean.

Calling the certifier for every candidate in the same prefix would require 12
calls. This is a call-count comparison, **not a measured runtime speedup**.
The specialized affine verifier is not a general solver for Lean specifications.
The five behavioral axiom audits contain only `propext` or `propext` together
with `Quot.sound`; none contains `sorryAx` or `Classical.choice`.

## Reproduce

### Lean, locally

With the pinned Lean toolchain installed, from `prototype/`:

```sh
lake env lean Core.lean
lake env lean Behavior.lean
```

The source files import `Lean`, not Mathlib. The remote service nevertheless
emitted advisories about its preferred Mathlib header. These are retained in the
receipts; the original imports were not overridden. The minimal Lake project is
provided for replay, but it was not locally built in this environment.

Do not include `evidence/Core-failed-index-binder.lean` in a successful build: it
is intentionally preserved evidence of a rejected revision.

### Lean, remotely

The supplied clients send the source to an external AXLE service. Review them
and their README before submitting private code. From this archive's root:

```sh
python tools/axle_check.py prototype/Core.lean \
  --no-audit --theorem Leant2Prototype.vecMap_spec \
  --environment lean-4.34.0 --timeout 40 \
  --output evidence/Core.replay.json

python tools/axle_check.py prototype/Behavior.lean \
  --no-audit --theorem Leant2Behavior.run_result \
  --environment lean-4.34.0 --timeout 40 \
  --output evidence/Behavior.replay.json
```

The files already include all their `#print axioms` commands. `--no-audit`
preserves the source; the explicit theorem selects the client's principal audit
target. Inspect the entire returned response, not only the selected audit.
Availability and environment support of the external service may change.

### Supporting checks

From the archive root with Python 3.10 or newer:

```sh
python experiments/check_artifact.py
python experiments/affine_counts.py
```

The first compares the retained receipts and source bytes. It does not rerun
Lean or independently authenticate the remote service. The second independently
mirrors the small enumeration count; it is not a Lean proof checker.

### Article

From `article/`, run `make`, or execute the following three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error leant2.tex
```

A normal TeX installation with the packages used in the preamble is required.
The article uses inline bibliography entries and needs no BibTeX run. `make clean`
removes auxiliary build files without deleting the PDF.

## Evidence and scope

The repository review uses Leant commit
`6bf05ad78c467989e68290f2d08bbed40802d485` and standalone Djex commit
`e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`. The reviewed Leant documentation
separately identifies its vendored Djex dependency as `e237e866`; these revision
boundaries must not be conflated. Existing rewrite analysis and current indexing
composition diagnostics are explicitly discussed rather than treated as new
findings of this article.

The complete scheduler, demand index, automatic recursion/motive discovery,
general behavioral proof service, SMT adapters, and broad benchmark are proposed
work. The predecessors' original indexing and two-box fixtures were not rerun or
solved by these microexperiments. The article's status ledger makes these
boundaries explicit.
