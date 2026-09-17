# Leant2: Lean-native synthesis of programs and their contracts

This archive contains a technical architecture and algorithm design for a Lean-only
successor to Leant and Djex, together with small executable experiments.

## Start here

Open `article/Leant2.pdf`. The LaTeX entry point is `article/Leant2.tex`; its section
sources and bibliography are included. The article covers exact Lean request semantics,
transactional coupled term/proof search, polymorphic application spines, dependent
elimination, proof-carrying recursion, behavioral propagation, certified abstractions,
CEGIS, solver boundaries, caching, acceptance, process isolation, and an evaluation plan.

The proposed production interfaces (`synthdef`, `leant2`, extension schemas) are designs,
not implemented APIs. The actual small tactic is named `micro_synth`.

## What was implemented and checked

`prototype/MicroSynth.lean` is a bounded Lean-native metaprogram. It passed 15 complete
synthesis declarations, two manually supplied elimination skeletons with synthesized
branches, and three expected bounded-failure controls on Lean 4.34.0 through the AXLE
service, called via Wolfram Language. All 15 complete synthesis outputs and the equality
transport skeleton have empty printed axiom inventories. The indexed-head skeleton uses
`propext`. The prototype does not discover general recursion or dependent case skeletons.

`prototype/Certificates.lean` defines a list-fold grammar and **handwritten** proofs of
its exact length summary, the necessary/sufficient length-preservation condition, and the
universal correctness of the exact reverse AST selected by the Python experiment. It
passed a separate remote Lean 4.34.0 check. The length proofs use `propext` and `Quot.sound`;
the reverse proof uses `propext`. No audited result uses `sorryAx` or `Classical.choice`.

There was no local Lean installation and no independent kernel run. The remote checks
preserved `import Lean` (`ignore_imports=false`) and returned no Lean errors or failed
declarations. Compiler/style and service import advisories are described in the receipt
summary. A later repeat of the certificate request was cached, not a second fresh run.

`receipts/check-summary.json` is a manually transcribed summary of actual tool responses,
not an untouched raw API response or signed certificate. Exact submitted sources are in
`receipts/*.submitted.lean`. Their annotated counterparts only add comments/blank lines.

## Reproduce

With the pinned Lean version installed, run from this directory:

```sh
lean prototype/MicroSynth.lean
lean prototype/Certificates.lean
```

Alternatively, from a network-enabled environment (Python standard library only):

```sh
python tools/check_remote.py prototype/MicroSynth.lean
python tools/check_remote.py prototype/Certificates.lean
```

The helper retains a complete new response in `*.remote.json`, preserves imports, checks
errors and source echo, and requires every `#print axioms` report. Its default axiom
allowlist is `propext`, `Quot.sound`; repeated `--allowed-axiom` overrides it. An optional
`AXLE_API_KEY` is read from the environment but never recorded in the receipt. Preparing
a request without making an external call is possible with `--prepare-request FILE`.
The wrapper is a convenience client, not an independently verified checker.

For Wolfram Language:

```wolfram
Get["tools/remote_check.wls"];
r = AxleCheckSource[Import["prototype/MicroSynth.lean", "Text"]];
r["passed"]
```

The HTTP/UTF-8 mechanism was used for the article's remote experiments. The reusable
wrapper adds audit parsing and is not itself formally verified.

The finite algorithm experiment needs only Python 3.9+:

```sh
python experiments/cegis.py --output experiments/results.json
```

It enumerates 3,873 fold-step ASTs of at most nine nodes, retains 354 with the required
length summary, and compares ordinary versus length-guided counterexample search. A
separate intentionally unsound deduplication control loses the correct reverse program.
All reported candidate counts are deterministic. Passing the 121-input corpus is not
a universal proof; the separate Lean certificate proves the selected program correct.

Replay-response validation has offline fixture tests (these do not run Lean or HTTP):

```sh
python -m unittest discover -s tools -p 'test_*.py' -v
```

Build the article with a usual TeX installation, Latin Modern Roman/Sans, and DejaVu
Sans Mono available on the system:

```sh
cd article
latexmk -xelatex -interaction=nonstopmode -halt-on-error Leant2.tex
```

No font files are redistributed. The PDF was built with XeLaTeX and visually inspected
from rendered pages.

## Source snapshots

Leant: `6bf05ad78c467989e68290f2d08bbed40802d485`.
Djex (independently inspected HEAD): `e8778f4ebd63e1f9b9b410fa4de8d14a8a04c9e5`.
These are not a claim that the inspected Leant revision uses that Djex HEAD as its
submodule. Exact source/documentation links and research references are in the article.

The architecture, expected coverage, scheduling policies, recursion planner, and
production acceptance system are proposals. The small prototypes validate selected
mechanisms and should not be read as a completed Leant2 implementation or an empirical
success-rate claim about real Lean projects.
