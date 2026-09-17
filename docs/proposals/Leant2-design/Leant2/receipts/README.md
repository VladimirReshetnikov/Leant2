# Check evidence

`check-summary.json` is a **manually transcribed summary of the actual tool responses**.
It is not an untouched raw API response, a signed receipt, or an independent proof certificate.
It includes request identifiers, the reported compiler environment and executor identifiers,
axiom reports, errors, warning summaries, and whether a response was cached.

`MicroSynth.submitted.lean` and `Certificates.submitted.lean` contain the actual
source submitted in the corresponding final checks. The annotated copies in
`prototype/` add only comments and blank lines. The remote service appends trailing
whitespace; both final echo comparisons passed after surrounding whitespace was trimmed.

The initial certificate comparison used an overly specific newline-pattern comparison
and reported false. A small probe established that the service appends a newline; the
cached repeat with plain StringTrim confirmed that the submitted source was unchanged.

The final microprototype had 15 full synthesis declarations, two manually supplied
elimination skeletons with synthesized branches, and three expected bounded failures.
All 15 full synthesis outputs and the equality-transport skeleton have empty printed
axiom inventories. The indexed-head skeleton uses propext. The handwritten certificate
proofs use propext and (for length lemmas) Quot.sound, as recorded. No audited result
uses sorryAx or Classical.choice.

The runs used Lean 4.34.0 through AXLE, invoked from Wolfram Language. They did not use
a local Lean installation, and no independent kernel implementation was run.
Import-header advisories were retained; `ignore_imports` was false throughout.

To obtain fresh complete API responses, use the replay helpers in `tools/` or compile
the sources locally under the pinned Lean toolchain. The replay helpers are conveniences,
not replacements for reading compiler diagnostics and dependency audits.
