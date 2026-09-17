# Validation and development notes

Date: 17 September 2026. No local Lean or Lake executable was available, and
container network requests failed DNS resolution. Lean checks were actually
executed using Wolfram Language's HTTP client and the AXLE check endpoint
identified in the user-supplied `tools.zip`.

The JSON files are compact transcriptions of observed tool responses, not claims
of a local build. The exact submitted sources are `lean/Validation.lean` and
`lean/RecursionCertificates.lean`. Their UTF-8 SHA-256 values were computed in the
remote request and independently matched locally. The service returned the
submitted source with one extra terminal newline. It did not change imports.
Receipts omit echoed source to avoid duplication. Service timings describe the
whole check, not isolated search speed, and are not a performance comparison.

## Successful final runs

* Native prototype: request `3ae6e8d8-a4a5-491a-a01a-1883ff4b35c1`.
  All 21 synthesis examples, four rejection controls, eight additional statements,
  and evaluation/audit commands compiled. Twenty-four of the 25 audited
  declarations have empty inventories; `indexedHeadNative` uses `propext`.
* Recursion artifacts: request `7593e833-ccb3-40da-ae93-689c27d941a3`.
  All four declarations audited. `sumCorrect` uses `propext`; the other three
  inventories are empty. The recursion schemas are manually selected. Only
  the affine-fold coefficients were synthesized in the local Python experiment.

No accepted result depends on `sorryAx`, `Classical.choice`, or `Quot.sound`.
The audit permits Lean's standard three axioms but records the actual inventory.

## Earlier failed attempts and corrections

1. API probe `41bc9dbe-28bb-4c33-a611-92f1c85366e2`: two guessed API names
   were unavailable. `mkConstWithFreshMVarLevels` is in `Lean.Meta`; interrupt
   handling uses the internal-exception constructor instead of an absent helper.
2. First prototype `4a8a8471-836f-456a-9ee9-ea637ba733b6`: multiline record
   layout caused a parse failure. Fixed the `ApplyConfig` layout.
3. Small original prototype `ab9bc60b-16a3-4ca8-b64e-dc4c90f6e259`: passed
   identity, composition, and a constrained selector; recorded empty inventories
   for the latter two. This was not the larger final test suite.
4. Expanded suite `c7da8c35-cf34-440b-9546-dec962ef3e5c`: a generic application
   of `Sigma.snd` did not determine its parent. Added explicit projections of
   known local structures, using Lean structure metadata and `mkProj`.
5. Expanded suite `44d30919-a934-45c1-a91f-77dbac3aa5b4`: all synthesis
   declarations were accepted, but the overly strict zero-axiom audit rejected
   the indexed-head proof's `propext`. Changed the audit to the documented
   standard-axiom policy and printed every inventory. No output proof was
   replaced by an assumption.
6. Recursion draft `e81dd5f6-86df-4f30-b56f-9568e7cbb8aa`: wrote propositional
   negation directly on a type. Replaced it by `(forall A : Type, A) -> False`,
   a genuine proof of emptiness. This corrected file was checked again.

A few transport/decompression experiments made no compilation request and
provided no Lean evidence. The final evidence is the two successful runs above.
