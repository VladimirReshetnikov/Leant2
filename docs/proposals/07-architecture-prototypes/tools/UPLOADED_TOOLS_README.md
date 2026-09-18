# Checking Lean code remotely with AXLE

AXLE (Axiom Math's Lean service) compiles a Lean 4 file with a bundled
Mathlib and returns the compiler's messages over HTTP, so a proof can be
checked from an environment that has network access but no Lean toolchain.
This directory contains instructions and two clients:

| File | Purpose |
|---|---|
| `axle_check.py` | Python 3.9+, standard library only. Submits a file, appends the project's axiom/statement guard, validates the answer, writes a JSON receipt. |
| `axle_check.wls` | The same check in Wolfram Language, as a script or as a function `AxleCheck` for a notebook or a Wolfram evaluator tool. |

## 1. The check API

`POST https://axle.axiommath.ai/api/v1/check` with a JSON body.
Documentation: <https://axle.axiommath.ai/v1/docs/tools/check/>.

| Field | Type | Default | Use |
|---|---|---|---|
| `content` | string | required | The Lean source. Diagnostics (`#print axioms ...`, an `example` restating the theorem) are appended to the same string. |
| `environment` | string | required | An environment name such as `lean-4.34.0` (§1.1). |
| `ignore_imports` | bool | true | When true the service replaces the import header by its cached `import Mathlib`; `false` keeps the file's own imports. |
| `theorems_only` | bool | true | Documented as "process only theorem/lemma declarations"; the clients send `false`. |
| `timeout_seconds` | float | 120 | Server-side elaboration budget; documented cap 900. |
| `names`, `indices` | list | – | Restrict validation to some declarations. |
| `mathlib_options`, `global_options` | – | – | Lean option overrides (e.g. heartbeats). |

Response, a JSON object (HTTP 200 whenever the service itself ran):

| Field | Meaning |
|---|---|
| `okay` | Compilation succeeded. `sorry` still gives `okay: true`. |
| `failed_declarations` | Named declarations with errors or `sorry`. Anonymous `example`s are not listed. |
| `lean_messages.{errors,warnings,infos}` | Lean's own messages. `#print axioms` and `#eval` output arrive in `infos`, as `-:LINE:COL-LINE:COL: info: ...`; the file name is `-` and lines count the submitted `content`, including anything appended. |
| `tool_messages.{errors,warnings,infos}` | The service's validation layer: header advisories, "Declaration 'x' is incomplete", "Imports mismatch detected. Overriding with default header". |
| `content` | The source as processed; a substituted header shows up here. |
| `timings` | `parse_ms`, `total_ms`. |
| `info` | `request_id`, `environment`, `cached_response`, queue and execution times, and `_executor_commit_sha` / `_executor_docker_image_id` / `_executor_artifact_sha256`, which identify the service build. No Mathlib commit is reported. |
| `user_error` | Present instead of a result when the request itself is rejected (unknown environment, malformed body), still with HTTP 200. |

Authentication: anonymous requests are accepted. If a key is set in
`AXLE_API_KEY`, `axle_check.py` sends it as `Authorization: Bearer ...`. The
client retries 429/502/503/504 with backoff.

Related endpoints and tools: `verify_proof/` (checks a proof against a
separately supplied sorried statement), a pip package (`pip install axiom-axle`, `from axle import AxleClient`,
async `client.check(content=..., environment=...)`), and a CLI.

### 1.1 Environments

Names have the form `lean-4.NN.N`; each bundles the Mathlib of that Lean
release. There is no listing endpoint: the list is contained in the
`user_error` returned for an unknown name, which is what
`axle_check.py --list-environments` extracts.

## 2. Running the check

Python:

```bash
python axle_check.py path/to/File.lean
```

```bash
python axle_check.py path/to/File.lean --environment lean-4.32.2
```

```bash
python axle_check.py --list-environments
```

Options: `--audit FILE` (append this Lean text instead of the project guard),
`--no-audit`, `--theorem NAME` (the declaration whose axiom report is read),
`--allowed-axiom NAME` (repeatable), `--ignore-imports`, `--timeout SECONDS`,
`--endpoint URL`, `--output FILE` for the receipt, `--prepare-local FILE`
(write source + audit to a file for `lake env lean`, sending nothing),
`--quiet`. If the console is not UTF-8, set `PYTHONUTF8=1`.

By default the client appends the project's `checks/Axioms.lean` (found by
walking up from the source file) minus its `import` line, so the remote run
executes the same `#print axioms`, the same `run_cmd` axiom filter and the
same frozen-statement `example` as the local guard. Without a
`checks/Axioms.lean` nearby it appends `#print axioms <theorem>` and
`#eval Lean.versionString`.

Wolfram Language: run `axle_check.wls` as a script with the arguments
`SOURCE.lean [ENVIRONMENT [AUDIT.lean [THEOREM]]]`, or load it and call

```wolfram
AxleCheck["path/to/File.lean", "lean-4.34.0", "path/to/checks/Axioms.lean"]
```

The audit file is appended minus its `import` lines and is expected to print
the axioms of the theorem; with `""` as audit file the script appends
`#print axioms THEOREM` itself, so the fourth argument is then required.

Plain HTTP, for any other tool (the audit tail goes inside the JSON string):

```bash
curl -sS -X POST https://axle.axiommath.ai/api/v1/check -H 'Content-Type: application/json' --data-binary @request.json
```

Both clients write `<source>.axle.json`: verdict, the problems found, the
axiom list, `request_id`, executor identifiers, SHA-256 of the source and of
the submitted content, and the complete response.

## 3. What the clients check

`PASS` requires all of:

1. no `user_error` in the response;
2. `okay == true`, `failed_declarations == []`, `lean_messages.errors == []`,
   `tool_messages.errors == []`;
3. no Lean warning containing ``declaration uses `sorry` `` (the only trace an
   anonymous `example ... := by sorry` leaves);
4. the `#print axioms` line for the theorem is present in `lean_messages.infos`
   and lists nothing beyond `propext`, `Classical.choice`, `Quot.sound`;
5. the echoed `content` equals what was sent, unless `--ignore-imports` was
   requested.

The frozen-statement `example` of the appended guard is covered by 2; the
receipt's `content_sha256` records what was submitted. Exit status: 0 PASS,
1 otherwise, 2 when the check could not be performed.

## 4. Service behavior

* `okay: true` with `sorry`: a file whose theorems are all `sorry` compiles.
  Named declarations then appear in `failed_declarations`; anonymous
  `example`s appear only as a warning.
* `ignore_imports` defaults to `true` and swaps in `import Mathlib` without
  failing; the signs are a `tool_messages.infos` entry ("Imports mismatch
  detected. Overriding with default header") and the echoed `content`. A file
  that only compiles thanks to a transitive import it does not write passes
  with the default and fails locally.
* With `ignore_imports: false`, an explicit import list draws two advisories
  in `tool_messages.warnings`: "`Mathlib.Tactic` is a required import but is
  missing" and "you are not using the default header ... may experience
  significant slowdowns". They do not affect the result.
* An unknown environment is not an HTTP error: the body is
  `{"user_error": "Unknown environment: ... Available environments: ..."}`
  with HTTP 200.
* No Mathlib revision is reported, only the environment name and executor
  hashes. Lemma names, simp sets and import structure differ between Mathlib
  snapshots, so a file can pass remotely and fail against the project's pin,
  or the reverse.
* Identical `content` in the same environment may be answered from a cache
  (`info.cached_response: true`, `total_ms` of a few milliseconds); changing
  a comment forces a fresh run.
* `timeout_seconds` is the server budget; the HTTP client's own timeout has
  to exceed it plus queue time. A full check of a file of a few hundred lines
  takes on the order of ten seconds; a cold environment or a non-default
  header takes longer.
* Lean source is full of `ℕ`, `∀`, `⟨⟩`. The clients send UTF-8 bytes or
  ASCII-escaped JSON (`json.dumps(..., ensure_ascii=True)`) and read the
  answer as UTF-8; in Wolfram Language the body is built with
  `ExportByteArray[..., "RawJSON"]` and the answer read with
  `ImportByteArray[response["BodyByteArray"], "RawJSON"]`, because
  string-based transfers corrupt the source.
