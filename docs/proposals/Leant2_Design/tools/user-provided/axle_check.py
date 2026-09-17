#!/usr/bin/env python3
"""Check a Lean file with the AXLE remote Lean service and validate the result.

Python 3.9+, standard library only.  Typical use::

    python axle_check.py path/to/File.lean
    python axle_check.py path/to/File.lean --environment lean-4.32.2
    python axle_check.py --list-environments
    python axle_check.py path/to/File.lean --prepare-local Audit.lean

What "PASS" means here (all of these, not just AXLE's ``okay`` flag):

* the service returned a JSON object without a ``user_error`` field;
* ``okay`` is true, ``failed_declarations`` is empty, and both
  ``lean_messages.errors`` and ``tool_messages.errors`` are empty;
* no Lean warning says ``declaration uses `sorry```` (anonymous ``example``s
  with ``sorry`` are NOT listed in ``failed_declarations``);
* the appended audit produced ``'<theorem>' depends on axioms: [...]`` and
  every listed axiom is allowed (default: propext, Classical.choice,
  Quot.sound);
* the source the service echoes back is what was sent (so the import header
  was not replaced), unless ``--ignore-imports`` was requested.

Exit status: 0 PASS, 1 FAIL (the service answered but the checks did not all
hold), 2 the check could not be performed (network, encoding, arguments).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

DEFAULT_ENDPOINT = "https://axle.axiommath.ai/api/v1/check"
DEFAULT_ENVIRONMENT = "lean-4.34.0"
DEFAULT_ALLOWED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
SORRY_WARNING = "declaration uses `sorry`"
AXIOMS_RE = r"'{theorem}' depends on axioms: \[([^\]]*)\]"
NO_AXIOMS_RE = r"'{theorem}' does not depend on any axioms"
RETRY_STATUSES = {429, 502, 503, 504}


def find_repo_audit(source: Path) -> Path | None:
    """Find ``checks/Axioms.lean`` next to or above the source file."""
    for directory in [source.resolve().parent, *source.resolve().parents]:
        candidate = directory / "checks" / "Axioms.lean"
        if candidate.is_file():
            return candidate
    return None


def audit_from_checks_file(path: Path) -> str:
    """The repository's own guard, minus its ``import`` line.

    ``checks/Axioms.lean`` imports the compiled module; appended to the source
    text instead, its ``#print axioms``, the ``run_cmd`` axiom filter and the
    frozen-statement ``example`` run inside the same file.
    """
    lines = [line for line in path.read_text(encoding="utf-8").splitlines()
             if not line.startswith("import ")]
    return "\n".join(lines).strip() + "\n"


def default_audit(theorem: str) -> str:
    return f"#print axioms {theorem}\n#eval Lean.versionString\n"


def post_json(endpoint: str, payload: dict[str, Any], api_key: str | None,
              client_timeout: float, attempts: int = 4) -> dict[str, Any]:
    """POST the payload; retry transient failures with exponential backoff."""
    # ensure_ascii=True escapes every non-ASCII character, so the transport
    # cannot mangle Lean's Unicode syntax whatever the local code page is.
    data = json.dumps(payload, ensure_ascii=True).encode("ascii")
    headers = {"Content-Type": "application/json", "Accept": "application/json"}
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"
    delay = 2.0
    for attempt in range(1, attempts + 1):
        request = urllib.request.Request(endpoint, data=data, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(request, timeout=client_timeout) as response:
                result = json.loads(response.read().decode("utf-8"))
            if not isinstance(result, dict):
                raise ValueError("the service did not return a JSON object")
            return result
        except urllib.error.HTTPError as exc:
            body = exc.read().decode("utf-8", errors="replace")
            if exc.code in RETRY_STATUSES and attempt < attempts:
                print(f"HTTP {exc.code}, retrying in {delay:.0f}s", file=sys.stderr)
                time.sleep(delay)
                delay *= 2
                continue
            raise RuntimeError(f"HTTP {exc.code}: {body[:1000]}") from exc
        except (urllib.error.URLError, TimeoutError) as exc:
            if attempt < attempts:
                print(f"{exc}, retrying in {delay:.0f}s", file=sys.stderr)
                time.sleep(delay)
                delay *= 2
                continue
            raise RuntimeError(str(exc)) from exc
    raise RuntimeError("unreachable")


def list_environments(endpoint: str, api_key: str | None) -> list[str]:
    """AXLE has no listing endpoint; an unknown environment name makes the
    service answer (HTTP 200) with a ``user_error`` that enumerates them."""
    result = post_json(endpoint, {"content": "", "environment": "lean-0.0.0",
                                  "timeout_seconds": 5}, api_key, 60)
    message = str(result.get("user_error", ""))
    match = re.search(r"Available environments:\s*(.*)", message)
    if not match:
        raise RuntimeError(f"unexpected answer: {json.dumps(result)[:500]}")
    return [name.strip() for name in match.group(1).split(",") if name.strip()]


def validate(result: dict[str, Any], theorem: str, allowed: set[str],
             sent_content: str, expect_echo: bool) -> tuple[list[str], list[str] | None]:
    """Return (problems, axioms).  An empty problem list is a PASS."""
    problems: list[str] = []
    if "user_error" in result:
        return [f"service rejected the request: {result['user_error']}"], None
    lean = result.get("lean_messages") or {}
    tool = result.get("tool_messages") or {}
    if result.get("okay") is not True:
        problems.append("okay is not true (Lean reported errors)")
    if result.get("failed_declarations") != []:
        problems.append(f"failed declarations: {result.get('failed_declarations')}")
    if lean.get("errors"):
        problems.append(f"{len(lean['errors'])} Lean error(s)")
    if tool.get("errors"):
        problems.append(f"service errors: {tool['errors']}")
    sorries = [w for w in lean.get("warnings", []) if SORRY_WARNING in w]
    if sorries:
        problems.append(f"{len(sorries)} declaration(s) use sorry (possibly anonymous examples)")
    infos = "\n".join(str(m) for m in lean.get("infos", []))
    match = re.search(AXIOMS_RE.format(theorem=re.escape(theorem)), infos)
    axioms: list[str] | None = None
    if match:
        axioms = sorted(a.strip() for a in match.group(1).split(",") if a.strip())
        extra = set(axioms) - allowed
        if extra:
            problems.append(f"disallowed axioms in {theorem}: {sorted(extra)}")
    elif re.search(NO_AXIOMS_RE.format(theorem=re.escape(theorem)), infos):
        axioms = []  # Lean's wording when the axiom list is empty
    else:
        problems.append(f"no '#print axioms {theorem}' output found (audit missing or the "
                        "theorem did not elaborate)")
    echoed = result.get("content")
    if expect_echo and isinstance(echoed, str) and echoed.strip() != sent_content.strip():
        problems.append("the service processed different content than was sent "
                        "(import header replaced? compare 'content' in the receipt)")
    return problems, axioms


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("source", nargs="?", type=Path, help="Lean file to check")
    parser.add_argument("--environment", default=DEFAULT_ENVIRONMENT,
                        help=f"AXLE environment name (default {DEFAULT_ENVIRONMENT}; "
                             "see --list-environments)")
    parser.add_argument("--endpoint", default=DEFAULT_ENDPOINT)
    parser.add_argument("--timeout", type=float, default=120,
                        help="server-side timeout_seconds (default 120, service cap 900)")
    parser.add_argument("--theorem", metavar="NAME",
                        help="declaration whose axiom report is checked (default: the "
                             "'#print axioms NAME' found in the audit text)")
    parser.add_argument("--allowed-axiom", action="append", metavar="NAME",
                        help="allowed axiom (repeatable; default propext, Classical.choice, "
                             "Quot.sound)")
    audit = parser.add_mutually_exclusive_group()
    audit.add_argument("--audit", type=Path, metavar="FILE",
                       help="Lean text to append (default: checks/Axioms.lean found above "
                            "the source, minus its import line; else '#print axioms')")
    audit.add_argument("--no-audit", action="store_true", help="append nothing")
    parser.add_argument("--ignore-imports", action="store_true",
                        help="let AXLE replace the header by its cached 'import Mathlib' "
                             "(faster, but does not test the file's own imports)")
    parser.add_argument("--output", type=Path, metavar="FILE",
                        help="receipt JSON (default: <source>.axle.json)")
    parser.add_argument("--prepare-local", type=Path, metavar="FILE",
                        help="write source+audit to FILE for 'lake env lean' and exit; "
                             "nothing is sent")
    parser.add_argument("--list-environments", action="store_true",
                        help="print the environment names the service accepts and exit")
    parser.add_argument("--quiet", action="store_true", help="print only the verdict line")
    args = parser.parse_args()
    api_key = os.environ.get("AXLE_API_KEY") or None

    try:
        if args.list_environments:
            print("\n".join(list_environments(args.endpoint, api_key)))
            return 0
        if args.source is None:
            parser.error("a source file is required")
        if args.timeout <= 0 or args.timeout > 900:
            parser.error("--timeout must be in (0, 900]")
        raw = args.source.read_bytes()
        source = raw.decode("utf-8")
        if args.no_audit:
            audit_text, audit_origin = "", "none"
        elif args.audit:
            audit_text, audit_origin = args.audit.read_text(encoding="utf-8"), str(args.audit)
        else:
            checks = find_repo_audit(args.source)
            if checks:
                audit_text, audit_origin = audit_from_checks_file(checks), str(checks)
            elif args.theorem:
                audit_text, audit_origin = default_audit(args.theorem), "built-in"
            else:
                parser.error("no checks/Axioms.lean found near the source: give --theorem "
                             "NAME or --audit FILE")
        if not args.theorem:
            printed = re.search(r"^#print axioms\s+([\w'.]+)", audit_text, re.M)
            if not printed:
                parser.error("the audit text prints no axioms: give --theorem NAME")
            args.theorem = printed.group(1)
        content = source.rstrip("\n") + "\n\n" + audit_text if audit_text else source
        if args.prepare_local:
            if args.prepare_local.resolve() == args.source.resolve():
                parser.error("--prepare-local must not overwrite the source")
            args.prepare_local.write_text(content, encoding="utf-8", newline="\n")
            print(f"wrote {args.prepare_local} (audit: {audit_origin}); check it with "
                  f"'lake env lean {args.prepare_local.name}' inside the Lean project")
            return 0

        payload = {
            "content": content,
            "environment": args.environment,
            "ignore_imports": bool(args.ignore_imports),
            "theorems_only": False,
            "timeout_seconds": args.timeout,
        }
        if not args.quiet:
            print(f"submitting {args.source} ({len(raw)} bytes) + audit [{audit_origin}] "
                  f"to {args.endpoint} in {args.environment}")
        started = time.monotonic()
        result = post_json(args.endpoint, payload, api_key, args.timeout + 90)
        elapsed = time.monotonic() - started
    except (OSError, UnicodeError, ValueError, RuntimeError) as exc:
        print(f"could not complete the check: {exc}", file=sys.stderr)
        return 2

    allowed = set(args.allowed_axiom or DEFAULT_ALLOWED_AXIOMS)
    problems, axioms = validate(result, args.theorem, allowed, content,
                                expect_echo=not args.ignore_imports)
    info = result.get("info") or {}
    lean = result.get("lean_messages") or {}
    tool = result.get("tool_messages") or {}
    version = next((m.split("info:")[-1].strip() for m in lean.get("infos", [])
                    if "Lean.versionString" in audit_text and '"4.' in m), None)
    receipt = {
        "source": str(args.source),
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "content_sha256": hashlib.sha256(content.encode("utf-8")).hexdigest(),
        "endpoint": args.endpoint,
        "request": {k: v for k, v in payload.items() if k != "content"},
        "audit": audit_text,
        "verdict": "PASS" if not problems else "FAIL",
        "problems": problems,
        "axioms": axioms,
        "lean_version_reported": version,
        "request_id": info.get("request_id"),
        "cached_response": info.get("cached_response"),
        "executor": {k: v for k, v in info.items() if k.startswith("_executor")},
        "client_elapsed_s": round(elapsed, 1),
        "response": result,
    }
    output = args.output or args.source.with_name(args.source.name + ".axle.json")
    try:
        output.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n",
                          encoding="utf-8")
    except OSError as exc:
        print(f"could not write the receipt: {exc}", file=sys.stderr)

    print(f"{receipt['verdict']}: {args.source} in {args.environment} "
          f"(request {info.get('request_id')}, {elapsed:.1f}s"
          f"{', cached' if info.get('cached_response') else ''}); receipt {output}")
    if not args.quiet:
        if axioms is not None:
            print(f"axioms of {args.theorem}: {axioms}")
        if version:
            print(f"Lean reported: {version}")
        for label, messages in (("Lean error", lean.get("errors", [])),
                                ("Lean warning", lean.get("warnings", [])),
                                ("service error", tool.get("errors", [])),
                                ("service warning", tool.get("warnings", [])),
                                ("service info", tool.get("infos", []))):
            for message in messages:
                print(f"{label}: {str(message).rstrip()}")
    for problem in problems:
        print(f"problem: {problem}", file=sys.stderr)
    return 0 if not problems else 1


if __name__ == "__main__":
    raise SystemExit(main())
