#!/usr/bin/env python3
"""Check a Lean source file through AXLE without replacing its imports.

Standard library only. This is a replay convenience, not an independent kernel.
Requires #print axioms directives unless --no-audit is explicitly selected.
The complete response is retained in the output JSON. Network access is needed.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any, Optional

ENDPOINT = "https://axle.axiommath.ai/api/v1/check"
AUDIT_DIRECTIVE = re.compile(r"^\s*#print\s+axioms\s+(\S+)\s*$", re.MULTILINE)
AUDIT_REPORT = re.compile(
    r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])"
)


def validate(source: str, response: dict[str, Any], allowed: set[str],
             require_audit: bool = True) -> dict[str, Any]:
    problems: list[str] = []
    if "user_error" in response:
        problems.append(f"Service rejected the request: {response['user_error']}")
    if response.get("okay") is not True:
        problems.append("Service did not report okay=true")
    if response.get("failed_declarations", []):
        problems.append(f"Failed declarations: {response['failed_declarations']}")
    lean = response.get("lean_messages", {})
    tool = response.get("tool_messages", {})
    for label, messages in (("Lean", lean), ("Service", tool)):
        if messages.get("errors", []):
            problems.append(f"{label} errors: {messages['errors']}")
    if any(re.search(r"declaration uses.*sorry", str(w), re.I)
           for w in lean.get("warnings", [])):
        problems.append("A declaration uses sorry")
    echoed = response.get("content")
    if not isinstance(echoed, str) or echoed.strip() != source.strip():
        problems.append("Echoed source differs beyond surrounding whitespace")
    reports: dict[str, list[str]] = {}
    for info in lean.get("infos", []):
        for match in AUDIT_REPORT.finditer(str(info)):
            names = [part.strip() for part in (match.group(2) or "").split(",")
                     if part.strip()]
            reports[match.group(1)] = names
    expected = AUDIT_DIRECTIVE.findall(source)
    if require_audit and not expected:
        problems.append("No #print axioms directives in source (use --no-audit explicitly)")
    for name in expected:
        matching = [full for full in reports if full == name or full.endswith("." + name)]
        if len(matching) != 1:
            problems.append(f"Expected exactly one axiom report for {name}: {matching}")
            continue
        disallowed = set(reports[matching[0]]) - allowed
        if disallowed:
            problems.append(f"Disallowed axioms for {name}: {sorted(disallowed)}")
    if any("sorryAx" in names for names in reports.values()):
        problems.append("An audited declaration depends on sorryAx")
    return {"passed": not problems, "problems": problems,
            "expected_axiom_reports": expected, "axiom_reports": reports}


def submit(request: dict[str, Any], timeout: float) -> dict[str, Any]:
    headers = {"Content-Type": "application/json"}
    key = os.environ.get("AXLE_API_KEY")
    if key:
        headers["Authorization"] = "Bearer " + key
    body = json.dumps(request, ensure_ascii=True).encode("utf-8")
    for attempt in range(3):
        try:
            req = urllib.request.Request(ENDPOINT, data=body, headers=headers, method="POST")
            with urllib.request.urlopen(req, timeout=timeout + 120) as result:
                value = json.loads(result.read().decode("utf-8"))
            if not isinstance(value, dict):
                raise ValueError("Expected a JSON object from AXLE")
            return value
        except urllib.error.HTTPError as error:
            if error.code not in (429, 502, 503, 504) or attempt == 2:
                raise
            time.sleep(2 ** attempt)
    raise RuntimeError("Unreachable retry state")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--environment", default="lean-4.34.0")
    parser.add_argument("--timeout", type=float, default=90)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--allowed-axiom", action="append", default=None,
                        help="Repeat to override default allowlist: propext, Quot.sound")
    parser.add_argument("--no-audit", action="store_true")
    parser.add_argument("--prepare-request", type=Path,
                        help="Write request JSON only; do not contact the service")
    args = parser.parse_args()
    if not 0 < args.timeout <= 900:
        parser.error("--timeout must be in (0, 900]")
    try:
        source = args.source.read_text(encoding="utf-8-sig")
        request = {"content": source, "environment": args.environment,
                   "ignore_imports": False, "theorems_only": False,
                   "timeout_seconds": args.timeout}
        output = args.prepare_request or args.output or args.source.with_suffix(".remote.json")
        if output.resolve() == args.source.resolve():
            raise ValueError("Output must not overwrite the Lean source")
        output.parent.mkdir(parents=True, exist_ok=True)
        if args.prepare_request:
            output.write_text(json.dumps(request, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
            print(f"Request written without execution: {output}")
            return 0
        response = submit(request, args.timeout)
        allowed = set(args.allowed_axiom if args.allowed_axiom is not None
                      else ["propext", "Quot.sound"])
        verdict = validate(source, response, allowed, not args.no_audit)
        receipt = {"source_file": str(args.source), "request": request,
                   "allowed_axioms": sorted(allowed), "validation": verdict,
                   "response": response}
        output.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(json.dumps(verdict, indent=2, ensure_ascii=False))
        print(f"Complete response saved to {output}")
        return 0 if verdict["passed"] else 1
    except (OSError, ValueError, urllib.error.URLError) as error:
        print(f"Remote check was not completed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
