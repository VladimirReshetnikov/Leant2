#!/usr/bin/env python3
"""Submit either Leant2 experiment unchanged and audit every #print axioms result.

Requires Python 3.9+ and network access. Writes a complete response receipt.
This wrapper was syntax-checked, not network-executed in the document build.
The reported Lean runs used the same request settings via a Wolfram connector.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any


def expected_audits(source: str) -> list[str]:
    """Handle the single explicit namespace used by each distributed experiment."""
    namespaces = re.findall(r"^namespace\s+([\w.]+)\s*$", source, re.MULTILINE)
    if len(namespaces) != 1:
        raise ValueError("This artifact wrapper requires exactly one namespace command.")
    namespace = namespaces[0]
    short_names = re.findall(r"^#print axioms\s+([\w.]+)\s*$", source, re.MULTILINE)
    if not short_names:
        raise ValueError("No explicit axiom audits were found in the source.")
    return [n if n.startswith(namespace + ".") else namespace + "." + n for n in short_names]


def validate(response: dict[str, Any], source: str, names: list[str],
             allowed: set[str]) -> tuple[list[str], dict[str, list[str]]]:
    problems: list[str] = []
    if "user_error" in response:
        problems.append(f"Service rejected the request: {response['user_error']}")
    if response.get("okay") is not True:
        problems.append("okay is not true")
    if response.get("failed_declarations") != []:
        problems.append(f"failed_declarations: {response.get('failed_declarations')}")
    lean = response.get("lean_messages", {})
    tool = response.get("tool_messages", {})
    for label, messages in (("Lean", lean), ("Service", tool)):
        errors = messages.get("errors", [])
        if errors:
            problems.append(f"{label} errors: {errors}")
    warnings = lean.get("warnings", [])
    if any("sorry" in warning.lower() for warning in warnings):
        problems.append("Lean emitted a sorry-related warning")
    echo = response.get("content")
    if not isinstance(echo, str) or echo.strip() != source.strip():
        problems.append("Processed source differs from the submitted source after whitespace trim")
    infos = "\n".join(lean.get("infos", []))
    found: dict[str, list[str]] = {}
    for name in names:
        empty = f"'{name}' does not depend on any axioms"
        match = re.search(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", infos)
        if match:
            axioms = [s.strip() for s in match.group(1).split(",") if s.strip()]
        elif empty in infos:
            axioms = []
        else:
            problems.append(f"Missing axiom report for {name}")
            continue
        found[name] = axioms
        if set(axioms) - allowed:
            problems.append(f"Disallowed axioms in {name}: {sorted(set(axioms) - allowed)}")
    return problems, found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--environment", default="lean-4.34.0")
    parser.add_argument("--endpoint", default="https://axle.axiommath.ai/api/v1/check")
    parser.add_argument("--timeout", type=float, default=40)
    parser.add_argument("--allowed-axiom", action="append", default=None,
                        help="Repeat to override the default allowance of propext only.")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        raw = args.source.read_bytes()
        source = raw.decode("utf-8")
        names = expected_audits(source)
        allowed = set(args.allowed_axiom if args.allowed_axiom is not None else ["propext"])
        body = {"content": source, "environment": args.environment,
                "ignore_imports": False, "theorems_only": False,
                "timeout_seconds": args.timeout}
        encoded = json.dumps(body, ensure_ascii=True).encode("utf-8")
        headers = {"Content-Type": "application/json; charset=utf-8"}
        key = os.environ.get("AXLE_API_KEY")
        if key:
            headers["Authorization"] = "Bearer " + key
        request = urllib.request.Request(args.endpoint, data=encoded, headers=headers, method="POST")
        with urllib.request.urlopen(request, timeout=args.timeout + 90) as reply:
            status = reply.status
            response = json.loads(reply.read().decode("utf-8"))
        if not isinstance(response, dict):
            raise ValueError("The response is not a JSON object")
        problems, axioms = validate(response, source, names, allowed)
        if status != 200:
            problems.append(f"HTTP status {status}")
        receipt = {
            "kind": "complete response from this script's own network run",
            "source": str(args.source),
            "source_sha256": hashlib.sha256(raw).hexdigest(),
            "environment": args.environment,
            "request_settings": {k: v for k, v in body.items() if k != "content"},
            "http_status": status,
            "expected_audits": names,
            "allowed_axioms": sorted(allowed),
            "axioms": axioms,
            "verdict": "PASS" if not problems else "FAIL",
            "problems": problems,
            "response": response,
        }
        output = args.output or args.source.with_suffix(".axle.json")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"{receipt['verdict']}: {args.source}; {len(axioms)} axiom audits; receipt {output}")
        for problem in problems:
            print(problem, file=sys.stderr)
        return int(bool(problems))
    except (OSError, UnicodeError, ValueError, urllib.error.URLError) as exc:
        print(f"Check could not be completed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
