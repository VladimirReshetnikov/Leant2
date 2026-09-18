#!/usr/bin/env python3
"""Submit an audited standalone Lean file to AXLE and retain a full JSON receipt.

Python 3.10+, standard library only. This runner sends the specified source to
an external service. It never replaces imports, inserts axioms, or appends a
proof. The source must already contain its own run_cmd axiom audit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import time
import urllib.error
import urllib.request

DEFAULT_ENDPOINT = "https://axle.axiommath.ai/api/v1/check"


def validate_response(source: str, result: dict, marker: str) -> list[str]:
    problems: list[str] = []
    if result.get("user_error"):
        problems.append(f"Service rejected request: {result['user_error']}")
    if result.get("okay") is not True:
        problems.append("The service did not report successful compilation.")
    if result.get("failed_declarations") != []:
        problems.append(f"Failed or incomplete declarations: {result.get('failed_declarations')!r}")
    for category in ("lean_messages", "tool_messages"):
        messages = result.get(category)
        if not isinstance(messages, dict):
            problems.append(f"Missing {category} object.")
            continue
        errors = messages.get("errors")
        if errors != []:
            problems.append(f"{category} errors: {errors!r}")
        warnings = messages.get("warnings", [])
        if any("sorry" in str(warning).lower() or "incomplete" in str(warning).lower()
               for warning in warnings):
            problems.append(f"{category} warns about an incomplete/sorry declaration.")
    infos = "\n".join(map(str, result.get("lean_messages", {}).get("infos", [])))
    if marker not in infos or "standard-axiom audit passed" not in infos:
        problems.append("Expected completed source audit marker is missing.")
    if "sorryAx" in infos:
        problems.append("An axiom report mentions sorryAx.")
    reports = re.findall(r"AXIOMS\s+(\S+):\s*\[([^\]]*)\]", infos)
    if not reports:
        problems.append("No per-declaration axiom reports were returned.")
    allowed = {"propext", "Quot.sound", "Classical.choice"}
    for name, entries in reports:
        actual = {entry.strip() for entry in entries.split(",") if entry.strip()}
        if actual - allowed:
            problems.append(f"Unexpected axioms for {name}: {sorted(actual - allowed)}")
    echo = result.get("content")
    # This exact extra terminal newline was observed in the actual service.
    if echo not in (source, source + "\n"):
        problems.append("Processed source differs by more than one appended terminal newline.")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--audit-marker", required=True,
                        help="For example LEANT2_AUDIT: or LEANT2_RECURSION_AUDIT:")
    parser.add_argument("--environment", default="lean-4.34.0")
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--endpoint", default=DEFAULT_ENDPOINT)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.timeout <= 0 or args.timeout > 900:
        parser.error("timeout must be in (0, 900]")
    try:
        raw = args.source.read_bytes()
        source = raw.decode("utf-8")
    except (OSError, UnicodeError) as exc:
        print(f"Cannot read UTF-8 source: {exc}", file=sys.stderr)
        return 2
    payload = {"content": source, "environment": args.environment,
               "ignore_imports": False, "theorems_only": False,
               "timeout_seconds": args.timeout}
    headers = {"Content-Type": "application/json", "User-Agent": "Leant2-research-check/1"}
    if os.environ.get("AXLE_API_KEY"):
        headers["Authorization"] = "Bearer " + os.environ["AXLE_API_KEY"]
    request = urllib.request.Request(args.endpoint, json.dumps(payload).encode("utf-8"),
                                     headers, method="POST")
    result = None
    for attempt in range(3):
        try:
            with urllib.request.urlopen(request, timeout=args.timeout + 90) as response:
                result = json.load(response)
            break
        except urllib.error.HTTPError as exc:
            if exc.code in (429, 502, 503, 504) and attempt < 2:
                time.sleep(2 ** attempt)
                continue
            print(f"HTTP error: {exc}", file=sys.stderr)
            return 2
        except (OSError, ValueError) as exc:
            print(f"Check not performed: {exc}", file=sys.stderr)
            return 2
    if not isinstance(result, dict):
        print("Check did not return a JSON object.", file=sys.stderr)
        return 2
    problems = validate_response(source, result, args.audit_marker)
    receipt = {"source_path": str(args.source), "source_sha256": hashlib.sha256(raw).hexdigest(),
               "source_bytes": len(raw), "request": {k: v for k, v in payload.items() if k != "content"},
               "verdict": "PASS" if not problems else "FAIL", "problems": problems,
               "response": result}
    output = args.output or args.source.with_suffix(".axle.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(receipt["verdict"], output)
    for problem in problems:
        print("  " + problem)
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
