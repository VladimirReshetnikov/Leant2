#!/usr/bin/env python3
"""Replay an exact Lean source through AXLE and retain the complete response.

Python 3.9+, standard library only. This is a reproduction helper, not an
independent Lean kernel. Its offline assessment routine is regression tested.
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
from typing import Any, Dict, List, Mapping, Optional

ENDPOINT = "https://axle.axiommath.ai/api/v1/check"


def assess(source: str, response: Mapping[str, Any],
           expected_axioms: Optional[Mapping[str, List[str]]] = None,
           expected_compiler_error: Optional[str] = None) -> Dict[str, Any]:
    """Inspect exact-source integrity, compilation, admissions, and axiom reports."""
    problems: List[str] = []
    lean = response.get("lean_messages", {}) or {}
    tool = response.get("tool_messages", {}) or {}
    errors = list(lean.get("errors", []) or [])
    warnings = list(lean.get("warnings", []) or [])
    infos = "\n".join(lean.get("infos", []) or [])
    if response.get("user_error"):
        problems.append(str(response["user_error"]))
    echo = response.get("content")
    if not isinstance(echo, str) or echo.rstrip("\r\n") != source.rstrip("\r\n"):
        problems.append("Echoed source differs (apart from trailing newlines).")
    if tool.get("errors"):
        problems.extend(str(e) for e in tool["errors"])
    if any("sorry" in str(w).lower() for w in warnings):
        problems.append("Lean warning mentions sorry; inspect for admitted proofs.")
    if response.get("failed_declarations"):
        problems.append("The service reports failed or incomplete declarations.")
    if expected_compiler_error is None:
        if response.get("okay") is not True:
            problems.append("Compilation did not succeed.")
        problems.extend(str(e) for e in errors)
    else:
        if response.get("okay") is not False:
            problems.append("Expected compiler rejection did not occur.")
        if not errors or not all(expected_compiler_error in str(e) for e in errors):
            problems.append("Errors do not match the specific expected compiler rejection.")
    observed: Dict[str, List[str]] = {}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", infos):
        observed[name] = []
    for name, raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", infos):
        observed[name] = sorted(x.strip() for x in raw.split(",") if x.strip())
    for name, allowed in (expected_axioms or {}).items():
        if name not in observed:
            problems.append(f"Missing axiom report: {name}")
        elif observed[name] != sorted(allowed):
            problems.append(f"Changed axiom inventory for {name}: {observed[name]}")
    return {"pass": not problems, "problems": problems,
            "observed_axioms": observed,
            "lean_warnings": warnings, "tool_warnings": tool.get("warnings", []),
            "expected_compiler_rejection": expected_compiler_error is not None}


def request_check(payload: Mapping[str, Any], endpoint: str, timeout: float) -> Dict[str, Any]:
    data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    headers = {"Content-Type": "application/json"}
    if os.environ.get("AXLE_API_KEY"):
        headers["Authorization"] = "Bearer " + os.environ["AXLE_API_KEY"]
    for attempt in range(3):
        try:
            req = urllib.request.Request(endpoint, data=data, headers=headers, method="POST")
            with urllib.request.urlopen(req, timeout=timeout) as handle:
                result = json.load(handle)
            if not isinstance(result, dict):
                raise ValueError("AXLE did not return a JSON object.")
            return result
        except urllib.error.HTTPError as exc:
            if exc.code not in (429, 502, 503, 504) or attempt == 2:
                raise
            time.sleep(2 ** attempt)
    raise RuntimeError("Retry loop ended unexpectedly.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--environment", default="lean-4.34.0")
    parser.add_argument("--endpoint", default=ENDPOINT)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--axiom-profile", type=Path,
                        help="JSON map from fully qualified declaration names to exact axiom lists")
    parser.add_argument("--expect-compiler-error", metavar="SUBSTRING",
                        help="Use only for the intentional compiler-boundary negative probe")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    try:
        source = args.source.read_text(encoding="utf-8")
        profile = json.loads(args.axiom_profile.read_text(encoding="utf-8")) if args.axiom_profile else None
        if profile is not None and (not isinstance(profile, dict) or
            not all(isinstance(k, str) and isinstance(v, list) and
                    all(isinstance(a, str) for a in v) for k, v in profile.items())):
            raise ValueError("Axiom profile must map strings to lists of strings.")
        payload = {"content": source, "environment": args.environment,
                   "ignore_imports": False, "theorems_only": False,
                   "timeout_seconds": args.timeout}
        response = request_check(payload, args.endpoint, args.timeout + 90)
        verdict = assess(source, response, profile, args.expect_compiler_error)
        receipt = {"source_path": str(args.source),
                   "source_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
                   "request": payload, "assessment": verdict, "response": response,
                   "limitation": "Remote compilation and report audit; not independent kernel replay."}
        output = args.output or args.source.with_suffix(".axle.full.json")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print("PASS" if verdict["pass"] else "FAIL")
        print(f"Receipt: {output}")
        for problem in verdict["problems"]:
            print(problem, file=sys.stderr)
        return 0 if verdict["pass"] else 1
    except (OSError, ValueError, urllib.error.URLError) as exc:
        print(f"Check could not be completed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
