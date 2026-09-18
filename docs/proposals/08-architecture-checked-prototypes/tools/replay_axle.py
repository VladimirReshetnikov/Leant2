#!/usr/bin/env python3
"""Replay the three supplied Lean experiments against AXLE.

Uses only Python's standard library. This is an experiment utility, not a
Leant2 frontend. Full HTTP responses are saved before validation. No claim of
independent kernel checking is made. Network/service failures fail the replay.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import re
import sys
import time
import urllib.error
import urllib.request
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
URL = "https://axle.axiommath.ai/api/v1/check"
EXPECTED: dict[str, dict[str, list[str]]] = {
    "NativeSearch.lean": {
        **{f"Leant2Prototype.{name}": [] for name in (
            "double", "dependentApply", "identity", "compose", "swap",
            "distribute", "dependentPair", "singleton", "preserveDictionary",
            "polymorphicArgument", "singleton_spec", "polymorphic_spec")},
        "Leant2Prototype.vectorHead": ["propext"],
    },
    "FiniteCegis.lean": {
        "Leant2Finite.verify_sound": ["propext"],
        "Leant2Finite.all_found": ["propext"],
        "Leant2Finite.all_correct": ["propext"],
        "Leant2Finite.generatedXor": [],
        "Leant2Finite.generatedXor_correct": [],
    },
    "CertifiedFold.lean": {
        f"Leant2Fold.{name}": [] for name in (
            "fold_contract", "certifiedRecursor", "indexFold",
            "indexFold_correct", "noUniversalValue", "noUniformConversion")
    },
}


def _messages(payload: dict[str, Any], group: str, kind: str) -> list[str]:
    value = payload.get(group)
    if not isinstance(value, dict):
        raise ValueError(f"Missing or malformed message group: {group}")
    result = value.get(kind)
    if not isinstance(result, list) or any(not isinstance(x, str) for x in result):
        raise ValueError(f"Missing or malformed messages: {group}.{kind}")
    return result


def validate_response(payload: dict[str, Any], source: str,
                      expected: dict[str, list[str]], environment: str) -> dict[str, Any]:
    """Strict checks for these fixed experiments, including exact axiom sets."""
    if payload.get("okay") is not True:
        raise ValueError("AXLE did not report okay=true")
    if payload.get("failed_declarations") != []:
        raise ValueError("Nonempty or missing failed_declarations")
    if not isinstance(payload.get("content"), str):
        raise ValueError("Missing source echo")
    if payload["content"].strip() != source.strip():
        raise ValueError("Source changed (including possible import replacement)")
    for group in ("lean_messages", "tool_messages"):
        if _messages(payload, group, "errors"):
            raise ValueError(f"{group} contains errors")
        warnings = _messages(payload, group, "warnings")
        if any(re.search(r"\bsorry\b|\bsorryAx\b|\bincomplete\b", x, re.I)
               for x in warnings):
            raise ValueError(f"{group} reports incomplete/sorried code")
    infos = "\n".join(_messages(payload, "lean_messages", "infos"))
    checked: dict[str, list[str]] = {}
    for name, allowed in expected.items():
        pattern = (r"'" + re.escape(name) +
                   r"' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])")
        matches = list(re.finditer(pattern, infos))
        if len(matches) != 1:
            raise ValueError(f"Expected one axiom inventory for {name}; found {len(matches)}")
        raw = matches[0].group(1)
        actual = [] if raw is None or not raw.strip() else [x.strip() for x in raw.split(",")]
        if set(actual) != set(allowed):
            raise ValueError(f"Axiom mismatch for {name}: {actual}; expected {allowed}")
        checked[name] = actual
    info = payload.get("info")
    if not isinstance(info, dict) or info.get("environment") != environment:
        raise ValueError("Missing or different environment identity")
    version = environment.removeprefix("lean-")
    if f'info: "{version}"' not in infos:
        raise ValueError("Lean version output does not match requested environment")
    return {"passed": True, "axioms": checked, "request_id": info.get("request_id"),
            "environment": environment, "source_echo_match_trimmed": True,
            "timings": payload.get("timings"), "service_info": info,
            "warnings": {g: _messages(payload, g, "warnings")
                         for g in ("lean_messages", "tool_messages")}}


def post(payload: dict[str, Any], timeout: float) -> dict[str, Any]:
    data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    headers = {"Content-Type": "application/json", "User-Agent": "Leant2-prototype-replay/1"}
    key = os.getenv("AXLE_API_KEY")
    if key:
        headers["Authorization"] = f"Bearer {key}"
    for attempt in range(3):
        try:
            req = urllib.request.Request(URL, data=data, headers=headers, method="POST")
            with urllib.request.urlopen(req, timeout=timeout + 30) as response:
                raw = response.read(16 * 1024 * 1024 + 1)
            if len(raw) > 16 * 1024 * 1024:
                raise ValueError("Response exceeds 16 MiB limit")
            result = json.loads(raw.decode("utf-8"))
            if not isinstance(result, dict):
                raise ValueError("Expected a JSON object")
            return result
        except urllib.error.HTTPError as exc:
            if exc.code not in (429, 502, 503, 504) or attempt == 2:
                raise
            time.sleep(2 ** attempt)
    raise RuntimeError("Unreachable retry state")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("fresh-receipts"),
                        help="New directory; existing directories are refused")
    parser.add_argument("--environment", default="lean-4.34.0")
    parser.add_argument("--timeout", type=float, default=45.0)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 900:
        parser.error("--timeout must be between 1 and 900 seconds")
    args.output.mkdir(parents=True, exist_ok=False)
    summary: dict[str, Any] = {
        "kind": "fresh-remote-replay", "service": "AXLE", "url": URL,
        "time_utc": dt.datetime.now(dt.timezone.utc).isoformat(), "results": {}}
    failures = 0
    for filename, expected in EXPECTED.items():
        try:
            source = (ROOT / "lean" / filename).read_text(encoding="utf-8")
            request = {"content": source, "environment": args.environment,
                       "ignore_imports": False, "theorems_only": False,
                       "timeout_seconds": args.timeout}
            response = post(request, args.timeout)
            (args.output / f"{filename}.response.json").write_text(
                json.dumps(response, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
            result = validate_response(response, source, expected, args.environment)
            summary["results"][filename] = result
            print(f"PASS {filename}: {result['request_id']}")
        except (OSError, ValueError, RuntimeError) as exc:
            failures += 1
            summary["results"][filename] = {"passed": False, "error": str(exc)}
            print(f"FAIL {filename}: {exc}", file=sys.stderr)
    summary["passed"] = failures == 0
    (args.output / "summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return int(failures != 0)


if __name__ == "__main__":
    raise SystemExit(main())
