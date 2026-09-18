#!/usr/bin/env python3
"""Submit an existing Lean file to AXLE; retain the full HTTP JSON response.

Standard library only. This is a conservative response/audit client for honest
source and service responses, NOT a sandbox or an independent Lean checker.
The local response-audit unit tests were run; HTTP in this session used Wolfram.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import re
import sys
import time
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

ENDPOINT = 'https://axle.axiommath.ai/api/v1/check'
EMPTY_AUDIT = re.compile(r"'([^']+)' does not depend on any axioms")
AXIOM_AUDIT = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")


def audit_response(response: dict[str, Any], source: str,
                   expected_axioms: dict[str, list[str]],
                   environment: str) -> dict[str, Any]:
    problems: list[str] = []
    if response.get('okay') is not True:
        problems.append('Compilation was not explicitly successful.')
    if response.get('user_error'):
        problems.append('Service rejected the request: ' + str(response['user_error']))
    if response.get('failed_declarations'):
        problems.append('Failed declarations: ' + str(response['failed_declarations']))
    messages = response.get('lean_messages', {})
    tool_messages = response.get('tool_messages', {})
    if messages.get('errors') or tool_messages.get('errors'):
        problems.append('Lean or service errors are present.')
    processed = response.get('content')
    if not isinstance(processed, str) or processed.rstrip() != source.rstrip():
        problems.append('Returned source is missing or changed beyond final whitespace.')
    if response.get('info', {}).get('environment') != environment:
        problems.append('Returned environment does not match the request.')
    warnings = list(messages.get('warnings', [])) + list(tool_messages.get('warnings', []))
    if any('sorry' in str(w).lower() or 'incomplete' in str(w).lower() for w in warnings):
        problems.append('Incomplete-proof warning is present.')
    reports: dict[str, list[list[str]]] = {}
    for info in messages.get('infos', []):
        for name in EMPTY_AUDIT.findall(str(info)):
            reports.setdefault(name, []).append([])
        for name, body in AXIOM_AUDIT.findall(str(info)):
            reports.setdefault(name, []).append([x.strip() for x in body.split(',') if x.strip()])
    if not expected_axioms:
        problems.append('No expected declaration audit manifest was supplied.')
    for name, allowed in expected_axioms.items():
        found = reports.get(name, [])
        if len(found) != 1:
            problems.append(f'{name}: expected exactly one axiom report, got {len(found)}.')
        elif set(found[0]) - set(allowed):
            problems.append(f'{name}: disallowed axioms: {sorted(set(found[0]) - set(allowed))}')
    return {'accepted_by_response_audit': not problems, 'problems': problems,
            'reported_axioms': reports, 'warnings': warnings,
            'scope': 'Only declarations named in the supplied manifest are audited. '
                     'Assumes honest source/logs/service; no independent kernel replay.'}


def submit(source: str, environment: str, timeout: float) -> dict[str, Any]:
    payload = {'content': source, 'environment': environment, 'ignore_imports': False,
               'theorems_only': False, 'timeout_seconds': timeout}
    headers = {'Content-Type': 'application/json', 'Accept': 'application/json'}
    key = os.environ.get('AXLE_API_KEY')
    if key:
        headers['Authorization'] = 'Bearer ' + key
    request = Request(ENDPOINT, data=json.dumps(payload, ensure_ascii=False).encode('utf-8'),
                      headers=headers, method='POST')
    for attempt in range(3):
        try:
            with urlopen(request, timeout=timeout + 30) as result:
                body = result.read(32 * 1024 * 1024 + 1)
            if len(body) > 32 * 1024 * 1024:
                raise ValueError('Response exceeds the client size limit.')
            response = json.loads(body.decode('utf-8'))
            if not isinstance(response, dict):
                raise ValueError('Expected a JSON object from AXLE.')
            return response
        except HTTPError as exc:
            if exc.code in {429, 502, 503, 504} and attempt < 2:
                time.sleep(2 ** attempt)
                continue
            raise
    raise RuntimeError('Unreachable retry state.')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--manifest', type=Path, required=True,
                        help='JSON object with expected_axioms mapping names to allowed lists')
    parser.add_argument('--output', type=Path, required=True,
                        help='New file for raw service response and client audit')
    parser.add_argument('--environment', default='lean-4.34.0')
    parser.add_argument('--timeout', type=float, default=40)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('Output already exists; choose a new path to preserve old receipts.')
    if not 0 < args.timeout <= 900:
        parser.error('Timeout must lie in (0, 900].')
    try:
        source = args.source.read_text(encoding='utf-8')
        manifest = json.loads(args.manifest.read_text(encoding='utf-8'))
        expected = manifest['expected_axioms']
        if not isinstance(expected, dict) or not all(
            isinstance(k, str) and isinstance(v, list) and all(isinstance(a, str) for a in v)
            for k, v in expected.items()
        ):
            raise ValueError('Invalid expected_axioms manifest.')
        response = submit(source, args.environment, args.timeout)
        audit = audit_response(response, source, expected, args.environment)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open('x', encoding='utf-8') as out:
            json.dump({'source_path': str(args.source), 'manifest_path': str(args.manifest),
                       'response': response, 'audit': audit}, out, indent=2, ensure_ascii=False)
            out.write('\n')
        print(json.dumps(audit, indent=2, ensure_ascii=False))
        return 0 if audit['accepted_by_response_audit'] else 1
    except (OSError, URLError, ValueError, KeyError) as exc:
        print(f'Check failed: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
