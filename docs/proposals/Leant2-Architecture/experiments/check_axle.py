#!/usr/bin/env python3
"""Submit one of the standalone Lean experiments to AXLE and audit its reply.

Uses only Python's standard library. A successful HTTP request or `okay` flag
alone does not count as a successful proof check. This is a reproducibility
client, not an independently verified Lean checker.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

ENDPOINT = 'https://axle.axiommath.ai/api/v1/check'
EXPECTED: dict[str, set[str]] = {
    'Prototype.lean': {f'Leant2Prototype.{name}' for name in (
        'identity', 'compose', 'dependentApply', 'dependentPair', 'higherRank',
        'swap', 'sumElim', 'vectorHead', 'vectorTail', 'coupledWitness',
        'dictionary', 'conjunction', 'impossibleFunction')},
    'SkeletonChecks.lean': {f'Leant2Prototype.{name}' for name in (
        'vectorMap', 'vectorMap_nil', 'vectorMap_cons')},
    'ReverseCertificate.lean': {f'Leant2Certificate.{name}' for name in (
        'generatedReverse', 'foldInvariant', 'generatedReverse_correct')},
}


def validate_reply(reply: dict[str, Any], source: str,
                   expected: set[str], allowed: set[str]) -> list[str]:
    problems: list[str] = []
    if reply.get('okay') is not True:
        problems.append('AXLE did not report okay=true.')
    if reply.get('failed_declarations'):
        problems.append(f"Failed declarations: {reply['failed_declarations']!r}")
    echo = reply.get('content')
    if not isinstance(echo, str) or echo.strip() != source.strip():
        problems.append('Returned source does not match after outer-whitespace trimming.')
    messages = reply.get('lean_messages', {})
    if not isinstance(messages, dict):
        return problems + ['Missing or malformed Lean diagnostics.']
    if messages.get('errors'):
        problems.append(f"Lean errors: {messages['errors']!r}")
    tool_messages = reply.get('tool_messages', {})
    if isinstance(tool_messages, dict) and tool_messages.get('errors'):
        problems.append(f"Service errors: {tool_messages['errors']!r}")
    warnings = '\n'.join(str(x) for x in messages.get('warnings', []))
    if re.search(r'\bsorry\b|sorryAx', warnings):
        problems.append('Lean warnings report an incomplete/sorry declaration.')
    found: dict[str, set[str]] = {}
    for line in messages.get('infos', []):
        line = str(line)
        empty = re.search(r"'([^']+)' does not depend on any axioms", line)
        nonempty = re.search(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", line)
        if empty:
            found[empty.group(1)] = set()
        elif nonempty:
            found[nonempty.group(1)] = {x.strip() for x in nonempty.group(2).split(',')
                                       if x.strip()}
    for name in sorted(expected):
        if name not in found:
            problems.append(f'Missing axiom audit for {name}.')
    for name, axioms in sorted(found.items()):
        forbidden = axioms - allowed
        if forbidden:
            problems.append(f'{name} uses unapproved axioms: {sorted(forbidden)}.')
    if not expected:
        problems.append('No expected declarations specified; refusing a vacuous audit.')
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--environment', default='lean-4.34.0')
    parser.add_argument('--timeout', type=int, default=50,
                        help='Server timeout in seconds; the client permits 20 extra seconds.')
    parser.add_argument('--allow-axiom', action='append', default=None,
                        help='Repeat for allowed axioms. Default: propext only.')
    parser.add_argument('--empty-axioms', action='store_true',
                        help='Reject all axiom dependencies, including propext.')
    parser.add_argument('--expect', action='append', default=None,
                        help='Override the known file audit list with fully qualified declarations.')
    args = parser.parse_args()
    if not 1 <= args.timeout <= 120:
        parser.error('--timeout must be between 1 and 120 seconds.')
    expected = set(args.expect) if args.expect else EXPECTED.get(args.source.name, set())
    if not expected:
        parser.error('Unknown source filename: supply at least one --expect declaration.')
    allowed = set() if args.empty_axioms else set(args.allow_axiom or ['propext'])
    try:
        source = args.source.read_text(encoding='utf-8')
    except (OSError, UnicodeError) as exc:
        print(f'Cannot read source: {exc}', file=sys.stderr)
        return 2
    payload = {'content': source, 'environment': args.environment,
               'ignore_imports': False, 'theorems_only': False,
               'timeout_seconds': args.timeout}
    request = urllib.request.Request(
        ENDPOINT, data=json.dumps(payload, ensure_ascii=False).encode('utf-8'),
        headers={'Content-Type': 'application/json'}, method='POST')
    try:
        with urllib.request.urlopen(request, timeout=args.timeout + 20) as response:
            status = response.status
            reply = json.loads(response.read().decode('utf-8'))
    except (OSError, urllib.error.URLError, json.JSONDecodeError) as exc:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({'client_error': str(exc)}, indent=2) + '\n',
                               encoding='utf-8')
        print(f'Check request failed: {exc}', file=sys.stderr)
        return 2
    if not isinstance(reply, dict):
        print('Service returned a non-object JSON value.', file=sys.stderr)
        return 2
    problems = validate_reply(reply, source, expected, allowed)
    if status != 200:
        problems.insert(0, f'Unexpected HTTP status: {status}')
    record = {'http_status': status, 'source_path': str(args.source),
              'audit': {'passed': not problems, 'problems': problems,
                        'allowed_axioms': sorted(allowed), 'expected': sorted(expected)},
              'response': reply}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, ensure_ascii=False) + '\n',
                           encoding='utf-8')
    print('Audit passed.' if not problems else '\n'.join(problems))
    print(f'Full receipt: {args.output}')
    return 0 if not problems else 1


if __name__ == '__main__':
    raise SystemExit(main())
