"""Strict query boundaries and scoring shared by the secondary REPL harnesses.

The REPL can exit zero after Lean errors. Neither a printed candidate nor an
absent candidate is an outcome until its query completion marker is present.
"""
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess

QUERY_END = "-- leant2-query-end"
QUERY = re.compile(r"(?m)^λ> (:synth(?: .*)?)$")
ERROR = re.compile(r"(?im)^\s*(?:error(?:\([^)]*\))?:|PANIC|uncaught exception)")
SORRY = re.compile(r"declaration uses [`']sorry", re.I)
CANDIDATE = re.compile(r"(?m)^  it1(?:\s|$)")
NEGATIVES = {
    "contract_impossible": "provably no program satisfies the contract",
    "uninhabited": "provably uninhabited",
    "refuted": "program(s) of the type proposed, none passed the contract",
    "search_exhausted": "no term found within the search bounds",
    "budget_exhausted": "budget exhausted",
}
BOUNDED = {"refuted", "search_exhausted", "budget_exhausted"}


@dataclass
class QueryResult:
    command: str
    text: str
    outcome: str
    candidate: bool = False
    elapsed_ms: int | None = None
    first: str = ""


@dataclass
class SessionResult:
    queries: list[QueryResult]
    problems: list[str]
    stdout: str
    stderr: str

    @property
    def healthy(self):
        return not self.problems

    def query(self, index):
        if index < len(self.queries):
            return self.queries[index]
        return QueryResult("", "", "missing")


def classify(command, text, complete=True):
    has = bool(CANDIDATE.search(text))
    times = re.findall(r"(?m)^(?:-- )?leant2: (\d+) ms$", text)
    first = next((line.strip() for line in text.splitlines() if CANDIDATE.match(line)), "")
    negative = [name for name, message in NEGATIVES.items() if message in text]
    if not complete:
        outcome = "incomplete"
    elif ERROR.search(text) or SORRY.search(text):
        outcome = "error"
    elif len(times) != 1 or len(negative) > 1 or (has and negative):
        outcome = "protocol_error"
    elif has:
        outcome = "candidate"
    elif negative:
        outcome = negative[0]
    else:
        outcome = "unknown"
    return QueryResult(command, text, outcome, has,
                       int(times[0]) if len(times) == 1 else None, first)


def parse(stdout, stderr, returncode, expected_commands, allowed_outside_errors=0):
    stdout = stdout.replace("\r\n", "\n")
    starts = list(QUERY.finditer(stdout))
    end_markers = list(re.finditer(r"(?m)^-- leant2-query-end$", stdout))
    problems = []
    if returncode != 0:
        problems.append(f"REPL exited {returncode}")
    if stderr.strip():
        problems.append("REPL wrote to stderr")
    if len(starts) != len(expected_commands):
        problems.append(f"expected {len(expected_commands)} queries, got {len(starts)}")
    if len(end_markers) != len(expected_commands):
        problems.append(f"expected {len(expected_commands)} completion markers, got {len(end_markers)}")
    results = []
    outside = [stdout[:starts[0].start()] if starts else stdout]
    for index, start in enumerate(starts):
        stop = starts[index + 1].start() if index + 1 < len(starts) else len(stdout)
        ends = [m for m in end_markers if start.end() < m.start() < stop]
        complete = len(ends) == 1
        text = stdout[start.end():ends[0].start() if complete else stop]
        result = classify(start.group(1), text, complete)
        if index >= len(expected_commands) or start.group(1) != expected_commands[index]:
            problems.append(f"query {index + 1} does not match its input command")
        if result.outcome in {"incomplete", "error", "protocol_error", "unknown"}:
            problems.append(f"query {index + 1}: {result.outcome}")
        results.append(result)
        if complete:
            outside.append(stdout[ends[0].end():stop])
    outside_text = "\n".join(outside)
    outside_errors = list(ERROR.finditer(outside_text))
    if len(outside_errors) != allowed_outside_errors or SORRY.search(outside_text):
        problems.append(f"expected {allowed_outside_errors} setup diagnostics, got {len(outside_errors)}")
    if allowed_outside_errors and any(not m.group(0).lstrip().startswith("error") for m in outside_errors):
        problems.append("unexpected runtime diagnostic outside queries")
    return SessionResult(results, problems, stdout, stderr)


def passes(result, expectation):
    if expectation == "candidate":
        return result.outcome == "candidate"
    if expectation == "false":
        return result.outcome == "contract_impossible"
    if expectation == "none":
        return result.outcome in BOUNDED | {"contract_impossible", "uninhabited"}
    if expectation == "inconclusive":
        return result.outcome in BOUNDED
    if expectation == "stretch":
        return result.outcome in BOUNDED | {"candidate"}
    raise ValueError(f"unknown expectation: {expectation}")


def run(exe, budget, source, output, allowed_outside_errors=0):
    path = Path(output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.with_suffix(".in").write_text(source, encoding="utf-8")
    expected = [line.rstrip() for line in source.splitlines() if line.startswith(":synth")]
    try:
        proc = subprocess.run([exe, f"--budget={budget}", "--query-markers"],
                              input=source.encode("utf-8"), capture_output=True,
                              timeout=max(60, budget * len(expected) / 1000 + 60))
        stdout = proc.stdout.decode("utf-8", "replace")
        stderr = proc.stderr.decode("utf-8", "replace")
        status = proc.returncode
    except (OSError, subprocess.TimeoutExpired) as error:
        stdout = getattr(error, "stdout", b"") or b""
        stderr = getattr(error, "stderr", b"") or b""
        stdout = stdout.decode("utf-8", "replace") if isinstance(stdout, bytes) else stdout
        stderr = stderr.decode("utf-8", "replace") if isinstance(stderr, bytes) else stderr
        stderr += f"\n{type(error).__name__}: {error}"
        status = -1
    path.write_text(stdout, encoding="utf-8")
    path.with_suffix(".stderr").write_text(stderr, encoding="utf-8")
    return parse(stdout, stderr, status, expected, allowed_outside_errors)


def print_problems(session):
    for problem in session.problems:
        print(f"FAIL protocol: {problem}", flush=True)
