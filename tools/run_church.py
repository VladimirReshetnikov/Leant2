#!/usr/bin/env python3
"""Run Leant's Church behavior probes through the leant2 REPL.

The specifications are imported verbatim from Leant's vendored Djex directory
(`C:\\Leant\\lib\\Djex\\test-church`, Leant rev 6bf05ad): the six core operations
of `behavior_probe.py` (not, swap, map, append, reverse, filter) and the
thirteen extended operations of `behavior_extended_probe.py`, and the nineteen
partial operations of `behavior_partial_probe.py` (total functions with an
explicit default argument). Each `:synth`
carries the spec's `check_<op> f = true` contract, so a candidate passes only
when it behaves correctly on the spec's exhaustive finite inputs. Leant ran
the matrix per engine; Leant2 has one adaptive engine, so each case runs once.
`length` needs the numeric providers the spec declares (`BehaviorExtendedNumeric`).

Usage: python tools/run_church.py [--exe PATH] [--budget MS] [--spec core|extended|all]
                                  [--leant DIR] [--op NAME ...]
"""
import argparse, os, subprocess, sys, re
from pathlib import Path
import repl_protocol


def load_specs(leant_root, which):
    sys.path.insert(0, str(Path(leant_root) / "lib" / "Djex" / "test-church"))
    specs = []
    if which in ("core", "all"):
        import behavior_spec, behavior_runtime
        prov = behavior_runtime.source_provenance(Path(leant_root) / "lib/Djex/test-church/manifest.json")
        targets = {row["name"]: row["lean_target"] for row in prov["operations"]}
        specs.append(("church", behavior_spec, list(behavior_spec.OPERATIONS), targets, []))
    if which in ("extended", "all"):
        import behavior_extended_spec as ext
        specs.append(("extended", ext, list(ext.OPERATIONS), dict(ext.LEAN_TYPES), list(ext.LEAN_NUMERIC_PROVIDERS)))
    if which in ("partial", "all"):
        import behavior_partial_spec as part
        provs = []
        for op in part.OPERATIONS:
            for row in part.REQUIRED_PROVIDERS[op]["lean"]:
                d = f"def {row['name']} : {row['type']} := {row['definition']}"
                if d not in provs:
                    provs.append(d)
        specs.append(("partial", part, list(part.OPERATIONS), dict(part.LEAN_TYPES), provs))
    return specs


# Partial operations Leant's behavior ledger (test-church/behavior-ledger.md)
# never accepted in any engine: stretch goals, reported but not scored.
STRETCH = {"at", "foldl1", "foldr1", "maximumBy", "maximumOn", "minimumBy", "minimumOn",
           "minMaxBy", "minmaxElement", "reduce", "maximum", "minimum", "minMax"}


def main():
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser()
    ap.add_argument("--exe", default=".lake/build/bin/leant2.exe")
    ap.add_argument("--budget", type=int, default=10000)
    ap.add_argument("--spec", choices=("core", "extended", "partial", "all"), default="all")
    ap.add_argument("--leant", default=r"C:\Leant")
    ap.add_argument("--op", action="append")
    ap.add_argument("--out", default="baseline-out/church", help="directory for raw per-tier REPL transcripts")
    args = ap.parse_args()
    exe = os.path.abspath(args.exe)
    try:
        lean = subprocess.run(["elan", "which", "lean"], capture_output=True, text=True).stdout.strip()
        os.environ["PATH"] = os.path.dirname(lean) + os.pathsep + os.environ.get("PATH", "")
    except FileNotFoundError:
        pass
    passed = total = 0
    healthy = True
    for label, spec, ops, targets, numeric in load_specs(args.leant, args.spec):
        lines = [l for l in spec.lean_prelude() if not l.startswith("set_option") and not l.startswith("universe")]
        lines += numeric + [""]
        expected = []
        for op in ops:
            if args.op and op not in args.op:
                continue
            name = f"{label}_{op}"
            lines.append(f":synth {name} : {targets[op]} where {spec.lean_predicate(op, name)}")
            expected.append((name, "stretch" if label == "partial" and op in STRETCH else "candidate"))
        first_op = ops[0]
        lines.append(f":synth {label}_reject : {targets[first_op]} where False")
        expected.append((f"{label}_reject", "false"))
        lines.append(":quit")
        src = "\n".join(lines) + "\n"
        session = repl_protocol.run(exe, args.budget, src, Path(args.out) / f"{label}.out")
        repl_protocol.print_problems(session)
        healthy = healthy and session.healthy
        for index, (name, exp) in enumerate(expected):
            result = session.query(index)
            ok = session.healthy and repl_protocol.passes(result, exp)
            if exp == "stretch":
                healthy = healthy and ok
                status = "STRETCH-PASS" if ok and result.candidate else "STRETCH-MISS" if ok else "STRETCH-ERROR"
                print(f"{status} {name} [{result.elapsed_ms} ms] {result.outcome} {result.first[:120]}")
                continue
            passed += ok
            total += 1
            print(f"{'PASS' if ok else 'FAIL'} {name} [{result.elapsed_ms} ms] {result.outcome} {result.first[:120]}")
    print(f"TOTAL {passed}/{total}")
    return 0 if healthy and total > 0 and passed == total else 1


if __name__ == "__main__":
    sys.exit(main())
