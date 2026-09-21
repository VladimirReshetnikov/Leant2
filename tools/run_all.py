#!/usr/bin/env python3
"""Build everything and run every acceptance harness, printing one summary.

Order: `lake build` (library, tests, executable), then the golden `:synth`
baseline and the extended tiers. Each harness prints its own detail; this
script keeps the TOTAL lines. Exit status is nonzero when any harness is not
at full score (stretch cases are never counted).

Usage: python tools/run_all.py [--budget MS] [--skip-build] [--out DIRECTORY]
"""
import argparse, json, os, re, subprocess, sys, time
from pathlib import Path

HARNESSES = [
    ("baseline", ["tools/run_baseline.py"]),
    ("recursive", ["tools/run_recursive.py"]),
    ("church", ["tools/run_church.py"]),
    ("context", ["tools/run_context.py"]),
    ("corpus", ["tools/run_corpus.py"]),
    ("session", ["tools/run_session.py"]),
    ("results", ["tools/run_results.py"]),
    ("extended", ["tools/run_extended.py"]),
    ("recursion-gates", ["tools/run_extended.py", "--manifest", "tests/benchmarks/recursion.json"]),
    ("local-proofs", ["tools/run_extended.py", "--manifest", "tests/benchmarks/local-proofs.json"]),
]


def main():
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser()
    ap.add_argument("--budget", type=int, default=10000)
    ap.add_argument("--skip-build", action="store_true")
    ap.add_argument("--out", default="baseline-out/run-all", help="directory for complete harness logs and summary")
    args = ap.parse_args()
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    os.chdir(root)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    if not args.skip_build:
        t0 = time.time()
        r = subprocess.run(["lake", "build", "Leant2", "Leant2Tests", "leant2"], capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        ok = r.returncode == 0
        (out / "build.log").write_text(r.stdout + "\n" + r.stderr, encoding="utf-8")
        print(f"build: {'ok' if ok else 'FAILED'} in {time.time() - t0:.0f}s", flush=True)
        if not ok:
            print(r.stdout[-3000:], r.stderr[-3000:])
            sys.exit(1)
    rows = []
    receipts = []
    for name, cmd in HARNESSES:
        t0 = time.time()
        extra = ["--budget", str(args.budget)]
        if name in {"baseline", "church", "session", "results"}:
            extra += ["--out", str(out / name)]
        elif name in {"recursive", "context", "corpus"}:
            extra += ["--out", str(out / f"{name}.out")]
        elif name in {"extended", "recursion-gates", "local-proofs"}:
            extra += ["--out", str(out / f"{name}.json")]
        r = subprocess.run([sys.executable, "-X", "utf8", *cmd, *extra], capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        m = re.search(r"^TOTAL (\d+)/(\d+)", r.stdout, re.M)
        got, tot = (int(m.group(1)), int(m.group(2))) if m else (0, -1)
        ok = r.returncode == 0 and tot > 0 and got == tot
        (out / f"{name}.log").write_text(r.stdout + "\n" + r.stderr, encoding="utf-8")
        receipts.append(dict(harness=name, passed=got, total=tot, seconds=time.time() - t0,
                             returncode=r.returncode, ok=ok))
        rows.append((name, got, tot, time.time() - t0, ok))
        print(f"{name}: {got}/{tot} in {time.time() - t0:.0f}s" + ("" if ok else "  <-- see below"), flush=True)
        if not ok:
            print(f"exit status: {r.returncode}\n{r.stdout[-2500:]}\n{r.stderr[-2500:]}")
        else:
            for line in r.stdout.splitlines():
                if line.startswith("OPEN "):
                    print(f"{name}: {line}", flush=True)
    print()
    print("| Harness | Score | Time |")
    print("| --- | --- | --- |")
    for name, got, tot, dt, ok in rows:
        print(f"| {name} | {got}/{tot} | {dt:.0f} s |")
    (out / "summary.json").write_text(json.dumps(
        dict(budget_ms=args.budget, harnesses=receipts), indent=2) + "\n", encoding="utf-8")
    sys.exit(0 if all(ok for _, _, _, _, ok in rows) else 1)


if __name__ == "__main__":
    main()
