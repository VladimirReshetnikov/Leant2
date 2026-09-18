#!/usr/bin/env python3
"""Build everything and run every acceptance harness, printing one summary.

Order: `lake build` (library, tests, executable), then the golden `:synth`
baseline and the extended tiers. Each harness prints its own detail; this
script keeps the TOTAL lines. Exit status is nonzero when any harness is not
at full score (stretch cases are never counted).

Usage: python tools/run_all.py [--budget MS] [--skip-build]
"""
import argparse, os, re, subprocess, sys, time

HARNESSES = [
    ("baseline", ["tools/run_baseline.py"]),
    ("recursive", ["tools/run_recursive.py"]),
    ("church", ["tools/run_church.py"]),
    ("context", ["tools/run_context.py"]),
    ("corpus", ["tools/run_corpus.py"]),
    ("session", ["tools/run_session.py"]),
]


def main():
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser()
    ap.add_argument("--budget", type=int, default=10000)
    ap.add_argument("--skip-build", action="store_true")
    args = ap.parse_args()
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    os.chdir(root)
    if not args.skip_build:
        t0 = time.time()
        r = subprocess.run(["lake", "build", "Leant2", "Leant2Tests", "leant2"], capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        ok = r.returncode == 0
        print(f"build: {'ok' if ok else 'FAILED'} in {time.time() - t0:.0f}s")
        if not ok:
            print(r.stdout[-3000:], r.stderr[-3000:])
            sys.exit(1)
    rows = []
    for name, cmd in HARNESSES:
        t0 = time.time()
        extra = ["--budget", str(args.budget)] if name != "session" else []
        r = subprocess.run([sys.executable, "-X", "utf8", *cmd, *extra], capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        m = re.search(r"^TOTAL (\d+)/(\d+)", r.stdout, re.M)
        got, tot = (int(m.group(1)), int(m.group(2))) if m else (0, -1)
        rows.append((name, got, tot, time.time() - t0))
        print(f"{name}: {got}/{tot} in {time.time() - t0:.0f}s" + ("" if got == tot else "  <-- see below"))
        if got != tot:
            print(r.stdout[-2500:])
    print()
    print("| Harness | Score | Time |")
    print("| --- | --- | --- |")
    for name, got, tot, dt in rows:
        print(f"| {name} | {got}/{tot} | {dt:.0f} s |")
    sys.exit(0 if all(got == tot for _, got, tot, _ in rows) else 1)


if __name__ == "__main__":
    main()
