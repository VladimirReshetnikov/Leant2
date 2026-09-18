#!/usr/bin/env python3
"""Run Leant's Church signature corpus (350 type-only queries) through leant2.

The Lean counterparts of the Djex Church signatures are produced by Leant's
own translator (`C:\\Leant\\test-church\\run_corpus.py`, Leant rev 6bf05ad) from
the vendored manifest (`C:\\Leant\\lib\\Djex\\test-church\\manifest.json`). Every
query is expected to yield a candidate; the 16 `needs_int_provider` cases may
use the session provider `ChurchCorpus.integerZero`. Leant ran the corpus per
engine; Leant2 runs it once.

Usage: python tools/run_corpus.py [--exe PATH] [--budget MS] [--leant DIR] [--limit N]
"""
import argparse, json, os, subprocess, sys, re
from pathlib import Path


def main():
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser()
    ap.add_argument("--exe", default=".lake/build/bin/leant2.exe")
    ap.add_argument("--budget", type=int, default=10000)
    ap.add_argument("--leant", default=r"C:\Leant")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--out", default="baseline-out/church-corpus.out")
    args = ap.parse_args()
    sys.path.insert(0, str(Path(args.leant) / "test-church"))
    import run_corpus as rc
    manifest = json.load(open(Path(args.leant) / "lib/Djex/test-church/manifest.json", encoding="utf-8"))
    cases = rc.translated_cases(manifest)
    if args.limit:
        cases = cases[:args.limit]
    exe = os.path.abspath(args.exe)
    try:
        lean = subprocess.run(["elan", "which", "lean"], capture_output=True, text=True).stdout.strip()
        os.environ["PATH"] = os.path.dirname(lean) + os.pathsep + os.environ.get("PATH", "")
    except FileNotFoundError:
        pass
    lines = ["def ChurchCorpus.integerZero : Int := 0", ""]
    for c in cases:
        lines.append(f":synth {c['lean_type']}")
    lines.append(":quit")
    src = "\n".join(lines) + "\n"
    proc = subprocess.run([exe, f"--budget={args.budget}"], input=src.encode("utf-8"), capture_output=True)
    out = proc.stdout.decode("utf-8", errors="replace")
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    open(args.out, "w", encoding="utf-8").write(out)
    blocks = re.split(r"(?m)^λ> :synth ", out)[1:]
    if len(blocks) != len(cases):
        print(f"expected {len(cases)} query blocks, got {len(blocks)}")
    passed = 0
    slow = []
    for c, block in zip(cases, blocks):
        has = re.search(r"^  it1", block, re.M) is not None
        ms = re.search(r"leant2: (\d+) ms", block)
        t = int(ms.group(1)) if ms else -1
        passed += has
        first = next((l.strip() for l in block.splitlines() if l.startswith("  it1")), "")
        if not has:
            tail = " ".join(l.strip() for l in block.splitlines()[1:3] if "leant2:" not in l)[:80]
            print(f"FAIL {c['id']} {c['name']} ({c['classification']}) [{t} ms] {c['lean_type'][:140]} | {tail}")
        elif t >= 2000:
            slow.append((t, c['name']))
    print(f"slow (>= 2 s): {sorted(slow, reverse=True)[:15]}")
    print(f"TOTAL {passed}/{len(cases)}")
    if proc.stderr:
        print(proc.stderr.decode("utf-8", errors="replace")[:500])


if __name__ == "__main__":
    main()
