#!/usr/bin/env python3
"""Run the Leant `:synth` golden corpus through the leant2 REPL and score it.

Scoring follows Definition 1.5 of the unified proposal: outcomes are compared
by category, not by text.

  positive   golden shows >= 1 candidate      -> leant2 must show >= 1 candidate
  uninhab    golden says provably uninhabited -> leant2 must say provably
             uninhabited, or show a classical candidate (the p ∨ ¬p case)
  miss       golden: no term found            -> any non-error outcome passes
  rejected   golden: none passed              -> any non-error outcome passes
  preflight  golden: assertion rejected       -> leant2 must report an error

Usage: python tools/run_baseline.py [--leant C:/Leant/test] [--exe PATH]
       [--budget MS] [--only NAME] [--out DIR]
"""
import argparse, os, re, subprocess, sys, time, json

def classify_golden(lines, i):
    """Classify the golden outcome of the :synth at golden line i."""
    j = i + 1
    while j < len(lines) and not (lines[j].startswith("λ>") or lines[j].startswith("⊢>")):
        l = lines[j]
        if l.startswith("  it1"):
            return "positive"
        if "provably uninhabited" in l:
            return "uninhab"
        if "no term found" in l:
            return "miss"
        if "none passed" in l:
            return "rejected"
        if "expected to have type" in l or "unknown" in l.lower() and "Unknown" in l:
            return "preflight"
        j += 1
    # assertion with unknown name / type errors show as error blocks
    k = i + 1
    while k < len(lines) and not (lines[k].startswith("λ>") or lines[k].startswith("⊢>")):
        if "error" in lines[k].lower() or "expected" in lines[k]:
            return "preflight"
        k += 1
    return "unknown"

def classify_ours(block):
    txt = "\n".join(block)
    if re.search(r"^  it1", txt, re.M):
        classical = "(classical)" in txt
        return "positive", classical
    if "provably uninhabited" in txt:
        return "uninhab", False
    if "no term found" in txt:
        return "miss", False
    if "budget exhausted" in txt:
        return "budget", False
    if "none passed" in txt or "provably no program" in txt:
        return "rejected", False
    if "error" in txt.lower():
        return "error", False
    return "unknown", False

def passes(golden, ours, classical):
    if golden == "positive":
        return ours == "positive"
    if golden == "uninhab":
        return ours == "uninhab" or (ours == "positive" and classical)
    if golden in ("miss", "rejected"):
        return ours in ("positive", "uninhab", "miss", "budget", "rejected")
    if golden == "preflight":
        return ours == "error"
    return False

def main():
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser()
    ap.add_argument("--leant", default="C:/Leant/test")
    ap.add_argument("--exe", default=".lake/build/bin/leant2.exe")
    ap.add_argument("--budget", type=int, default=10000)
    ap.add_argument("--only", default=None)
    ap.add_argument("--out", default="baseline-out")
    args = ap.parse_args()
    args.exe = os.path.abspath(args.exe)
    # the executable needs the toolchain's shared libraries on PATH
    try:
        lean = subprocess.run(["elan", "which", "lean"], capture_output=True, text=True).stdout.strip()
        os.environ["PATH"] = os.path.dirname(lean) + os.pathsep + os.environ.get("PATH", "")
    except FileNotFoundError:
        pass
    os.makedirs(args.out, exist_ok=True)
    fixtures = sorted(f for f in os.listdir(args.leant) if f.startswith("synth-") and f.endswith(".txt"))
    if args.only:
        fixtures = [f for f in fixtures if args.only in f]
    total = 0; passed = 0; rows = []
    for fx in fixtures:
        name = fx[:-4]
        with open(os.path.join(args.leant, fx), encoding="utf-8") as f:
            src = f.read()
        with open(os.path.join(args.leant, name + ".golden"), encoding="utf-8") as f:
            golden = f.read().splitlines()
        t0 = time.time()
        proc = subprocess.run([args.exe, f"--budget={args.budget}"], input=src.encode("utf-8"),
                              capture_output=True, timeout=3600)
        out = proc.stdout.decode("utf-8", errors="replace").splitlines()
        elapsed = time.time() - t0
        with open(os.path.join(args.out, name + ".out"), "w", encoding="utf-8") as f:
            f.write("\n".join(out) + "\n" + proc.stderr.decode("utf-8", errors="replace"))
        # pair up queries in order
        is_q = lambda l: l.startswith("λ> :synth") or l.startswith("⊢> :synth")
        g_idx = [i for i, l in enumerate(golden) if is_q(l)]
        o_idx = [i for i, l in enumerate(out) if is_q(l)]
        n = min(len(g_idx), len(o_idx))
        fx_pass = 0
        for q in range(n):
            gi = g_idx[q]; oi = o_idx[q]
            oend = o_idx[q + 1] if q + 1 < len(o_idx) else len(out)
            gcat = classify_golden(golden, gi)
            ocat, classical = classify_ours(out[oi + 1:oend])
            ok = passes(gcat, ocat, classical)
            total += 1; passed += ok; fx_pass += ok
            rows.append((name, golden[gi][3:], gcat, ocat, ok))
            if not ok:
                print(f"FAIL {name}: {golden[gi][3:]}\n     golden={gcat} ours={ocat}", flush=True)
        if len(g_idx) != len(o_idx):
            print(f"WARN {name}: {len(g_idx)} golden queries, {len(o_idx)} in output", flush=True)
        print(f"{name}: {fx_pass}/{n} in {elapsed:.0f}s", flush=True)
    print(f"\nTOTAL {passed}/{total}")
    with open(os.path.join(args.out, "summary.json"), "w", encoding="utf-8") as f:
        json.dump([dict(fixture=r[0], query=r[1], golden=r[2], ours=r[3], ok=r[4]) for r in rows], f, indent=1, ensure_ascii=False)

if __name__ == "__main__":
    main()
