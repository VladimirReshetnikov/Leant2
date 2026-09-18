#!/usr/bin/env python3
"""Run Leant's `test-recursive` behavioral scenarios through the leant2 REPL.

The eight named `:synth NAME : T where P` cases and their datatype prelude are
taken verbatim from `C:\\Leant\\test-recursive\\run_behavior.py` (Leant rev
6bf05ad). Leant runs them per engine; Leant2 has one engine, so each case runs
once. A case passes when leant2 reports at least one accepted candidate; the
`reject_all` control passes when it reports no candidate.

Usage: python tools/run_recursive.py [--exe PATH] [--budget MS]
"""
import argparse, os, subprocess, sys, re

PRELUDE = [
    "inductive RecursiveCases.Tree (α : Type) where | leaf : α → Tree α | branch : Tree α → Tree α → Tree α",
    "inductive RecursiveCases.Payload (α : Type) where | pairLeaf : α × α → Payload α | next : Payload α → Payload α",
    "abbrev RecursiveCases.Sequence (α : Type) := List α",
]

CASES = [
    ("null", "{α : Type} → List α → Bool",
     "{f} ([] : List Nat) = true ∧ {f} [11] = false ∧ {f} [true, false] = false"),
    ("headOr", "{α : Type} → α → List α → α",
     "{f} 91 ([] : List Nat) = 91 ∧ {f} 91 [11, 29] = 11 ∧ {f} false [true] = true"),
    ("tailOr", "{α : Type} → List α → List α → List α",
     "{f} [91] ([] : List Nat) = [91] ∧ {f} [91] [11] = [] ∧ {f} [91] [11, 29, 37] = [29, 37] ∧ {f} [false] [true, true] = [true]"),
    ("tree", "{α : Type} → α → RecursiveCases.Tree α → α",
     "{f} 91 (.leaf 11) = 11 ∧ {f} 91 (.branch (.leaf 11) (.leaf 29)) = 91 ∧ {f} false (.leaf true) = true"),
    ("alias", "{α : Type} → α → RecursiveCases.Sequence α → α",
     "{f} 91 ([] : List Nat) = 91 ∧ {f} 91 [11, 29] = 11 ∧ {f} false [true] = true"),
    ("unconsOr", "{α : Type} → α → List α → α × List α",
     "{f} 91 ([] : List Nat) = (91, []) ∧ {f} 91 [11, 29] = (11, [29]) ∧ {f} false [true, false] = (true, [false])"),
    ("tupleField", "{α : Type} → α → RecursiveCases.Payload α → α",
     "{f} 91 (.pairLeaf (11, 29)) = 11 ∧ {f} 91 (.next (.pairLeaf (11, 29))) = 91 ∧ {f} false (.pairLeaf (true, false)) = true"),
    ("independent", "{α β : Type} → α → β → List α → List β → α × β",
     "{f} 91 false ([] : List Nat) [] = (91, false) ∧ {f} 91 false [11, 29] [true] = (11, true) ∧ {f} 91 false [] [true] = (91, true)"),
]

def main():
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser()
    ap.add_argument("--exe", default=".lake/build/bin/leant2.exe")
    ap.add_argument("--budget", type=int, default=10000)
    args = ap.parse_args()
    exe = os.path.abspath(args.exe)
    try:
        lean = subprocess.run(["elan", "which", "lean"], capture_output=True, text=True).stdout.strip()
        os.environ["PATH"] = os.path.dirname(lean) + os.pathsep + os.environ.get("PATH", "")
    except FileNotFoundError:
        pass
    lines = list(PRELUDE) + [""]
    expected = []
    for op, ty, pred in CASES:
        name = f"recursive_{op}"
        lines.append(f":synth {name} : {ty} where {pred.format(f=name)}")
        expected.append((name, "candidate"))
    lines.append(":synth recursive_reject_all : Nat → Nat where False")
    expected.append(("recursive_reject_all", "none"))
    lines.append(":quit")
    src = "\n".join(lines) + "\n"
    proc = subprocess.run([exe, f"--budget={args.budget}"], input=src.encode("utf-8"), capture_output=True)
    out = proc.stdout.decode("utf-8", errors="replace")
    blocks = re.split(r"(?m)^λ> :synth ", out)[1:]
    passed = 0
    for (name, exp), block in zip(expected, blocks):
        has = re.search(r"^  it1", block, re.M) is not None
        ms = re.search(r"leant2: (\d+) ms", block)
        ok = has if exp == "candidate" else not has
        passed += ok
        first = next((l.strip() for l in block.splitlines() if l.startswith("  it1")), "")
        print(f"{'PASS' if ok else 'FAIL'} {name} [{ms.group(1) if ms else '?'} ms] {first[:110]}")
    print(f"TOTAL {passed}/{len(expected)}")
    if proc.stderr:
        print(proc.stderr.decode("utf-8", errors="replace")[:500])

if __name__ == "__main__":
    main()
