#!/usr/bin/env python3
"""Replay Leant's session provider-identity suite through the leant2 REPL.

The six sessions come from `C:\Leant\test-context\run_session_provider_names.py`
(Leant rev 6bf05ad): nested namespaces, qualified names, attributes and
comments, duplicate short names, append/undo, and a rejected declaration.
Each `:synth pick : Nat → Nat where False` must be refuted, and the provider
inventory printed by `:providers` after it must equal the expected set of
session declarations. Each session is a fresh process.

Usage: python tools/run_session.py [--exe PATH] [--budget MS]
"""
import argparse, os, subprocess, sys, re

QUERY = ":synth pick : Nat → Nat where False\n:providers\n"


def block(code):
    return ":{\n" + code + "\n:}\n"


def cases():
    original = block("namespace Longer\ndef value : Nat := 37\nend Longer")
    yield "nested", block("namespace Outer\nnamespace Inner\ndef value : Nat := 37\nend Inner\nend Outer") + QUERY, [["Outer.Inner.value"]]
    yield "qualified", "def Outer.Inner.value : Nat := 37\n" + QUERY, [["Outer.Inner.value"]]
    yield "attributes-comments", block("namespace Outer\n/- def fake := 0 -/\n@[inline]\ndef value : Nat := 37\nend Outer") + QUERY, [["Outer.value"]]
    yield "same-leaf", block("namespace One\ndef value : Nat := 37\nend One\nnamespace Two\ndef value : Nat := 53\nend Two") + QUERY, [["One.value", "Two.value"]]
    yield "append-undo", original + QUERY + block("namespace A\ndef value : Nat := 53\nend A") + QUERY + ":undo\n" + QUERY, \
        [["Longer.value"], ["A.value", "Longer.value"], ["Longer.value"]]
    yield "rejected-entry", original + QUERY + block("namespace Bad\ndef value : Nat := True\nend Bad") + QUERY, \
        [["Longer.value"], ["Longer.value"]]


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
    passed = total = 0
    for name, src, expected in cases():
        proc = subprocess.run([exe, f"--budget={args.budget}"], input=(src + ":quit\n").encode("utf-8"), capture_output=True)
        out = proc.stdout.decode("utf-8", errors="replace")
        refuted = len(re.findall(r"provably no program satisfies the contract", out))
        inventories = [sorted(re.findall(r"`?([A-Za-z_][\w.]*)`?", m.group(1)))
                       for m in re.finditer(r"providers: \[([^\]]*)\]", out)]
        ok = refuted == len(expected) and inventories == [sorted(e) for e in expected]
        passed += ok
        total += 1
        print(f"{'PASS' if ok else 'FAIL'} {name}: refuted {refuted}/{len(expected)}, providers {inventories}")
        if not ok:
            print(out[-1500:])
    print(f"TOTAL {passed}/{total}")


if __name__ == "__main__":
    main()
