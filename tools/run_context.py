#!/usr/bin/env python3
"""Run Leant's behavioral-simplification and lexical-Given production cases.

Cases are transcribed from `C:\\Leant\\test-behavioral\\run_simplification.py`
and `C:\\Leant\\test-context\\run_production.py` (Leant rev 6bf05ad). Leant ran
each per engine; Leant2 runs each once. Expectations:

  candidate      at least one accepted `it1`
  none           no accepted candidate (actual-False or falsified contracts)
  inconclusive   no accepted candidate (opaque or partially opaque contracts)

Leant refused the `constant_universe` cell as unsupported metadata; Leant2 has
no such boundary, so it is expected to produce a candidate.

Usage: python tools/run_context.py [--exe PATH] [--budget MS]
"""
import argparse, os, subprocess, sys, re

CLASS = "ContextProduction.Dictionary"
TOKEN = "ContextProduction.Token"
UNIVERSE_CLASS = "ContextProduction.UniverseDictionary"
SCHEME = f"(∀ (β : Type), [{CLASS} β] → β → {TOKEN})"
IDENTITY = f"∀ (α : Type), [{CLASS} α] → α → α"
FORWARDING = SCHEME + " → " + SCHEME
LOCAL_GIVEN = f"∀ (α : Type), [{CLASS} α] → {SCHEME} → α → {TOKEN}"

PRELUDE = [
    "opaque BehavioralSimpFixture.pending : Prop := True",
    f"class {CLASS} (α : Type) where tag : Nat",
    f"structure {TOKEN} where payload : Nat",
    f"class {UNIVERSE_CLASS}.{{u}} (α : Type) : Type where evidence : ∀ β : Type u, True",
]


def dictionary(ty, payload):
    return f"(@{CLASS}.mk {ty} {payload})"


def provider(offset):
    return (f"(fun (β : Type) [d : {CLASS} β] (_ : β) => "
            f"{TOKEN}.mk ((@{CLASS}.tag β d) + {offset}))")


def conj(obs):
    return " ∧ ".join("(" + o + ")" for o in obs)


def cases():
    out = []
    # --- test-behavioral/run_simplification.py
    ty = "∀ A : Type, A → A"
    quantified = "∀ n : Nat, {f} Nat n + 0 = n"
    out += [
        ("simp_quantified", ty, quantified, "candidate"),
        ("simp_falsified", ty, "(" + quantified + ") ∧ False", "none"),
        ("simp_opaque", ty, "BehavioralSimpFixture.pending", "inconclusive"),
        ("simp_partial", ty, "BehavioralSimpFixture.pending ∧ (" + quantified + ")", "inconclusive"),
        ("simp_recovery", ty, "{f} Nat 7 = 7", "candidate"),
    ]
    # --- test-context/run_production.py
    identity_obs = [
        f"@{{f}} Nat {dictionary('Nat', 7)} 37 = 37",
        f"@{{f}} Nat {dictionary('Nat', 11)} 53 = 53",
        f"@{{f}} Bool {dictionary('Bool', 11)} true = true",
        f"@{{f}} Bool {dictionary('Bool', 7)} false = false",
    ]
    fwd_obs, local_obs = [], []
    for t, value, payload, offset in [("Nat", "37", 7, 0), ("Nat", "37", 11, 0),
                                      ("Nat", "53", 7, 100), ("Bool", "true", 11, 100)]:
        d = dictionary(t, payload)
        cb = provider(offset)
        fwd_obs.append(f"{TOKEN}.payload (@{{f}} {cb} {t} {d} {value}) = {payload + offset}")
        local_obs.append(f"{TOKEN}.payload (@{{f}} {t} {d} {cb} {value}) = {payload + offset}")
    out += [
        ("ctx_identity_ordinary", IDENTITY, None, "candidate"),
        ("ctx_identity", IDENTITY, conj(identity_obs), "candidate"),
        ("ctx_forwarding_ordinary", FORWARDING, None, "candidate"),
        ("ctx_forwarding", FORWARDING, conj(fwd_obs), "candidate"),
        ("ctx_local_given_ordinary", LOCAL_GIVEN, None, "candidate"),
        ("ctx_local_given", LOCAL_GIVEN, conj(local_obs), "candidate"),
        ("ctx_reject_all", IDENTITY, "False", "none"),
        ("ctx_identity_wrong", IDENTITY, f"@{{f}} Nat {dictionary('Nat', 7)} 37 = 38", "none"),
        ("ctx_constant_universe", f"∀ (α : Type), [{UNIVERSE_CLASS}.{{1}} α] → α → α", "True", "candidate"),
    ]
    return out


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
    for name, ty, pred, exp in cases():
        if pred is None:
            lines.append(f":synth {name} : {ty}")
        else:
            lines.append(f":synth {name} : {ty} where {pred.replace('{f}', name)}")
        expected.append((name, exp))
    lines.append(":quit")
    src = "\n".join(lines) + "\n"
    proc = subprocess.run([exe, f"--budget={args.budget}"], input=src.encode("utf-8"), capture_output=True)
    out = proc.stdout.decode("utf-8", errors="replace")
    blocks = re.split(r"(?m)^λ> :synth ", out)[1:]
    if len(blocks) != len(expected):
        print(f"expected {len(expected)} query blocks, got {len(blocks)}")
        print(out[-3000:])
    passed = 0
    for (name, exp), block in zip(expected, blocks):
        has = re.search(r"^  it1", block, re.M) is not None
        ms = re.search(r"leant2: (\d+) ms", block)
        ok = has if exp == "candidate" else not has
        passed += ok
        first = next((l.strip() for l in block.splitlines() if l.startswith("  it1")), "")
        tail = "" if has else " | " + " ".join(l.strip() for l in block.splitlines()[1:4] if "leant2:" not in l)[:90]
        print(f"{'PASS' if ok else 'FAIL'} {name} [{ms.group(1) if ms else '?'} ms] {first[:120]}{tail}")
    print(f"TOTAL {passed}/{len(expected)}")
    if proc.stderr:
        print(proc.stderr.decode("utf-8", errors="replace")[:500])


if __name__ == "__main__":
    main()
