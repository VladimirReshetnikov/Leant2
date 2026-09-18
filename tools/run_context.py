#!/usr/bin/env python3
"""Run Leant's behavioral-simplification and lexical-Given production cases.

Cases are transcribed from `C:\\Leant\\test-behavioral\\run_simplification.py`,
`C:\\Leant\\test-context\\run_production.py` and
`C:\\Leant\\test-context\\run_products.py` (Leant rev 6bf05ad). Leant ran
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
    "universe u",
    # test-context/run_polymorphic_selection.py and run_dictionary_selection.py
    "class SelectedPoly.Dictionary (α : Type) where tag : Nat",
    "structure SelectedPoly.Box (α : Type 1) where value : α",
    "structure SelectedPoly.GenericBox (α : Type u) where value : α",
    "inductive SelectedPoly.Pair (α : Type 1) (β : Type) where | mk : α → β → SelectedPoly.Pair α β",
    "class SelectionProbe.Dictionary (α : Type) where tag : Nat",
    "inductive SelectionProbe.Witness (α : Type 1) (R : Type) where | mk : R → α → SelectionProbe.Witness α R",
    "inductive SelectionProbe.Box (α : Type 1) where | mk : α → SelectionProbe.Box α",
    # test-context/run_constructors.py and run_strict_implicit.py
    "class Ctx.C (α : Type) where out : Nat",
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
    # --- test-context/run_products.py: general product construction; each spec
    # runs with its behavioral predicate and as an actual-False control
    products = [
        ("prod_adjacent_kinds", "∀ A : Type, (∀ F : Type → Type, A) → (∀ F : Type, A) → A × A",
         "@{f} Nat (fun _ => 7) (fun _ => 9) = (7,9)"),
        ("prod_mixed_applications", "∀ A B : Type, (A → B) → A → A → B × B",
         "@{f} Nat Nat (fun x => x + 1) 7 9 = (8,10)"),
        ("prod_projected_functions", "∀ A B : Type, ((A → B) × (A → B)) → A → B × B",
         "@{f} Nat Nat ((fun x => x + 1), (fun x => x * 2)) 3 = (4,6) ∧ @{f} Nat Nat ((fun x => x + 1), (fun x => x * 2)) 5 = (6,10)"),
        ("prod_sort_prop", "∀ A : Type, (Prop → A) → A", "@{f} Nat (fun _ => 37) = 37"),
        ("prod_sort_type_one", "∀ A : Type, (Type 1 → A) → A", "@{f} Nat (fun _ => 37) = 37"),
        ("prod_sort_parameter", "∀ A : Type, (Sort u → A) → A", "@{f} Nat (fun _ => 37) = 37"),
        ("prod_unequal_kind_domains", "∀ A : Type, ((Type 1 → Type) → A) → A", "@{f} Nat (fun _ => 37) = 37"),
    ]
    for name, ty, pred in products:
        out.append((name, ty, pred, "candidate"))
        out.append((name + "_false", ty, "False", "none"))
    # --- test-context/run_polymorphic_selection.py: nominal universe selections
    # and selected polymorphic payloads (the `.{u}` spellings use Leant's
    # live_predicate form, i.e. without the explicit universe)
    P = "∀ A : Type, [SelectedPoly.Dictionary A] → "
    POLY = "(∀ β : Type, β → Nat)"
    box_pred = ("(@{f} Nat (@SelectedPoly.Dictionary.mk Nat 7) (ULift.{1} Nat) ⟨37⟩).value.down = 37 ∧ "
                "(@{f} Nat (@SelectedPoly.Dictionary.mk Nat 11) (ULift.{1} Nat) ⟨53⟩).value.down = 53")
    poly_pred = ("(@{f} Nat (@SelectedPoly.Dictionary.mk Nat 7) (fun _ _ => 37)).value Bool true = 37 ∧ "
                 "(@{f} Nat (@SelectedPoly.Dictionary.mk Nat 11) (fun _ _ => 53)).value Unit () = 53")
    two_pred = ("let pair := @{f} Nat (@SelectedPoly.Dictionary.mk Nat 7) 37 ⟨53⟩; "
                "pair.1.value = 37 ∧ pair.2.value.down = 53")

    def higher(universe, applied_type, applied_value):
        return (f"(@{{f}} Nat (@SelectedPoly.Dictionary.mk Nat 7) (fun _ _ => 37)).value {applied_type} {applied_value} = 37 ∧ "
                f"(@{{f}} Nat (@SelectedPoly.Dictionary.mk Nat 11) (fun _ _ => 53)).value {applied_type} {applied_value} = 53")
    strict_poly = "(∀ ⦃β : Type⦄, β → Nat)"
    strict_pred = ("(@{f} Nat (@SelectedPoly.Dictionary.mk Nat 7) (fun ⦃_⦄ _ => 37)).value true = 37 ∧ "
                   "(@{f} Nat (@SelectedPoly.Dictionary.mk Nat 11) (fun ⦃_⦄ _ => 53)).value () = 53")
    pair_pred = ("match @{f} Nat (@SelectedPoly.Dictionary.mk Nat 7) Nat (fun _ _ => 37) 53 with "
                 "| .mk payload value => payload Bool true = 37 ∧ value = 53")
    QUAL = "(∀ β : Type, [SelectedPoly.Dictionary β] → β → Nat)"
    qual_pred = ("let result := (@{f} Nat (@SelectedPoly.Dictionary.mk Nat 7) "
                 "(fun (β : Type) [d : SelectedPoly.Dictionary β] _ => d.tag)).value; "
                 "@result Bool (@SelectedPoly.Dictionary.mk Bool 37) true = 37 ∧ "
                 "@result Unit (@SelectedPoly.Dictionary.mk Unit 53) () = 53")
    poly = [
        ("poly_fixed_higher_box", P + "∀ β : Type 1, β → SelectedPoly.Box β", box_pred),
        ("poly_selected_higher_box", P + "∀ β : Type 1, β → SelectedPoly.GenericBox.{1} β", box_pred),
        ("poly_two_box_selections", P + "Nat → ULift.{1} Nat → SelectedPoly.GenericBox.{0} Nat × SelectedPoly.GenericBox.{1} (ULift.{1} Nat)", two_pred),
        ("poly_boxed_polymorphic_payload", P + f"{POLY} → SelectedPoly.Box {POLY}", poly_pred),
        ("poly_boxed_type_one_quantifier", P + "(∀ β : Type 1, β → Nat) → SelectedPoly.GenericBox.{2} (∀ β : Type 1, β → Nat)",
         higher("1", "(ULift.{1} Nat)", "⟨37⟩")),
        ("poly_boxed_named_quantifier", P + "(∀ β : Type u, β → Nat) → SelectedPoly.GenericBox.{u+1} (∀ β : Type u, β → Nat)",
         higher("u", "PUnit.{u+1}", "PUnit.unit")),
        ("poly_boxed_strict_quantifier", P + f"{strict_poly} → SelectedPoly.Box {strict_poly}", strict_pred),
        ("poly_first_of_two_selections", P + f"∀ Z : Type, {POLY} → Z → SelectedPoly.Pair {POLY} Z", pair_pred),
        ("poly_boxed_qualified_payload", P + f"{QUAL} → SelectedPoly.Box {QUAL}", qual_pred),
    ]
    for name, ty, pred in poly:
        out.append((name, ty, pred, "candidate"))
        out.append((name + "_false", ty, "False", "none"))
    # --- test-context/run_dictionary_selection.py: a local qualified consumer
    # selecting a supplied forall, directly and inside a nominal wrapper
    DP = "∀ A R : Type, [SelectionProbe.Dictionary A] → "
    CONSUMER = "(∀ α : Type 1, [SelectionProbe.Dictionary A] → α → SelectionProbe.Witness α R) → "
    dict_obs, boxed_obs = [], []
    for tag, payload, at, av in [(7, 37, "Bool", "true"), (11, 53, "Unit", "()")]:
        head = (f"@{{f}} Nat Nat (@SelectionProbe.Dictionary.mk Nat {tag}) "
                "(fun α [d : SelectionProbe.Dictionary Nat] payload => (@SelectionProbe.Witness.mk α Nat d.tag payload)) ")
        dict_obs.append(f"(match {head}(fun _ _ => {payload}) with | .mk value payload => value = {tag} ∧ payload {at} {av} = {payload})")
        boxed_obs.append(f"(match {head}(@SelectionProbe.Box.mk {POLY} (fun _ _ => {payload})) with "
                         f"| .mk value (.mk payload) => value = {tag} ∧ payload {at} {av} = {payload})")
    BOXED = f"(SelectionProbe.Box {POLY})"
    dicts = [
        ("dict_forced_polymorphic_result", DP + CONSUMER + f"{POLY} → SelectionProbe.Witness {POLY} R", " ∧ ".join(dict_obs)),
        ("dict_boxed_polymorphic_result", DP + CONSUMER + f"{BOXED} → SelectionProbe.Witness {BOXED} R", " ∧ ".join(boxed_obs)),
    ]
    for name, ty, pred in dicts:
        out.append((name, ty, pred, "candidate"))
        out.append((name + "_false", ty, "False", "none"))
    # --- test-context/run_constructors.py: class methods and arguments under
    # constructors; run_strict_implicit.py repeats three of them with strict
    # implicit type binders
    ctors = [
        ("ctor_method", "∀ (α : Type), [Ctx.C α] → List Nat",
         "(@{f} Nat (@Ctx.C.mk Nat 7) = [7]) ∧ (@{f} Nat (@Ctx.C.mk Nat 11) = [11])"),
        ("ctor_argument", "∀ (α β : Type), [Ctx.C α] → β → List β",
         "(@{f} Nat Nat (@Ctx.C.mk Nat 7) 37 = [37]) ∧ (@{f} Nat Bool (@Ctx.C.mk Nat 11) true = [true])"),
        ("ctor_method_tail", "∀ (α : Type), [Ctx.C α] → List Nat → List Nat",
         "(@{f} Nat (@Ctx.C.mk Nat 7) [3, 5] = [7, 3, 5]) ∧ (@{f} Nat (@Ctx.C.mk Nat 11) [] = [11])"),
        ("ctor_argument_tail", "∀ (α β : Type), [Ctx.C α] → β → List β → List β",
         "(@{f} Nat Nat (@Ctx.C.mk Nat 7) 37 [3, 5] = [37, 3, 5]) ∧ (@{f} Nat Bool (@Ctx.C.mk Nat 11) true [false] = [true, false])"),
        ("ctor_wrapper", "∀ (α β : Type), [Ctx.C α] → β → Option (List β)",
         "(@{f} Nat Nat (@Ctx.C.mk Nat 7) 37 = some [37]) ∧ (@{f} Nat Bool (@Ctx.C.mk Nat 11) true = some [true])"),
        ("ctor_nested_list", "∀ (α β : Type), [Ctx.C α] → β → List (List β)",
         "(@{f} Nat Nat (@Ctx.C.mk Nat 7) 37 = [[37]]) ∧ (@{f} Nat Bool (@Ctx.C.mk Nat 11) true = [[true]])"),
        ("ctor_nested_context", "∀ (α : Type), [Ctx.C α] → ∀ (β : Type), [Ctx.C β] → List Nat",
         "(@{f} Nat (@Ctx.C.mk Nat 7) Bool (@Ctx.C.mk Bool 11) = [7]) ∧ (@{f} Nat (@Ctx.C.mk Nat 11) Bool (@Ctx.C.mk Bool 7) = [11])"),
    ]
    for name, ty, pred in ctors:
        out.append((name, ty, pred, "candidate"))
        out.append((name + "_false", ty, "False", "none"))
    strict = lambda text: re.sub(r"\((α(?: β)?|β) : Type\)", r"⦃\g<1> : Type⦄", text)
    for name, ty, pred in ctors:
        if name in ("ctor_method", "ctor_argument", "ctor_nested_context"):
            out.append((name.replace("ctor_", "strict_"), strict(ty), pred, "candidate"))
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
