"""Generate or check the ignored exact at fixture; never invoke native tools.

Default: read-only equality check. --write creates missing generated files and
refuses different existing bytes. Explicit --replace-draft permits replacing
generated draft sources, never native receipts.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
SPEC_DIR = Path("C:/Leant/lib/Djex/test-church")
OPERATION = "at"
sys.dont_write_bytecode = True


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_spec():
    sys.path.insert(0, str(SPEC_DIR))
    return importlib.import_module("behavior_partial_spec")


def build_artifacts():
    spec = load_spec()
    assert spec.SOURCE_CASE_IDS[OPERATION] == "church_case_033"
    assert spec.SOURCE_LINES[OPERATION] == 270
    assert len(spec.FIXTURES[OPERATION]) == 168
    inventory = spec.search_provider_inventory(OPERATION)
    assert [entry["name"] for entry in inventory["lean"]] == ["BehaviorPartialNumeric.intCase"]
    target = spec.LEAN_TYPES[OPERATION]
    contract = spec.lean_predicate(OPERATION, "f")
    prelude = "\n".join(spec.lean_prelude([OPERATION]))
    providers = spec.search_provider_source(OPERATION, "lean")
    template = (HERE / "Probe.body.lean.in").read_text(encoding="utf-8")
    probe = template.replace("@@PRELUDE@@", prelude).replace("@@PROVIDERS@@", "\n".join(providers))
    probe = probe.replace("@@TARGET@@", target).replace("@@CONTRACT@@", contract)
    assert "@@" not in probe
    assert prelude.count("(BehaviorPartial.enc (") == 168
    assert "def carrierReference" not in probe and "namespace BehaviorPartialOracle" not in probe
    assert "namespace BehaviorPartialControl" not in probe

    declarations, reference_names = spec.lean_control_source([OPERATION])
    primitive_declarations, primitive_names = spec.provider_control_source("lean")
    assert primitive_declarations[:len(providers)] == providers
    assert declarations[:len(providers)] == providers
    # Both authoritative source functions include the identical primitive.
    # Keep it once, preserving every original declaration/proof/audit unchanged.
    primitive_checks = primitive_declarations[len(providers):]
    controls = """import Lean

/-! UNVALIDATED independent controls. No Leant2 import, synthesis, or provider
discovery. The original oracle, primitive-only carrier witness, wrong programs,
and generic integer branch controls live only in this fresh Lean process.
Passing them would not establish automatic two-hole completion. -/

""" + prelude + "\n\n" + "\n".join(declarations + primitive_checks) + "\n"
    names = reference_names + primitive_names
    assert len(names) == len(set(names)) == 11
    assert spec.LEAN_PROVIDER_WITNESSES[OPERATION] in controls

    encode = lambda value: value.encode("utf-8")
    manifest = {
        "status": "UNVALIDATED_NOT_COMPILED_NOT_SYNTHESIZED",
        "generation_only": True,
        "operation": OPERATION,
        "source_case_id": spec.SOURCE_CASE_IDS[OPERATION],
        "source_line": spec.SOURCE_LINES[OPERATION],
        "source_signature": spec.SOURCE_SIGNATURES[OPERATION],
        "source_sha256_normalized": spec.SOURCE_SHA256,
        "spec_path": str(SPEC_DIR / "behavior_partial_spec.py"),
        "spec_sha256_bytes": digest(SPEC_DIR / "behavior_partial_spec.py"),
        "manifest_sha256_bytes": digest(SPEC_DIR / "manifest.json"),
        "original_lean_type_without_inserted_default": spec.ORIGINAL_LEAN_TYPES[OPERATION],
        "exact_established_defaulted_lean_type": target,
        "exact_contract": contract,
        "observation_count": len(spec.FIXTURES[OPERATION]),
        "observations": spec.FIXTURES[OPERATION],
        "profile": "strictConstructive",
        "explicit_query_providers": ["BehaviorPartialNumeric.intCase"],
        "original_provider_inventory": inventory,
        "exact_primitive_source": providers,
        "carrier": "Int → A",
        "open_holes_in_source_order": ["step", "init"],
        "hole_local_context": ["A : Type", "d : A"],
        "excluded_hole_locals": ["n : Int", "xs : CList A"],
        "budgets_ms": [5000, 10000],
        "budget_environment_variable": "LEANT2_SKETCH_PROBE_BUDGET_MS",
        "max_candidates": 1,
        "grace_ms": 0,
        "control_declarations": names,
        "original_reference_and_wrong_control_declarations": reference_names,
        "primitive_control_declarations": primitive_names,
        "exact_known_carrier_witness": spec.LEAN_PROVIDER_WITNESSES[OPERATION],
        "wrong_control_names": list(spec.LEAN_WRONG[OPERATION]),
        "control_import_policy": "Controls.lean must never be imported into Probe.lean or its process",
        "probe_sha256": hashlib.sha256(encode(probe)).hexdigest(),
        "controls_sha256": hashlib.sha256(encode(controls)).hexdigest(),
        "template_sha256": digest(HERE / "Probe.body.lean.in"),
        "generator_sha256": digest(Path(__file__)),
    }
    return {
        "Probe.lean": encode(probe),
        "Controls.lean": encode(controls),
        "provenance.json": encode(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--replace-draft", action="store_true")
    args = parser.parse_args()
    if args.replace_draft and not args.write:
        parser.error("--replace-draft requires --write")
    artifacts = build_artifacts()
    for name, content in artifacts.items():
        path = HERE / name
        if path.is_file() and path.read_bytes() == content:
            continue
        if not args.write:
            raise SystemExit("generated artifact absent or changed: " + name)
        if path.exists() and not args.replace_draft:
            raise SystemExit("refusing to overwrite different draft bytes: " + name)
    if args.write:
        for name, content in artifacts.items():
            path = HERE / name
            if not path.is_file() or path.read_bytes() != content:
                path.write_bytes(content)
    print("PASS: exact church_case_033 target, 168 observations, original primitive, 11 control audits; no native execution")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
