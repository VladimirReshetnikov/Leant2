"""Generate ignored, UNVALIDATED Lean probes without invoking native tools."""
from __future__ import annotations

import hashlib
import importlib
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
SPEC_DIR = Path("C:/Leant/lib/Djex/test-church")
sys.dont_write_bytecode = True
sys.path.insert(0, str(SPEC_DIR))
spec = importlib.import_module("behavior_partial_spec")

operation = "foldr1"
assert spec.SOURCE_CASE_IDS[operation] == "church_case_039"
assert spec.SOURCE_LINES[operation] == 295
assert len(spec.FIXTURES[operation]) == 36
provider_inventory = spec.search_provider_inventory(operation)
assert provider_inventory["lean"] == [], "review the original provider inventory"

target = spec.LEAN_TYPES[operation]
contract = spec.lean_predicate(operation, "f")
prelude = "\n".join(spec.lean_prelude([operation]))
template = (HERE / "Probe.body.lean.in").read_text(encoding="utf-8")
probe = template.replace("@@PRELUDE@@", prelude).replace("@@TARGET@@", target).replace("@@CONTRACT@@", contract)
assert "@@" not in probe
assert prelude.count("(BehaviorPartial.enc (") == 36
assert "BehaviorPartialOracle.foldr1" not in probe
(HERE / "Probe.lean").write_text(probe, encoding="utf-8", newline="\n")

controls, names = spec.lean_control_source([operation])
control_source = """import Lean

/-!
UNVALIDATED DRAFT: independent Lean-only controls, never synthesis providers.
Run in a separate fresh process. A pass verifies the original finite oracle,
known witness, and three separating wrong controls; it proves no search result.
-/

""" + prelude + "\n\n" + "\n".join(controls) + f"""

namespace Foldr1CarrierControl

def carrierReference : {target} :=
  fun A d combine xs =>
    (xs (Option A)
      (fun x rest => some (rest.elim x (combine x))) none).getD d

theorem carrierReference_passes :
    BehaviorPartial.check_foldr1 carrierReference = true := by decide

-- Universal only for this known carrier term on encodings of native lists.
-- It is not a theorem about a synthesized term or every Church inhabitant.
theorem carrierReference_enc (A : Type) (d : A) (combine : A → A → A) (xs : List A) :
    carrierReference A d combine (BehaviorPartial.enc xs) =
      BehaviorPartialOracle.foldr1 d combine xs := by rfl

end Foldr1CarrierControl

#print axioms Foldr1CarrierControl.carrierReference
#print axioms Foldr1CarrierControl.carrierReference_passes
#print axioms Foldr1CarrierControl.carrierReference_enc
"""
(HERE / "Controls.lean").write_text(control_source, encoding="utf-8", newline="\n")

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest = {
    "status": "UNVALIDATED_NOT_COMPILED_NOT_SYNTHESIZED",
    "generation_only": True,
    "operation": operation,
    "source_case_id": spec.SOURCE_CASE_IDS[operation],
    "source_line": spec.SOURCE_LINES[operation],
    "source_signature": spec.SOURCE_SIGNATURES[operation],
    "source_sha256_normalized": spec.SOURCE_SHA256,
    "spec_path": str(SPEC_DIR / "behavior_partial_spec.py"),
    "spec_sha256_bytes": digest(SPEC_DIR / "behavior_partial_spec.py"),
    "original_lean_type_without_inserted_default": spec.ORIGINAL_LEAN_TYPES[operation],
    "exact_established_defaulted_lean_type": target,
    "exact_contract": contract,
    "observation_count": len(spec.FIXTURES[operation]),
    "observations": spec.FIXTURES[operation],
    "profile": "strictConstructive",
    "explicit_query_providers": [],
    "original_provider_inventory": provider_inventory,
    "carrier": "Option A",
    "open_holes_in_source_order": ["step", "init", "finish"],
    "budgets_ms": [5000, 10000],
    "budget_environment_variable": "LEANT2_SKETCH_PROBE_BUDGET_MS",
    "control_declarations": names,
    "control_import_policy": "Controls.lean must never be imported into Probe.lean or its process",
    "probe_sha256": digest(HERE / "Probe.lean"),
    "controls_sha256": digest(HERE / "Controls.lean"),
    "template_sha256": digest(HERE / "Probe.body.lean.in"),
}
(HERE / "provenance.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
print(json.dumps({key: manifest[key] for key in [
    "status", "source_case_id", "observation_count", "explicit_query_providers",
    "probe_sha256", "controls_sha256",
]}, indent=2))
