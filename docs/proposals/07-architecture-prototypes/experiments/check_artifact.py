#!/usr/bin/env python3
"""Check retained source identities and receipt fields, NOT the Lean proofs."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Quot.sound"}


def main() -> None:
    records: list[dict[str, object]] = []
    for name, expected_audit_count in (("Core", 20), ("Behavior", 5)):
        receipt_path = ROOT / "evidence" / f"{name}.receipt.json"
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        source = ROOT / receipt["submitted_file"]
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        if digest != receipt["source_sha256"]:
            raise ValueError(f"Source does not match retained receipt: {source}")
        response = receipt["response"]
        if response["okay"] is not True or response["failed_declarations"]:
            raise ValueError(f"Receipt does not report acceptance: {name}")
        if response["lean_errors"] or response["tool_errors"]:
            raise ValueError(f"Receipt contains errors: {name}")
        if response["echo_trim_equal"] is not True:
            raise ValueError(f"Echo comparison failed: {name}")
        audits = response["axiom_audits"]
        if len(audits) != expected_audit_count:
            raise ValueError(f"Unexpected audit count for {name}")
        for declaration, axioms in audits.items():
            forbidden = set(axioms) - ALLOWED_AXIOMS
            if forbidden:
                raise ValueError(f"Unexpected axioms for {declaration}: {forbidden}")
        records.append({"module": name, "source_identity_matches": True,
                        "named_axiom_audits": len(audits),
                        "request_id": response["info"]["request_id"]})
    print(json.dumps({"status": "retained evidence consistent; no new Lean check performed",
                      "records": records}, indent=2))

if __name__ == "__main__":
    main()
