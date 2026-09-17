#!/usr/bin/env python3
"""Offline checks of source identities, fixture counts, and local experiments.
This does not run Lean. A passing result validates the package's consistency,
not a new compilation of its Lean code.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    core = (ROOT / "lean/Leant2Core.lean").read_text(encoding="utf-8")
    tests = (ROOT / "lean/Tests.lean").read_text(encoding="utf-8")
    joined = core + "\n" + tests.replace("import Leant2Core\n", "", 1)
    assert joined == (ROOT / "lean/StandaloneTests.lean").read_text(encoding="utf-8")
    # These exact sources contain no nested block comments or comment markers in strings.
    stripped = re.sub(r"/\-.*?\-/", "", joined, flags=re.S)
    stripped = "\n".join(line for line in stripped.splitlines()
                         if line.strip() and not line.lstrip().startswith("--")) + "\n"
    assert stripped == (ROOT / "lean/Validation.lean").read_text(encoding="utf-8")
    checker_spec = importlib.util.spec_from_file_location("check_lean", ROOT / "tools/check_lean.py")
    checker = importlib.util.module_from_spec(checker_spec)
    checker_spec.loader.exec_module(checker)
    for name, marker in (("native-validation.json", "LEANT2_AUDIT:"),
                         ("recursion-validation.json", "LEANT2_RECURSION_AUDIT:")):
        receipt = json.loads((ROOT / "receipts" / name).read_text())
        raw = (ROOT / receipt["source_path"]).read_bytes()
        assert len(raw) == receipt["source_bytes"]
        assert hashlib.sha256(raw).hexdigest() == receipt["source_sha256"]
        response = receipt["response"] | {"content": raw.decode("utf-8") + "\n"}
        assert checker.validate_response(raw.decode("utf-8"), response, marker) == []
        bad = response | {"okay": False}
        assert checker.validate_response(raw.decode("utf-8"), bad, marker)
        bad = response | {"content": "import Mathlib\n" + raw.decode("utf-8")}
        assert checker.validate_response(raw.decode("utf-8"), bad, marker)
    native = json.loads((ROOT / "receipts/native-validation.json").read_text())
    assert len(native["axiom_inventories"]) == 25
    assert sum(bool(v) for v in native["axiom_inventories"].values()) == 1
    assert tests.count("example ") == 8
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / "results.json"
        subprocess.run([sys.executable, str(ROOT / "experiments/search_models.py"),
                        "--output", str(output)], check=True, stdout=subprocess.DEVNULL)
        assert json.loads(output.read_text()) == json.loads((ROOT / "experiments/results.json").read_text())
    print("PASS: exact source identities, source generation, receipt validation, and local models.")
    print("Lean was not run by this offline consistency checker.")


if __name__ == "__main__":
    main()
