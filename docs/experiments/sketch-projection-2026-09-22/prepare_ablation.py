"""Derive a recorded projection-disabled runner without changing frozen inputs."""
from pathlib import Path
import ast
import hashlib

here = Path(__file__).resolve().parent
original = (here / "run_probe.py").read_text(encoding="utf-8")
changes = [
    ('command = [str(lean), "--json", str(source)]',
     'command = [str(lean), *(["-Dleant2.skipRules=sketchProjection"] if budget is not None else []), "--json", str(source)]'),
    ('"provenance.json", "prepare.py", "run_probe.py")]',
     '"provenance.json", "prepare.py", "run_probe.py", "run_ablation.py", "prepare_ablation.py")]'),
    ('"source_mutation_performed": False,',
     '"source_mutation_performed": False,\n        "ablation": "projection disabled in native probe only",\n        "native_probe_options": ["-Dleant2.skipRules=sketchProjection"],'),
]
derived = original
for before, after in changes:
    assert derived.count(before) == 1, before
    derived = derived.replace(before, after)

def functions(text):
    return {n.name: ast.dump(n, include_attributes=False) for n in ast.parse(text).body
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}

a, b = functions(original), functions(derived)
assert a.keys() == b.keys()
assert {name for name in a if a[name] != b[name]} == {"run_native", "fingerprints", "main"}
(here / "run_ablation.py").write_text(derived, encoding="utf-8", newline="\n")
print("Derived runner; classifier, source, budgets, controls, providers and policy unchanged.")
print("sha256", hashlib.sha256((here / "run_ablation.py").read_bytes()).hexdigest())
