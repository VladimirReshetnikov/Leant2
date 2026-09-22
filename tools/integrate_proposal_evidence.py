"""Inventory the nine incoming expert packages and preserve original model evidence.

This one-time integration step does not delete sources or rewrite historical
receipts. The resulting manifest identifies every original Git blob, including
the articles/PDFs superseded by the maintained synthesis. It refuses a changed
input tree or an already existing manifest rather than silently replacing it.
"""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]
INCOMING = ROOT / "docs/proposals/new"
DEST = ROOT / "docs/proposals/11-further-improvements"
BASE = "5c3a53c22c18e6acd8ff17eb0902ce4da354518a"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    manifest = DEST / "integration/sources.json"
    assert not manifest.exists(), "source inventory already exists"
    assert git("rev-parse", "HEAD").decode().strip() == BASE
    packages = []
    for number in range(1, 10):
        directory = INCOMING / str(number)
        paths = sorted(p for p in directory.rglob("*") if p.is_file())
        assert paths, directory
        roots = [directory, *(p for p in directory.iterdir() if p.is_dir())]
        readmes = [p for p in roots if (p / "README.md").is_file()]
        assert len(readmes) == 1, readmes
        package_root = readmes[0]
        rows = []
        for path in paths:
            relative = path.relative_to(ROOT).as_posix()
            checkout = path.read_bytes()
            blob = git("rev-parse", f"{BASE}:{relative}").decode().strip()
            assert git("hash-object", "--path", relative, relative).decode().strip() == blob, relative
            data = git("cat-file", "blob", blob)
            row = {"original_path": relative, "bytes": len(data),
                   "sha256": sha(data), "git_blob": blob,
                   "checkout_bytes": len(checkout), "checkout_sha256": sha(checkout)}
            if path.suffix in {".py", ".json"} or path.name.startswith("SHA256SUMS"):
                target = DEST / "evidence" / f"N{number}" / path.relative_to(package_root)
                assert not target.exists(), target
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
                row.update(disposition="preserved evidence", destination=target.relative_to(ROOT).as_posix())
            elif path.suffix == ".tex":
                row["disposition"] = "integrate into maintained article; detailed coverage in integration ledgers"
            elif path.suffix == ".pdf":
                row["disposition"] = "superseded generated article; original retained at pinned Git blob"
            else:
                row["disposition"] = "superseded package/build instructions; original retained at pinned Git blob"
            rows.append(row)
        packages.append({"id": f"N{number}", "original_root": package_root.relative_to(ROOT).as_posix(),
                         "files": rows})
    document = {"schema": 1, "source_revision": BASE,
                "scope": "All files in the nine incoming packages, before integration or deletion.",
                "evidence_policy": "Preserved receipts describe the source packages, not a current Lean build or current PDF. New model reruns are recorded separately.",
                "packages": packages}
    manifest.parent.mkdir(parents=True, exist_ok=True)
    (DEST / "evidence/.gitattributes").write_text(
        "* -text whitespace=cr-at-eol\n*.bin -text whitespace=cr-at-eol,-blank-at-eof\n", encoding="utf-8")
    manifest.write_text(json.dumps(document, indent=2) + "\n", encoding="utf-8")
    print(f"Inventoried {sum(len(p['files']) for p in packages)} files in {len(packages)} packages")
    print(f"Preserved {sum('destination' in r for p in packages for r in p['files'])} evidence files")


if __name__ == "__main__":
    main()
