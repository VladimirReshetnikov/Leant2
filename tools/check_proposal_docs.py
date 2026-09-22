"""Check the maintained proposal sources and preserved incoming evidence.

This is documentation validation, not a Lean or mathematical-proof check.
Run from any directory; --require-retired additionally forbids incoming files.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parents[1]
PROPOSALS = ROOT / "docs/proposals"
MAINTAINED = PROPOSALS / "11-further-improvements"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-retired", action="store_true")
    args = parser.parse_args()
    errors: list[str] = []
    counts: dict[str, object] = {}
    maintained_bibkeys: set[str] = set()

    for directory, entry in [("10-unified-proposal", "Leant2.tex"),
                             ("11-further-improvements", "Leant2-next.tex")]:
        article_root = PROPOSALS / directory
        visited: set[Path] = set()
        texts: list[str] = []

        def read_article(path: Path) -> None:
            if path in visited:
                return
            visited.add(path)
            if not path.is_file():
                errors.append(f"Missing TeX input: {path.relative_to(ROOT)}")
                return
            text = path.read_text(encoding="utf-8")
            texts.append(text)
            for target in re.findall(r"\\(?:input|include)\{([^}]+)\}", text):
                child = article_root / target
                read_article(child if child.suffix else child.with_suffix(".tex"))

        read_article(article_root / entry)
        joined = "\n".join(texts)
        labels = re.findall(r"\\label\{([^}]+)\}", joined)
        references = re.findall(r"\\(?:ref|eqref|pageref|autoref)\{([^}]+)\}", joined)
        bibkeys = re.findall(r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}", joined)
        citations = [key.strip() for group in
                     re.findall(r"\\cite\w*\*?(?:\[[^\]]*\])*\{([^}]+)\}", joined)
                     for key in group.split(",")]
        for kind, values in [("label", labels), ("bibliography key", bibkeys)]:
            for value, count in Counter(values).items():
                if count > 1:
                    errors.append(f"{directory}: duplicate {kind} {value}")
        for reference in sorted(set(references) - set(labels)):
            errors.append(f"{directory}: undefined reference {reference}")
        for citation in sorted(set(citations) - set(bibkeys)):
            errors.append(f"{directory}: undefined citation {citation}")
        counts[directory] = {"tex_files": len(visited), "labels": len(labels),
                             "bibliography_entries": len(bibkeys)}
        if directory == "11-further-improvements":
            maintained_bibkeys = set(bibkeys)

    expected_questions = {1: 4, 2: 5, 3: 4, 4: 4, 5: 4, 6: 3, 7: 3, 8: 3, 9: 3}
    question_ids: list[str] = []
    for path in sorted((MAINTAINED / "sections").glob("*.tex")):
        text = path.read_text(encoding="utf-8")
        question_ids.extend(re.findall(r"\\item\[(R\d+\.N\d+)\.\]", text))
        for topic, body in re.findall(
                r"\\begin\{enumerate\}\[label=R(\d+)\.N\\arabic\*\.\](.*?)"
                r"\\end\{enumerate\}", text, flags=re.S):
            for number in range(1, len(re.findall(r"\\item\b", body)) + 1):
                question_ids.append(f"R{topic}.N{number}")
        if re.search(r"\\item\[R\d+\.(?:Q)?\d+\.\]", text):
            errors.append(f"Historical question still active: {path.name}")
    expected_ids = {f"R{topic}.N{number}" for topic, total in expected_questions.items()
                    for number in range(1, total + 1)}
    if set(question_ids) != expected_ids or len(question_ids) != len(expected_ids):
        errors.append(f"Expected exactly 33 distinct active question IDs; got {question_ids}")
    counts["active_questions"] = len(question_ids)

    manifest = json.loads((MAINTAINED / "integration/sources.json").read_text(encoding="utf-8"))
    originals = preserved = incoming = 0
    incoming_bibkeys: set[str] = set()
    for package in manifest["packages"]:
        if args.require_retired and package.get("status") != "integrated and retired":
            errors.append(f"Package not marked integrated: {package['id']}")
        for item in package["files"]:
            originals += 1
            source = ROOT / item["original_path"]
            blob = subprocess.run(["git", "cat-file", "blob", item["git_blob"]],
                                  cwd=ROOT, check=True, capture_output=True).stdout
            if len(blob) != item["bytes"] or hashlib.sha256(blob).hexdigest() != item["sha256"]:
                errors.append(f"Original Git blob mismatch: {item['original_path']}")
            if item["original_path"].endswith(".tex"):
                incoming_bibkeys.update(re.findall(
                    r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}", blob.decode("utf-8")))
            if source.exists():
                incoming += 1
                actual_blob = subprocess.run(
                    ["git", "hash-object", "--path", item["original_path"], str(source)],
                    cwd=ROOT, check=True, capture_output=True, text=True).stdout.strip()
                if actual_blob != item["git_blob"]:
                    errors.append(f"Incoming file changed since inventory: {item['original_path']}")
            if "destination" in item:
                preserved += 1
                destination = ROOT / item["destination"]
                if not destination.is_file() or destination.read_bytes() != blob:
                    errors.append(f"Preserved evidence differs from original: {item['destination']}")
    if originals != 97 or preserved != 28 or len(manifest["packages"]) != 9:
        errors.append("Unexpected source inventory size")
    if args.require_retired and any((PROPOSALS / "new").glob("**/*")):
        errors.append("Incoming proposal tree is not empty/absent")
    counts["inventory"] = {"original_files": originals, "preserved_files": preserved,
                            "incoming_files_remaining": incoming}
    for ledger in manifest.get("coverage_ledgers", []):
        if not (MAINTAINED / "integration" / ledger).is_file():
            errors.append(f"Missing coverage ledger: {ledger}")
    bibliography = json.loads((MAINTAINED / "integration/bibliography.json").read_text(encoding="utf-8"))
    accounted_bibkeys = maintained_bibkeys | set(bibliography["merged_aliases"])
    for item in bibliography["entries"]:
        accounted_bibkeys.add(item["source_key"])
        if item["canonical_key"] not in maintained_bibkeys:
            errors.append(f"Missing canonical bibliography entry: {item['canonical_key']}")
    for item in bibliography.get("additional_source_dispositions", []):
        accounted_bibkeys.update(item["source_keys"])
        if "canonical_key" in item and item["canonical_key"] not in maintained_bibkeys:
            errors.append(f"Missing bibliography disposition target: {item['canonical_key']}")
    for key in sorted(incoming_bibkeys - accounted_bibkeys):
        errors.append(f"Incoming bibliography key has no disposition: {key}")
    counts["incoming_bibliography_keys"] = len(incoming_bibkeys)

    receipt_path = MAINTAINED / "integration/validation-2026-09-22/receipt.json"
    if receipt_path.is_file():
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        for artifact in receipt["artifacts"]:
            path = ROOT / artifact["pdf"]
            if hashlib.sha256(path.read_bytes()).hexdigest() != artifact["pdf_sha256"]:
                errors.append(f"Published PDF differs from review receipt: {artifact['pdf']}")
            for source in artifact["tex_inputs"]:
                actual_blob = subprocess.run(
                    ["git", "hash-object", "--path", source["path"], str(ROOT / source["path"])],
                    cwd=ROOT, check=True, capture_output=True, text=True).stdout.strip()
                if actual_blob != source["git_blob"]:
                    errors.append(f"TeX source changed since PDF review: {source['path']}")
        for log in receipt["build"]["logs"]:
            if hashlib.sha256((ROOT / log["path"]).read_bytes()).hexdigest() != log["sha256"]:
                errors.append(f"Archived build log changed: {log['path']}")
        counts["reviewed_artifacts"] = len(receipt["artifacts"])

    markdown_files = [ROOT / "README.md", PROPOSALS / "README.md"]
    for directory in [PROPOSALS / "10-unified-proposal", MAINTAINED]:
        markdown_files.extend(directory.rglob("*.md"))
    for path in markdown_files:
        text = path.read_text(encoding="utf-8")
        for raw in re.findall(r"(?<!!)\[[^\]]+\]\(([^)]+)\)", text):
            target = raw.strip().strip("<>").split("#", 1)[0]
            if not target or re.match(r"[a-zA-Z][a-zA-Z0-9+.-]*:", target):
                continue
            if not (path.parent / unquote(target)).exists():
                errors.append(f"Broken local Markdown link in {path.relative_to(ROOT)}: {raw}")
    counts["markdown_files"] = len(markdown_files)

    result = {"status": "FAIL" if errors else "PASS", "counts": counts, "errors": errors,
              "scope": "Source references, question IDs, local links and archived evidence; no Lean proof or engine validation."}
    print(json.dumps(result, indent=2))
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
