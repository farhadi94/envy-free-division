#!/usr/bin/env python3
"""Build the focused article and check its sources, citations and early table."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
engine = shutil.which("tectonic")
if engine is None:
    candidate = ROOT.parent / "tooling/tectonic-0.17.0/tectonic"
    if not candidate.is_file():
        raise SystemExit("Install Tectonic 0.17.0 and make it available on PATH.")
    engine = str(candidate)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

sources = sorted([*PAPER.rglob("*.tex"), PAPER / "references.bib",
                  PAPER / "alphaurl-safe.bst"])
before = {str(p.relative_to(PAPER)): digest(p) for p in sources}
(PAPER / "build_inputs.json").write_text(json.dumps(before, indent=2) + "\n")
run = subprocess.run([engine, "--keep-logs", "--keep-intermediates", "paper.tex"],
                     cwd=PAPER, text=True, capture_output=True)
(PAPER / "build.log").write_text(run.stdout + run.stderr)
print(run.stdout + run.stderr, end="")
if run.returncode:
    raise SystemExit(run.returncode)
info = subprocess.check_output(["pdfinfo", str(PAPER / "paper.pdf")], text=True)
(PAPER / "paper.pdfinfo.txt").write_text(info)
subprocess.run(["pdftotext", "-layout", str(PAPER / "paper.pdf"),
                str(PAPER / "paper.txt")], check=True)
issues = []
for filename in ["paper.log", "paper.blg"]:
    for line in (PAPER / filename).read_text().splitlines():
        if any(t in line for t in [
            r"Overfull \hbox", r"Overfull \vbox", "LaTeX Warning:",
            "Package natbib Warning:", "Package amsmath Warning:",
            "undefined references", "undefined citations", "Warning--",
        ]):
            issues.append(filename + ": " + line)
        if filename.endswith(".blg") and re.search(r"\d+ error message", line):
            issues.append(filename + ": " + line)
after = {str(p.relative_to(PAPER)): digest(p) for p in sources}
if before != after:
    issues.append("Source bytes changed during the build.")
aux = (PAPER / "paper.aux").read_text()
labels = {}
for name, number, page in re.findall(
        r"\\newlabel\{([^}]+)\}\{\{([^}]+)\}\{(\d+)\}", aux):
    labels[name] = {"number": number, "page": int(page)}
table_page = labels.get("tab:comparison", {}).get("page")
if table_page is None or table_page > 4:
    issues.append("The results table is not within the first four PDF pages.")
for path in sources:
    if path.suffix != ".tex":
        continue
    text = path.read_text()
    for m in re.finditer(r"\\E(?![A-Za-z])", text):
        if text[m.end():m.end()+1] not in ["{", "}"]:
            issues.append(str(path.relative_to(PAPER)) +
                          ": expectation must use the bracket-enforcing macro.")
record = {
    "status": "failed" if issues else "build_passed_not_mathematical_acceptance",
    "built_at_utc": datetime.now(timezone.utc).isoformat(),
    "pages": int(re.search(r"Pages:\s+(\d+)", info).group(1)),
    "comparison_table_page": table_page,
    "diagnostics": issues,
    "labels": labels,
    "sha256": {**after, "paper.pdf": digest(PAPER / "paper.pdf")},
}
(PAPER / "build_manifest.json").write_text(json.dumps(record, indent=2) + "\n")
if issues:
    print("\n".join(issues))
    raise SystemExit("Manuscript build diagnostics failed.")
print(f"Clean {record['pages']}-page article; results table on page {table_page}.")
