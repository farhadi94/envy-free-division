#!/usr/bin/env python3
"""Freeze the focused artifact only after all review and verification gates pass."""
from __future__ import annotations

from datetime import datetime, timezone
import json
from pathlib import Path
import tempfile
import shutil
import zipfile

from verify_package import check_evidence, digest, verify_directory, verify_zip

ROOT = Path(__file__).resolve().parents[1]


def selected_files():
    names = {"README.md", "THIRD_PARTY_NOTICES.md"}
    names.update(str(p.relative_to(ROOT)) for p in (ROOT / "licenses").glob("*.txt"))
    paper = ROOT / "paper"
    names.update(str(p.relative_to(ROOT)) for p in paper.rglob("*.tex"))
    names.update("paper/" + name for name in [
        "paper.pdf", "references.bib", "alphaurl-safe.bst", "bibliography_style.json",
        "build_manifest.json", "build_inputs.json", "build.log", "paper.log",
        "paper.blg", "paper.bbl", "paper.pdfinfo.txt", "paper.txt"])
    names.update("verification/" + name for name in [
        "lean_status.json", "lean.log", "coverage.json", "module_selection.json",
        "main_results.json", "historical_proofs.json"])
    lean = ROOT / "verification/lean"
    names.update(str(p.relative_to(ROOT)) for p in (lean / "EnvyFreeResearch").rglob("*.lean"))
    names.update("verification/lean/" + name for name in [
        "EnvyFreeResearch.lean", "AxiomAudit.lean", "lakefile.lean",
        "lake-manifest.json", "lean-toolchain"])
    names.update(str(p.relative_to(ROOT)) for p in (ROOT / "scripts").glob("*.py"))
    names.update(str(p.relative_to(ROOT)) for p in (ROOT / "source").glob("*.json"))
    names.update(str(p.relative_to(ROOT)) for p in (ROOT / "review").rglob("*")
                 if p.is_file() and p.suffix in {".md", ".json", ".py", ".lean", ".log"}
                 and "compiled" not in p.parts and "__pycache__" not in p.parts)
    return sorted(names)


def main():
    check_evidence(ROOT)
    dist = ROOT / "dist"
    dist.mkdir(exist_ok=True)
    archive_path = dist / "envy_free_focused_submission.zip"
    with tempfile.TemporaryDirectory(prefix="envy-free-package-") as temp:
        stage = Path(temp)
        files = {}
        for name in selected_files():
            src, dst = ROOT / name, stage / name
            if src.is_symlink() or not src.is_file():
                raise ValueError(f"Package input is missing or a symlink: {name}")
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, dst)
            files[name] = {"sha256": digest(dst), "bytes": dst.stat().st_size}
        manifest = {"schema": 1, "created_at_utc": datetime.now(timezone.utc).isoformat(),
                    "description": "Four-result article, sources, complete main Lean endpoints and their dependencies, historical proof provenance, and scoped independent review records.",
                    "files": files}
        (stage / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
        verify_directory(stage)
        with zipfile.ZipFile(archive_path, "w", compression=zipfile.ZIP_DEFLATED,
                             compresslevel=9) as archive:
            for name in sorted([*files, "MANIFEST.json"]):
                info = zipfile.ZipInfo(name, date_time=(2026, 11, 7, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                archive.writestr(info, (stage / name).read_bytes())
        shutil.copyfile(stage / "MANIFEST.json", dist / "MANIFEST.json")
    result = verify_zip(archive_path)
    (dist / "package_verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"archive": str(archive_path), **result}, indent=2))


if __name__ == "__main__":
    main()
