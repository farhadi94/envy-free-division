#!/usr/bin/env python3
"""Package the actual TeX input closure and verify a clean local rebuild.

This creates a source-only upload, separate from the complete Lean artifact.
The check is local; it does not submit to or compile on arXiv's servers.
"""
from __future__ import annotations

from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tempfile
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
DIST = ROOT / "dist"
ARCHIVE = DIST / "envy_free_arxiv_source.zip"


def digest(data: bytes) -> str:
    return sha256(data).hexdigest()


def normalized_pdf_text(text: str) -> str:
    # Preserve the hyphen itself when a retained compound word, such as
    # 'local-order', is wrapped after its hyphen in only one of the builds.
    # This changes only layout whitespace, never letters or punctuation.
    text = re.sub(r"(?<=\w-)[\t ]*\n[\t ]*(?=\w)", "", text)
    return " ".join(text.split())


def safe_name(name: str) -> str:
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or "\\" in name:
        raise ValueError(f"Unsupported input path: {name}")
    return path.as_posix()


def input_files() -> dict[str, bytes]:
    """Resolve the manuscript's literal, upload-root-relative input paths."""
    files: dict[str, bytes] = {}
    pending = ["paper.tex"]
    while pending:
        name = safe_name(pending.pop())
        if name in files:
            continue
        path = PAPER / name
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"Missing regular source file: {name}")
        files[name] = path.read_bytes()
        source = re.sub(r"(?<!\\)%[^\n]*", "", files[name].decode())
        for target in re.findall(r"\\(?:input|include)\{([^}]+)\}", source):
            pending.append(target if Path(target).suffix else target + ".tex")
    for name in ["references.bib", "paper.bbl", "alphaurl-safe.bst"]:
        files[name] = (PAPER / name).read_bytes()
    return dict(sorted(files.items()))


def main() -> None:
    DIST.mkdir(exist_ok=True)
    build = json.loads((PAPER / "build_manifest.json").read_text())
    if build["status"] != "build_passed_not_mathematical_acceptance" or build["diagnostics"]:
        raise ValueError("Build the canonical paper successfully before packaging.")
    for name, expected in build["sha256"].items():
        if digest((PAPER / name).read_bytes()) != expected:
            raise ValueError(f"Canonical build is stale: {name}")
    files = input_files()
    engine = shutil.which("tectonic")
    if engine is None:
        engine = str(ROOT.parent / "tooling/tectonic-0.17.0/tectonic")
    canonical_text = subprocess.check_output(
        ["pdftotext", "-layout", str(PAPER / "paper.pdf"), "-"], text=True)

    # Publish the new archive only after all checks pass; keep the previous
    # delivery available if a build or comparison fails.
    with tempfile.TemporaryDirectory(prefix="envy-free-arxiv-") as temporary:
        temp = Path(temporary)
        candidate = temp / ARCHIVE.name
        with ZipFile(candidate, "w", compression=ZIP_DEFLATED, compresslevel=9) as archive:
            for name, data in files.items():
                info = ZipInfo(name, date_time=(2026, 11, 7, 0, 0, 0))
                info.compress_type = ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                archive.writestr(info, data)
        extracted = temp / "extracted"
        with ZipFile(candidate) as archive:
            if archive.testzip() is not None or set(archive.namelist()) != set(files):
                raise ValueError("Archive integrity check failed.")
            archive.extractall(extracted)
        for name, data in files.items():
            if (extracted / name).read_bytes() != data:
                raise ValueError(f"Extraction changed a source: {name}")
        process = subprocess.run(
            [engine, "--keep-logs", "--keep-intermediates", "paper.tex"],
            cwd=extracted, text=True, capture_output=True)
        log = process.stdout + process.stderr
        (DIST / "arxiv_source_build.log").write_text(log)
        if process.returncode:
            raise RuntimeError("Clean source build failed; see dist/arxiv_source_build.log.")
        diagnostics = []
        for name in ["paper.log", "paper.blg"]:
            for line in (extracted / name).read_text().splitlines():
                if any(marker in line for marker in [
                    r"Overfull \hbox", r"Overfull \vbox", "LaTeX Warning:",
                    "Package natbib Warning:", "Package amsmath Warning:",
                    "undefined references", "undefined citations", "Warning--",
                ]):
                    diagnostics.append(f"{name}: {line}")
                if name.endswith(".blg") and re.search(r"\d+ error message", line):
                    diagnostics.append(f"{name}: {line}")
        if diagnostics:
            raise ValueError("Clean source build diagnostics:\n" + "\n".join(diagnostics))
        fresh_text = subprocess.check_output(
            ["pdftotext", "-layout", str(extracted / "paper.pdf"), "-"], text=True)
        (DIST / "arxiv_source_pdf_text.txt").write_text(fresh_text)
        info = subprocess.check_output(["pdfinfo", str(extracted / "paper.pdf")], text=True)
        pages = int(re.search(r"Pages:\s+(\d+)", info).group(1))
        if pages != build["pages"]:
            raise ValueError("Clean build page count differs from the canonical paper.")
        if normalized_pdf_text(canonical_text) != normalized_pdf_text(fresh_text):
            raise ValueError("Clean build text differs beyond layout whitespace.")
        for name, data in files.items():
            if (PAPER / name).read_bytes() != data:
                raise ValueError(f"Source changed during verification: {name}")
        receipt = {
            "status": "passed_local_source_package_verification",
            "verified_at_utc": datetime.now(timezone.utc).isoformat(),
            "archive": ARCHIVE.name,
            "archive_sha256": digest(candidate.read_bytes()),
            "archive_size_bytes": candidate.stat().st_size,
            "file_count": len(files),
            "files_sha256": {name: digest(data) for name, data in files.items()},
            "canonical_pdf_sha256": build["sha256"]["paper.pdf"],
            "clean_build_pdf_sha256": digest((extracted / "paper.pdf").read_bytes()),
            "page_count": pages,
            "tex_input_closure_complete": True,
            "clean_extraction_local_build": "passed with Tectonic",
            "whitespace_normalized_pdf_text_matches_canonical": True,
            "comparison_note": "PDF bytes and line wrapping need not be reproducible; extracted content and page count are checked after whitespace normalization, including joining a line break after a retained word hyphen without removing the hyphen.",
            "arxiv_server_build_tested": False,
            "recommended_top_level_file": "paper.tex",
            "recommended_arxiv_processor": "xelatex",
        }
        shutil.copyfile(candidate, ARCHIVE)
        (DIST / "arxiv_source_verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: value for key, value in receipt.items() if key != "files_sha256"}, indent=2))


if __name__ == "__main__":
    main()
