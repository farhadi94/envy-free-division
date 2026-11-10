#!/usr/bin/env python3
"""Verify an untouched extracted artifact or ZIP; no external tools required."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import tempfile
import zipfile

from source_selection import check_selection, check_historical_provenance


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(root: Path, name: str):
    return json.loads((root / name).read_text())


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_hashes(root: Path, hashes: dict, prefix: str = ""):
    for name, expected in hashes.items():
        path = root / prefix / name
        require(path.is_file(), f"Missing checked file: {path}")
        require(digest(path) == expected, f"Hash mismatch: {path}")


def check_editorial_amendment(root: Path, record: dict, build: dict):
    """Verify an exact editorial delta without claiming a new proof review."""
    check_hashes(root, {record["path"]: record["sha256"]})
    amendment = read_json(root, record["path"])
    require(amendment["status"] == "editorial_only", "Unknown amendment scope.")
    base_path = amendment["reviewed_snapshot"]
    require(digest(root / base_path) == amendment["reviewed_snapshot_sha256"],
            "Editorial base snapshot differs.")
    base = read_json(root, base_path)
    before, after = base["paper_source_sha256"], build["sha256"]
    require(amendment["reviewed_pdf_sha256"] == base["pdf_sha256"] and
            amendment["pdf_sha256"] == after["paper.pdf"],
            "Editorial amendment PDF mismatch.")
    require(set(before) == set(after), "Editorial amendment changed the file set.")
    changed = {name for name in before if before[name] != after[name]}
    require(changed - {"paper.pdf"} == set(amendment["edits"]),
            "Unrecorded source change after review.")
    for name, edit in amendment["edits"].items():
        current = (root / "paper" / name).read_bytes()
        old, new = edit["before_text"].encode(), edit["after_text"].encode()
        require(new and current.count(new) == 1, "Ambiguous editorial replacement.")
        restored = current.replace(new, old, 1)
        require(hashlib.sha256(restored).hexdigest() == before[name],
                f"Reversing the editorial edit did not restore reviewed source: {name}")
    return amendment


def check_scoped_revision(root: Path, record: dict, build: dict, lean: dict):
    """Bind a reviewed mixed-theorem revision to its preserved other results."""
    check_hashes(root, {record["path"]: record["sha256"]})
    revision = read_json(root, record["path"])
    require(revision["status"] == "mixed_extremal_revision_reviewed",
            "Unknown substantive revision status.")
    baseline_path = revision["baseline_snapshot"]
    require(digest(root / baseline_path) == revision["baseline_snapshot_sha256"],
            "Revision baseline snapshot differs.")
    baseline = read_json(root, baseline_path)
    before, after = baseline["paper_source_sha256"], build["sha256"]
    require(set(before) == set(after), "Revision changed the paper input file set.")
    changed = {n for n in before if n != "paper.pdf" and before[n] != after[n]}
    require(changed == set(revision["changed_source_sha256"]),
            "Unrecorded manuscript change in the reviewed revision.")
    check_hashes(root, revision["changed_source_sha256"], "paper")
    require(revision["pdf_sha256"] == after["paper.pdf"], "Revision PDF differs.")

    statements = read_json(root, revision["baseline_statements"])
    require(hashlib.sha256(statements["text"].encode()).hexdigest() ==
            statements["sha256"] == before["sections/general_results.tex"],
            "Preserved theorem statements differ from the baseline.")
    separator = r"\subsection{Mixed cake and chores}"
    current = (root / "paper/sections/general_results.tex").read_text()
    require(current.count(separator) == statements["text"].count(separator) == 1 and
            current.split(separator)[0] == statements["text"].split(separator)[0],
            "One of the other three main theorem statements changed.")
    check_hashes(root, revision["unchanged_nonmixed_proof_sha256"], "paper")
    for name, expected in revision["unchanged_nonmixed_proof_sha256"].items():
        require(before[name] == expected, "An allegedly unchanged proof differs.")

    old_lean = baseline["lean_source_sha256"]
    require(all(lean["source_sha256"].get(n) == h for n, h in old_lean.items()),
            "A previously audited Lean module changed.")
    added = {n: h for n, h in lean["source_sha256"].items() if n not in old_lean}
    require(added == revision["new_lean_source_sha256"],
            "New Lean modules do not match the reviewed revision.")

    whole = read_json(root, revision["whole_source_receipt"])
    require(not whole["unresolved_required_findings"], "Whole change review is open.")
    check_hashes(root, whole["candidate_source_sha256"], "paper")
    require(changed <= set(whole["candidate_source_sha256"]),
            "A changed manuscript file is outside the new whole change review.")
    reviewed_lean = {"EnvyFreeResearch/" + Path(n).name: h
                    for n, h in whole["supporting_lean_source_sha256"].items()}
    require(all(reviewed_lean.get(n) == h for n, h in added.items()),
            "New Lean source is outside the reviewed coverage.")
    mixed = read_json(root, revision["mixed_source_receipt"])
    require(not mixed["unresolved_required_findings"], "Mixed proof review is open.")
    mixed_hashes = {n.removeprefix("paper_candidate/"): h
                    for n, h in mixed["reviewed_sources_sha256"].items()}
    require({"sections/general_results.tex", "sections/mixed_lower_proof.tex"}
            <= set(mixed_hashes), "Mixed review omits the statement or proof.")
    check_hashes(root, mixed_hashes, "paper")
    return revision


def check_evidence(root: Path):
    """Check that all receipts concern the packaged sources and PDF."""
    build = read_json(root, "paper/build_manifest.json")
    require(build["status"] == "build_passed_not_mathematical_acceptance",
            "Paper build did not pass.")
    require(not build["diagnostics"], "Unresolved build diagnostics.")
    require(build["comparison_table_page"] <= 4, "Results table is too late.")
    check_hashes(root, build["sha256"], "paper")
    pdf_hash = build["sha256"]["paper.pdf"]

    lean = read_json(root, "verification/lean_status.json")
    require(lean["status"] == "passed", "Lean audit did not pass.")
    require(set(lean["allowed_axioms"]) ==
            {"propext", "Classical.choice", "Quot.sound"},
            "Unexpected allowed-axiom policy.")
    check_hashes(root, lean["source_sha256"], "verification/lean")
    modules = {str(p.relative_to(root / "verification/lean"))
               for p in (root / "verification/lean/EnvyFreeResearch").rglob("*.lean")}
    require(modules == set(lean["source_sha256"]), "Lean module set differs from audit.")
    require(len(modules) == lean["module_count"], "Lean module count mismatch.")
    marker = f"AXIOM AUDIT PASSED: {lean['theorem_declaration_count']} theorem declarations"
    require(marker in (root / "verification/lean.log").read_text(),
            "Lean axiom-audit success marker missing.")
    if "evidence_sha256" in lean:
        check_hashes(root, lean["evidence_sha256"])
        cold_path = "review/final_cold_audit/report.json"
        require(cold_path in lean["evidence_sha256"], "Cold-audit report is not hash-bound.")
        cold = read_json(root, cold_path)
        require(cold.get("status") == "passed" and cold.get("snapshot_passed") is True
                and cold.get("release_mode") is True,
                "Cold source audit did not pass.")
        require({k: v for k, v in cold["source_sha256"].items()
                 if k != "EnvyFreeResearch.lean"} == lean["source_sha256"],
                "Cold audit concerns a different project source set.")
        for key in ("main_results_sha256", "module_selection_sha256",
                    "historical_proofs_sha256", "configuration_sha256",
                    "audit_inputs_sha256", "verification_script_sha256"):
            require(cold[key] == lean[key], "Cold audit binding differs: " + key)
        expected_modules = {".".join(Path(p).with_suffix("").parts) for p in modules}
        expected_modules.add("EnvyFreeResearch")
        require(len(cold["modules"]) == len(expected_modules)
                and {r["module"] for r in cold["modules"]} == expected_modules
                and all(r["exit_code"] == 0 and not r.get("cancelled") for r in cold["modules"]),
                "Cold audit has missing or failed project compilations.")

    endpoints = read_json(root, "verification/main_results.json")
    require(len(endpoints["results"]) == 4 and
            {r["id"] for r in endpoints["results"]} == {"deterministic_chores", "randomized_upper", "randomized_lower", "mixed_impossibility"},
            "Expected four distinct public main endpoints.")
    require(lean["main_results"] == endpoints["results"], "Main endpoint audit mismatch.")
    require(lean["main_results_sha256"] == digest(root / "verification/main_results.json"), "Endpoint manifest changed after audit.")
    for row in endpoints["results"]:
        source = "/".join(row["module"].split(".")) + ".lean"
        require(source in lean["source_sha256"] and row["declarations"], "Main endpoint not included in checked sources.")
    check_hashes(root, lean["configuration_sha256"], "verification/lean")
    check_hashes(root, lean["audit_inputs_sha256"], "verification/lean")
    check_hashes(root, lean["verification_script_sha256"])
    require({str(path.relative_to(root)) for path in (root / "scripts").glob("*.py")} ==
            set(lean["verification_script_sha256"]), "Verification script set changed after audit.")
    require(lean["historical_proofs_sha256"] == digest(root / "verification/historical_proofs.json"),
            "Historical provenance changed after audit.")
    provenance = read_json(root, "verification/historical_proofs.json")
    check_historical_provenance(provenance)
    selection = read_json(root, "verification/module_selection.json")
    selected = check_selection(root / "verification/lean", selection, endpoints)
    require(selected == modules, "Selected source inventory differs from checked sources.")
    require(lean["module_selection_sha256"] == digest(root / "verification/module_selection.json"),
            "Selected module manifest changed after audit.")

    snapshot = read_json(root, "review/final_snapshot.json")
    require(snapshot["pdf_sha256"] == pdf_hash, "Final snapshot PDF differs.")
    require(snapshot["paper_source_sha256"] == build["sha256"],
            "Final snapshot paper sources differ.")
    require(snapshot["lean_source_sha256"] == lean["source_sha256"],
            "Final snapshot Lean sources differ.")
    require(snapshot["coverage_sha256"] == digest(root / "verification/coverage.json"),
            "Coverage record changed after final snapshot.")
    coverage = read_json(root, "verification/coverage.json")
    require(coverage["main_theorem_count"] == 4 and
            coverage["main_theorems_fully_formalized"] == 4,
            "Formalization scope is inconsistent.")
    for row in coverage["coverage"]:
        check_hashes(root, row["proof_source_sha256"], "paper/sections")

    acceptance = read_json(root, "review/acceptance.json")
    require(acceptance["status"] == "all_five_reviews_closed_no_required_repairs",
            "Independent reviews are not closed.")
    require(acceptance["pdf_sha256"] == pdf_hash, "Acceptance concerns a different PDF.")
    require(acceptance["final_snapshot_sha256"] ==
            digest(root / "review/final_snapshot.json"), "Acceptance snapshot differs.")
    require(len(acceptance["reviews"]) == 5, "Expected five independent reviews.")
    require({r["role"] for r in acceptance["reviews"]} ==
            {"chores", "upper", "lower", "mixed", "whole"}, "Review roles differ.")
    amendment = None
    revision = None
    if "editorial_amendment" in acceptance:
        amendment = check_editorial_amendment(root, acceptance["editorial_amendment"], build)
    if "scoped_revision" in acceptance:
        revision = check_scoped_revision(root, acceptance["scoped_revision"], build, lean)
    for review in acceptance["reviews"]:
        require(review["accepted"] and not review["unresolved_required_findings"],
                f"Unresolved review: {review['role']}")
        check_hashes(root, review["files_sha256"])
        reviewed = read_json(root, review["reviewed_snapshot"])
        require(reviewed["pdf_sha256"] == review["reviewed_pdf_sha256"],
                "Reviewed PDF does not match its preserved snapshot.")
        if amendment:
            require(review["reviewed_snapshot"] == amendment["reviewed_snapshot"],
                    "Editorial amendment does not extend this review snapshot.")
        receipt = read_json(root, review["receipt"])
        pinned_pdf = receipt
        for key in review["receipt_pdf_field"]:
            pinned_pdf = pinned_pdf[key]
        require(pinned_pdf == review["reviewed_pdf_sha256"], "Receipt PDF mismatch.")
        for name, expected in acceptance["unchanged_proof_and_statement_sha256"].items():
            require(reviewed["paper_source_sha256"][name] == expected,
                    f"A substantive source changed after review: {name}")
        if revision and review["role"] in {"chores", "upper", "lower"}:
            old_statements = read_json(root, revision.get(
                "historical_statements", revision["baseline_statements"]))
            require(hashlib.sha256(old_statements["text"].encode()).hexdigest()
                    == old_statements["sha256"],
                    "Historical statement text does not match its hash.")
            current_statements = (root / "paper/sections/general_results.tex").read_text()
            separator = r"\subsection{Mixed cake and chores}"
            require(old_statements["text"].split(separator)[0]
                    == current_statements.split(separator)[0],
                    "A historically reviewed nonmixed theorem statement changed.")
            require(reviewed["paper_source_sha256"]["sections/general_results.tex"]
                    == old_statements["sha256"],
                    "Historical theorem statements differ from the preserved baseline.")
            require(all(lean["source_sha256"].get(n) == h
                        for n, h in reviewed["lean_source_sha256"].items()),
                    "A historically reviewed Lean source changed.")
            for name in revision["proof_files_by_role"][review["role"]]:
                content = (root / "paper" / name).read_bytes()
                expected = reviewed["paper_source_sha256"][name]
                if hashlib.sha256(content).hexdigest() != expected:
                    require(name == "sections/chore_proof.tex",
                            "A historical proof changed substantively.")
                    sentence = b"Here $\\sqcup$ denotes disjoint union.\n"
                    require(content.count(sentence) == 1,
                            "The recorded notation clarification is ambiguous.")
                    content = content.replace(sentence, b"", 1)
                require(hashlib.sha256(content).hexdigest() == expected,
                        "Historical proof source is not preserved.")
        else:
            require(reviewed["lean_source_sha256"] == lean["source_sha256"],
                    "Lean sources changed after review.")
    check_hashes(root, acceptance["unchanged_proof_and_statement_sha256"], "paper")
    whole = next(r for r in acceptance["reviews"] if r["role"] == "whole")
    require(whole["reviewed_pdf_sha256"] == pdf_hash or
            (amendment and whole["reviewed_pdf_sha256"] == amendment["reviewed_pdf_sha256"]),
            "Whole-paper reviewer has not closed the final presentation revision.")

    visual = read_json(root, "review/visual_check.json")
    require(visual["status"] == "passed" and visual["pdf_sha256"] == pdf_hash,
            "Final visual review is missing or stale.")
    return {"pages": build["pages"], "pdf_sha256": pdf_hash,
            "lean_modules": lean["module_count"],
            "lean_authored_theorems": lean["authored_theorem_declaration_count"],
            "lean_all_theorems": lean["theorem_declaration_count"],
            "independent_reviews": len(acceptance["reviews"]),
            "editorial_amendments_after_review": int(amendment is not None),
            "new_scoped_reviews_in_current_revision": 2 if revision else 0}


def verify_directory(root: Path):
    manifest = read_json(root, "MANIFEST.json")
    require(manifest["schema"] == 1, "Unknown manifest schema.")
    expected = manifest["files"]
    actual = set()
    for path in root.rglob("*"):
        require(not path.is_symlink(), f"Unexpected symlink: {path}")
        if path.is_file():
            actual.add(path.relative_to(root).as_posix())
    require(actual == set(expected) | {"MANIFEST.json"},
            "Archive file set differs from manifest.")
    for name, record in expected.items():
        require((root / name).stat().st_size == record["bytes"], f"Size mismatch: {name}")
        require(digest(root / name) == record["sha256"], f"Hash mismatch: {name}")
    details = check_evidence(root)
    return {"status": "passed", "manifest_files": len(expected), **details,
            "scope": "Archive bytes and existing verification/review receipts; no new Lean build or mathematical review."}


def verify_zip(path: Path):
    with tempfile.TemporaryDirectory(prefix="envy-free-extraction-") as temp:
        with zipfile.ZipFile(path) as archive:
            names = archive.namelist()
            require(len(names) == len(set(names)), "Duplicate ZIP entries.")
            for name in names:
                rel = PurePosixPath(name)
                require(not rel.is_absolute() and ".." not in rel.parts and
                        "\\" not in name, f"Unsafe ZIP entry: {name}")
                require(not name.endswith("/"), "Only file entries are expected.")
                mode = archive.getinfo(name).external_attr >> 16
                require(mode & 0o170000 != 0o120000, f"ZIP symlink: {name}")
            require(archive.testzip() is None, "ZIP checksum failure.")
            archive.extractall(temp)
        return {**verify_directory(Path(temp)), "zip_sha256": digest(path),
                "zip_bytes": path.stat().st_size}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", nargs="?", type=Path,
                        default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    result = verify_zip(args.path) if args.path.is_file() else verify_directory(args.path)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
