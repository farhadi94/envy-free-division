#!/usr/bin/env python3
"""Rebuild a frozen project import closure in isolation, then audit its axioms.

Shared agent build artifacts are neither read for project modules nor changed.
External pinned package artifacts are reused. Source hashes are rechecked at
the end, so the report distinguishes a passed snapshot from a changed tree.
"""
from __future__ import annotations

import argparse
import ast
import importlib.util
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time
import threading
from dag_scheduler import run_dag

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "verification/lean"
_installed_lake = shutil.which("lake")
BIN = Path(os.environ.get("EF_LEAN_BIN", "")) if os.environ.get("EF_LEAN_BIN") else (
    Path(_installed_lake).parent if _installed_lake else
    ROOT.parents[1] / "tooling/lean-4.35.0-darwin_aarch64/bin")



def script_snapshot(root=ROOT):
    """Freeze the entire active verification-script set, including helper modules."""
    return {path.relative_to(root).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted((root / "scripts").glob("*.py"))}


def load_release_helpers(root=ROOT):
    """Load only the pure parser and literal audit template; never invoke a build."""
    path = root / "scripts/source_selection.py"
    spec = importlib.util.spec_from_file_location("_frozen_release_source_selection", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot load release source-selection helper")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    tree = ast.parse((root / "scripts/verify_lean.py").read_text())
    audit_nodes = [node.value for node in tree.body if isinstance(node, ast.Assign)
                   and any(isinstance(target, ast.Name) and target.id == "AUDIT" for target in node.targets)]
    if len(audit_nodes) != 1:
        raise RuntimeError("Expected one literal verifier AUDIT template")
    audit = ast.literal_eval(audit_nodes[0])
    if not isinstance(audit, str):
        raise RuntimeError("Verifier AUDIT template must be a string")
    return {"AUDIT": audit, "lean_code_only": module.code_only,
            "project_imports": module.project_imports, "check_selection": module.check_selection,
            "check_historical_provenance": module.check_historical_provenance}


class FrozenSource:
    """Path-like reader for applying the shared import parser to frozen text."""
    def __init__(self, text):
        self.text = text

    def read_text(self):
        return self.text



def release_snapshot(helpers, report, root=ROOT):
    """Validate and pin release metadata without trusting previous build artifacts."""
    project = root / "verification/lean"
    names = ["verification/main_results.json", "verification/historical_proofs.json",
             "verification/module_selection.json", "verification/lean/EnvyFreeResearch.lean",
             "verification/lean/AxiomAudit.lean"]
    blobs = {name: (root / name).read_bytes() for name in names}
    report["release_inputs_sha256"] = {
        name: hashlib.sha256(blob).hexdigest() for name, blob in blobs.items()}
    release = json.loads(blobs["verification/main_results.json"])
    rows = release["results"]
    if len(rows) != 4 or {r["id"] for r in rows} != {
            "deterministic_chores", "randomized_upper", "randomized_lower", "mixed_impossibility"}:
        raise RuntimeError("Expected exactly four public main endpoints")
    report["main_results"] = rows
    report["main_results_sha256"] = report["release_inputs_sha256"]["verification/main_results.json"]
    config = {name: (project / name).read_bytes()
              for name in ("lean-toolchain", "lakefile.lean", "lake-manifest.json")}
    report["configuration_sha256"] = {name: hashlib.sha256(blob).hexdigest()
                                      for name, blob in config.items()}
    if config["lean-toolchain"].decode().strip() != "leanprover/lean4:v4.35.0":
        raise RuntimeError("Unexpected project toolchain")
    revisions = {p["name"].strip("«»"): p.get("rev")
                 for p in json.loads(config["lake-manifest.json"])["packages"]}
    expected = release["expected_dependencies"]
    if set(expected) != {"mathlib", "fixed-point-theorems"}:
        raise RuntimeError("Expected pinned mathlib and fixed-point-theorems dependencies")
    for name, revision in expected.items():
        if revisions.get(name) != revision:
            raise RuntimeError("Unexpected dependency revision: " + name)
    report["expected_dependencies"] = expected
    helpers["check_historical_provenance"](json.loads(blobs["verification/historical_proofs.json"]))
    report["historical_proofs_sha256"] = report["release_inputs_sha256"]["verification/historical_proofs.json"]
    current_scripts = script_snapshot(root)
    if report.get("verification_script_sha256", current_scripts) != current_scripts:
        raise RuntimeError("Verification scripts changed before release snapshot")
    report["verification_script_sha256"] = current_scripts
    selected = json.loads(blobs["verification/module_selection.json"])
    selected_paths = helpers["check_selection"](project, selected, release)
    report["module_selection_sha256"] = report["release_inputs_sha256"]["verification/module_selection.json"]
    sources = sorted((project / "EnvyFreeResearch").rglob("*.lean"))
    modules = [".".join(path.relative_to(project).with_suffix("").parts) for path in sources]
    if selected_paths != {path.relative_to(project).as_posix() for path in sources}:
        raise RuntimeError("Selected closure differs from packaged sources")
    for row in rows:
        if not row["declarations"]:
            raise RuntimeError("Empty public declaration list")
    umbrella = "-- Generated by scripts/verify_lean.py; imports every project module.\n"
    umbrella += "".join(f"import {module}\n" for module in modules)
    named = "".join("#check " + name + "\n" for row in rows for name in row["declarations"])
    audit = helpers["AUDIT"].replace("open Lean Elab Command in", named + "\nopen Lean Elab Command in", 1)
    if blobs["verification/lean/EnvyFreeResearch.lean"] != umbrella.encode():
        raise RuntimeError("Umbrella differs from hardened verifier generator")
    if blobs["verification/lean/AxiomAudit.lean"] != audit.encode():
        raise RuntimeError("AxiomAudit differs from hardened verifier generator")
    report["audit_inputs_sha256"] = {
        name: report["release_inputs_sha256"]["verification/lean/" + name]
        for name in ("EnvyFreeResearch.lean", "AxiomAudit.lean")}
    report["release_project_module_count"] = len(modules)
    report["release_project_modules"] = modules
    return audit, set(modules)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", required=True)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--jobs", type=int, choices=range(1, 4), default=1)
    parser.add_argument("--release", action="store_true",
                        help="Audit the complete packaged release with exact hardened verifier inputs")
    parser.add_argument("--preflight", action="store_true",
                        help="Validate frozen source and release inputs without running Lean or writing receipts")
    args = parser.parse_args()
    if args.release and args.modules != ["EnvyFreeResearch"]:
        parser.error("--release requires exactly the entry EnvyFreeResearch")
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", args.name):
        parser.error("--name must be a simple audit directory name")
    os.environ["PATH"] = str(BIN) + os.pathsep + os.environ.get("PATH", "")
    auditor_files = [Path(__file__).resolve(),
                     Path(__file__).resolve().with_name("dag_scheduler.py"),
                     Path(__file__).resolve().with_name("finalize_release_evidence.py"),
                     *sorted((ROOT / "scripts").glob("*.py"))]
    auditor_hashes = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                      for path in auditor_files}
    verification_scripts = script_snapshot(ROOT)
    helpers = load_release_helpers(ROOT)
    code_only = helpers["lean_code_only"]
    logs = ROOT / "formalization/logs" / args.name
    if not args.preflight and logs.exists():
        raise SystemExit("Refusing to overwrite an existing audit: " + str(logs))
    if not args.preflight:
        logs.mkdir(parents=True)
    report_path = logs / "report.json"
    report = {
        "status": "running",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "entry_modules": args.modules,
        "jobs": args.jobs,
        "release_mode": args.release,
        "auditor_sha256": auditor_hashes,
        "verification_script_sha256": verification_scripts,
        "lean_threads_per_job": 1,
        "scope": "Frozen complete local source import closure; external pinned package oleans reused",
        "source_sha256": {},
        "modules": [],
    }

    def save():
        if not args.preflight:
            report_path.write_text(json.dumps(report, indent=2) + "\n")

    sources, ordered, visiting, dependencies = {}, [], set(), {}

    def visit(module):
        if not (module == "EnvyFreeResearch" or module.startswith("EnvyFreeResearch.")) or module in sources:
            return
        if module in visiting:
            raise RuntimeError("Import cycle: " + module)
        visiting.add(module)
        path = Path(*module.split(".")).with_suffix(".lean")
        source = (PROJECT / path).read_bytes().decode("utf-8")
        code = code_only(source)
        forbidden = re.search(r"(?<![\w'])\b(sorry|admit|axiom)\b(?![\w'])", code)
        if forbidden:
            raise RuntimeError("Forbidden source token in " + module)
        deps = helpers["project_imports"](FrozenSource(source))
        for dep in sorted(deps):
            visit(dep)
        dependencies[module] = deps
        sources[module] = (path, source)
        report["source_sha256"][str(path)] = hashlib.sha256(source.encode()).hexdigest()
        visiting.remove(module)
        ordered.append(module)

    try:
        release_audit, release_modules = (release_snapshot(helpers, report)
                                          if args.release else (None, None))
        for module in args.modules:
            visit(module)
        if args.release and set(ordered) != release_modules | {"EnvyFreeResearch"}:
            raise RuntimeError("Release closure does not exactly cover all packaged modules")
        if args.release:
            if report["source_sha256"].get("EnvyFreeResearch.lean") != report["audit_inputs_sha256"]["EnvyFreeResearch.lean"]:
                raise RuntimeError("Umbrella changed before snapshot")
        report["module_count"] = len(ordered)
        report["local_dependencies"] = {m: sorted(dependencies[m]) for m in sorted(dependencies)}
        report["source_lines"] = sum(len(s.splitlines()) for _, s in sources.values())
        if args.preflight:
            if script_snapshot(ROOT) != report["verification_script_sha256"]:
                raise RuntimeError("Verification scripts changed during preflight")
            print(json.dumps({"status": "preflight_passed_not_compiled_or_accepted",
                              "release_mode": args.release, "module_count": len(ordered),
                              "jobs": args.jobs, "entry_modules": args.modules}, indent=2))
            return 0
        base_paths = subprocess.check_output(
            [str(BIN / "lake"), "env", "printenv", "LEAN_PATH"], cwd=PROJECT, text=True
        ).strip().split(os.pathsep)
        project_build = (PROJECT / ".lake/build/lib/lean").resolve()
        external_paths = []
        for entry in base_paths:
            if not entry:
                continue
            path = Path(entry)
            path = (path if path.is_absolute() else PROJECT / path).resolve()
            if path == project_build:
                continue
            if (path / "EnvyFreeResearch").exists() or (path / "EnvyFreeResearch.olean").exists():
                raise RuntimeError("External Lean path contains project artifacts: " + str(path))
            external_paths.append(str(path))
        report["external_lean_paths"] = external_paths
        version = subprocess.check_output([str(BIN / "lean"), "--version"],
                                          cwd=PROJECT, text=True).strip()
        if "version 4.35.0" not in version:
            raise RuntimeError("Unexpected Lean toolchain: " + version)
        report["lean_version"] = version
        if not args.release:
            for name in ("lean-toolchain", "lake-manifest.json", "lakefile.lean"):
                report.setdefault("configuration_sha256", {})[name] = hashlib.sha256(
                    (PROJECT / name).read_bytes()).hexdigest()
        save()
        with tempfile.TemporaryDirectory(prefix="ef-closure-") as temporary:
            temporary = Path(temporary)
            src, build = temporary / "source", temporary / "build"
            src.mkdir()
            build.mkdir()
            (src / "lean-toolchain").write_bytes((PROJECT / "lean-toolchain").read_bytes())
            for path, source in sources.values():
                (src / path).parent.mkdir(parents=True, exist_ok=True)
                (src / path).write_bytes(source.encode("utf-8"))
            env = os.environ.copy()
            env["LEAN_PATH"] = os.pathsep.join([str(build), *external_paths])
            rows = {}
            active = {}
            lock = threading.Lock()
            stopped = threading.Event()

            def abort():
                stopped.set()
                with lock:
                    processes = list(active.values())
                for process in processes:
                    if process.poll() is None:
                        try:
                            process.terminate()
                        except ProcessLookupError:
                            pass
                for process in processes:
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait()

            def compile_module(module):
                path, _ = sources[module]
                output = build / path.with_suffix(".olean")
                output.parent.mkdir(parents=True, exist_ok=True)
                logfile = logs / (module + ".log")
                started = time.monotonic()
                with logfile.open("w") as log:
                    with lock:
                        if stopped.is_set():
                            return {"module": module, "exit_code": -1, "cancelled": True}
                        process = subprocess.Popen(
                            [str(BIN / "lean"), "-j1", str(path), "-o", str(output)],
                            cwd=src, env=env, stdout=log, stderr=subprocess.STDOUT)
                        active[module] = process
                    try:
                        returncode = process.wait()
                    finally:
                        with lock:
                            active.pop(module, None)
                return {"module": module, "exit_code": returncode,
                        "seconds": round(time.monotonic() - started, 3)}

            def record(module, row):
                rows[module] = row
                # Stable topological order in reports, regardless of completion order.
                report["modules"] = [rows[m] for m in ordered if m in rows]
                save()
                print(("PASS " if row["exit_code"] == 0 else "FAIL ") + module, flush=True)

            run_dag(dependencies, args.jobs, compile_module, record, abort)
            audit = release_audit if args.release else helpers["AUDIT"].replace(
                "import EnvyFreeResearch\n", "".join("import " + m + "\n" for m in args.modules))
            (src / "ClosureAudit.lean").write_text(audit)
            with (logs / "axioms.log").open("w") as log:
                result = subprocess.run([str(BIN / "lean"), "-j1", "ClosureAudit.lean"],
                                        cwd=src, env=env, stdout=log, stderr=subprocess.STDOUT)
            if result.returncode:
                raise RuntimeError("Axiom audit failed; see axioms.log")
            match = re.search(r"AXIOM AUDIT PASSED: (\d+) theorem declarations",
                              (logs / "axioms.log").read_text())
            if not match:
                raise RuntimeError("Axiom audit passed marker missing")
            report["theorem_declaration_count"] = int(match.group(1))
        changed = [path for path, digest in report["source_sha256"].items()
                   if not (PROJECT / path).is_file() or hashlib.sha256((PROJECT / path).read_bytes()).hexdigest() != digest]
        changed_config = [path for path, digest in report["configuration_sha256"].items()
                          if not (PROJECT / path).is_file() or hashlib.sha256((PROJECT / path).read_bytes()).hexdigest() != digest]
        changed_auditor = [path for path, digest in report["auditor_sha256"].items()
                           if not (ROOT / path).is_file() or hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest]
        changed_release = [path for path, digest in report.get("release_inputs_sha256", {}).items()
                           if not (ROOT / path).is_file() or
                           hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest]
        if script_snapshot(ROOT) != report["verification_script_sha256"]:
            changed_auditor.append("verification_script_set_or_content")
        if args.release:
            current_modules = {".".join(p.relative_to(PROJECT).with_suffix("").parts)
                               for p in (PROJECT / "EnvyFreeResearch").rglob("*.lean")}
            if current_modules != release_modules:
                changed_release.append("packaged_project_module_set")
        report["release_inputs_changed_during_audit"] = changed_release
        report["auditor_changed_during_audit"] = changed_auditor
        report["sources_changed_during_audit"] = changed
        report["configuration_changed_during_audit"] = changed_config
        report["snapshot_passed"] = True
        report["status"] = "passed" if not (changed or changed_config or changed_auditor or changed_release) else "snapshot_passed_current_sources_changed"
        report["allowed_axioms"] = ["propext", "Classical.choice", "Quot.sound"]
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
        print(report["status"].upper() + ": " + str(report_path), flush=True)
        return 0 if not (changed or changed_config or changed_auditor or changed_release) else 2
    except BaseException as exc:
        report["status"] = "interrupted" if isinstance(exc, KeyboardInterrupt) else "failed"
        report["error"] = str(exc)
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
        print(str(exc), flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
