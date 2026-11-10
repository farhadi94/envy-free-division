"""Validate the exact local import closure of the released theorem roots."""
from pathlib import Path
import re


def check_historical_provenance(record: dict) -> None:
    """Check archival metadata without treating old sources as live dependencies.

    Git object contents were checked when this record was created. An offline
    artifact check validates its structure and frozen hash, not remote history.
    """
    if (record.get("schema") != 2 or record.get("kind") != "historical_git_provenance"
            or record.get("requires_current_source_files") is not False):
        raise ValueError("Invalid historical proof provenance schema.")
    git = record["git"]
    if (git.get("object_format") != "sha1" or not git.get("repository")
            or not re.fullmatch(r"[0-9a-f]{40}", git.get("commit", ""))):
        raise ValueError("Invalid historical Git identity.")
    sources = record["sources"]
    if not sources or record["source_record_count"] != len(sources):
        raise ValueError("Historical source record count differs.")
    for name, source in sources.items():
        path = Path(name)
        if (path.is_absolute() or ".." in path.parts or "\\" in name
                or not name.startswith("EnvyFreeResearch/") or path.suffix != ".lean"
                or source["git_path"] != "verification/lean/" + name
                or not re.fullmatch(r"[0-9a-f]{40}", source["git_blob_oid"])
                or not re.fullmatch(r"[0-9a-f]{64}", source["content_sha256"])
                or not isinstance(source["bytes"], int) or source["bytes"] < 0):
            raise ValueError("Invalid historical source identity: " + name)


def code_only(text: str) -> str:
    """Remove nested comments and strings, preserving line boundaries."""
    out = list(text)
    i, depth, state = 0, 0, "code"
    while i < len(text):
        if state == "block":
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
                if depth == 0:
                    state = "code"
                continue
            if text[i] != "\n":
                out[i] = " "
        elif state == "line":
            if text[i] == "\n":
                state = "code"
            else:
                out[i] = " "
        elif state == "string":
            if text[i] == "\\" and i + 1 < len(text):
                out[i] = " "
                if text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
                continue
            if text[i] == '"':
                state = "code"
            if text[i] != "\n":
                out[i] = " "
        elif text.startswith("/-", i):
            state, depth = "block", 1
            out[i:i + 2] = "  "
            i += 2
            continue
        elif text.startswith("--", i):
            state = "line"
            out[i:i + 2] = "  "
            i += 2
            continue
        elif text[i] == '"':
            state = "string"
            out[i] = " "
        i += 1
    if state in {"block", "string"}:
        raise ValueError("Unterminated comment or string in Lean source.")
    return "".join(out)


def project_imports(path: Path) -> set[str]:
    result = set()
    for line in code_only(path.read_text()).splitlines():
        match = re.match(r"\s*(?:public\s+)?import\s+(.+)$", line)
        if match:
            for module in match.group(1).split():
                if module == "EnvyFreeResearch" or module.startswith("EnvyFreeResearch."):
                    result.add(module)
    return result


def check_selection(project: Path, selection: dict, endpoints: dict) -> set[str]:
    """Reject missing dependencies, stale extras, and unapproved extra roots.

    Module names in the selection are relative to EnvyFreeResearch. The
    endpoint manifest explicitly approves both theorem and audit roots.
    Historical proof provenance is deliberately not an active-source root.
    """
    roots = {row["module"] for row in endpoints["results"]}
    roots.update(endpoints.get("supplemental_modules", []))
    for row in endpoints["results"]:
        roots.update(row.get("supporting_modules", []))
    declared_roots = {"EnvyFreeResearch." + n for n in selection["roots"]}
    if roots != declared_roots:
        raise ValueError("Selected roots differ from the approved endpoint/audit roots.")
    files = {".".join(p.relative_to(project).with_suffix("").parts): p
             for p in (project / "EnvyFreeResearch").rglob("*.lean")}
    visited, active = set(), set()

    def visit(module: str):
        if module in active:
            raise ValueError("Cyclic project import: " + module)
        if module in visited:
            return
        if module not in files:
            raise ValueError("Missing selected project dependency: " + module)
        active.add(module)
        for dependency in sorted(project_imports(files[module])):
            visit(dependency)
        active.remove(module)
        visited.add(module)

    for root in sorted(roots):
        visit(root)
    listed = ["EnvyFreeResearch." + n for n in selection["modules"]]
    if len(listed) != len(set(listed)) or len(listed) != selection["count"]:
        raise ValueError("Duplicate or miscounted selected modules.")
    if set(listed) != visited:
        raise ValueError("Selected module inventory is not the exact approved import closure.")
    if set(files) != visited:
        raise ValueError("Packaged source contains stale modules outside the approved closure.")
    return {str(files[n].relative_to(project)) for n in visited}
