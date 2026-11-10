#!/usr/bin/env python3
"""Translate a passed frozen release audit and actual scoped reviews into evidence.

This performs no Lean compilation and no review. It refuses pending audits,
stale sources, absent reviewer snapshot bindings, or incomplete coverage.
Use --write only after all gates close; the default validates without writing.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
from audit_closure_parallel import load_release_helpers, release_snapshot, script_snapshot

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / 'verification/lean'
ROLES = {
    'chores': 'review/final_chores_review.json',
    'upper': 'review/final_upper_review.json',
    'lower': 'review/final_lower_review.json',
    'mixed': 'review/final_mixed_review.json',
    'whole': 'review/whole_candidate_final_receipt.json',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2) + '\n').encode()


def read(name):
    return json.loads((ROOT / name).read_text())


def check_hashes(hashes, prefix=''):
    for name, expected in hashes.items():
        path = ROOT / prefix / name
        require(path.is_file() and sha(path.read_bytes()) == expected, 'Hash mismatch: ' + str(path))


def collect_lean_hashes():
    return {str(p.relative_to(PROJECT)): sha(p.read_bytes())
            for p in sorted((PROJECT / 'EnvyFreeResearch').rglob('*.lean'))}


def verify_release_bindings(report):
    """Recheck every current release input, including exact script membership."""
    require(script_snapshot(ROOT) == report["verification_script_sha256"],
            'Verification script set or contents changed')
    staging = Path(__file__).resolve().parent
    auditor_paths = [staging / name for name in
                     ('audit_closure_parallel.py', 'dag_scheduler.py', 'finalize_release_evidence.py')]
    auditor_paths += sorted((ROOT / 'scripts').glob('*.py'))
    expected_auditors = {path.relative_to(ROOT).as_posix(): sha(path.read_bytes()) for path in auditor_paths}
    require(report['auditor_sha256'] == expected_auditors, 'Auditor set or contents changed')
    helpers = load_release_helpers(ROOT)
    current = {}
    release_snapshot(helpers, current, ROOT)
    for key in ('main_results', 'main_results_sha256', 'configuration_sha256',
                'expected_dependencies', 'historical_proofs_sha256', 'module_selection_sha256',
                'verification_script_sha256', 'release_inputs_sha256', 'audit_inputs_sha256',
                'release_project_module_count', 'release_project_modules'):
        require(current[key] == report[key], 'Release snapshot differs: ' + key)
    return helpers



def validate_finalization_inputs(report, sources):
    """Read-only review/coverage preflight; makes no claim about audit status."""
    build = read('paper/build_manifest.json')
    require(build['status'] == 'build_passed_not_mathematical_acceptance' and not build['diagnostics'],
            'Paper build is not clean')
    require(build['comparison_table_page'] <= 4, 'Comparison table appears too late')
    check_hashes(build['sha256'], 'paper')
    pdf_hash = build['sha256']['paper.pdf']
    context_path = 'review/candidate_source_snapshot.json'
    context_bytes = (ROOT / context_path).read_bytes()
    context = json.loads(context_bytes)
    require(context['pdf_sha256'] == pdf_hash and context['paper_source_sha256'] == build['sha256']
            and context['lean_source_sha256'] == sources, 'Reviewer context differs from audited candidate')
    require(context['configuration_sha256'] == report['configuration_sha256'] and
            context['audit_inputs_sha256'] == report['audit_inputs_sha256'] and
            context['main_results_sha256'] == report['main_results_sha256'], 'Context verification inputs differ')
    coverage_input = ROOT / 'formalization/release_staging/coverage.release.json'
    readme_input = ROOT / 'formalization/release_staging/README.release.md'
    coverage_bytes = coverage_input.read_bytes()
    readme_bytes = readme_input.read_bytes()
    coverage = json.loads(coverage_bytes)
    require(coverage['main_theorem_count'] == 4 and coverage['main_theorems_fully_formalized'] == 4,
            'Coverage is not finalized for all four results')
    require(len(coverage['coverage']) == 4, 'Expected four coverage rows')
    require('pending' not in coverage.get('status', '').lower(), 'Coverage remains pending')
    require(coverage['main_endpoint_manifest_sha256'] == report['main_results_sha256'], 'Coverage endpoint manifest differs')
    expected_rows = {row['id']: row for row in report['main_results']}
    require({row['id'] for row in coverage['coverage']} == set(expected_rows), 'Coverage result IDs differ')
    for row in coverage['coverage']:
        expected_row = expected_rows[row['id']]
        require(row['module'] == expected_row['module'] and row['declarations'] == expected_row['declarations']
                and row['formalization_status'] == 'complete_main_statement', 'Coverage public statement mismatch')
        require(row['proof_source_sha256'], 'Missing paper proof bindings in coverage')
        check_hashes(row['proof_source_sha256'], 'paper/sections')

    accepted_reviews = []
    review_receipts = {}
    for role, receipt_path in ROLES.items():
        receipt_bytes = (ROOT / receipt_path).read_bytes()
        receipt = json.loads(receipt_bytes)
        require(receipt.get('status') == 'PASS' or receipt.get('status', '').startswith('accepted'),
                'Review status is not accepted: ' + role)
        require(receipt.get('role') == role and receipt.get('accepted') is True,
                'Review is missing explicit acceptance: ' + role)
        require(receipt.get('unresolved_required_findings') == [] and not receipt.get('required_findings')
                and not receipt.get('required_mathematical_repairs_from_this_review'), 'Open findings: ' + role)
        require(receipt.get('reviewed_snapshot') == context_path and
                receipt.get('reviewed_snapshot_sha256') == sha(context_bytes) and
                receipt.get('scoped_review_context') is True, 'Missing actual reviewer snapshot binding: ' + role)
        pdf_field = ['pdf_sha256'] if 'pdf_sha256' in receipt else ['pdf', 'sha256']
        reviewed_pdf = receipt
        for key in pdf_field:
            reviewed_pdf = reviewed_pdf[key]
        require(reviewed_pdf == pdf_hash, 'Review PDF is stale: ' + role)
        # Check current, explicitly scoped source lists; historical comparison maps
        # inside receipts are preserved as historical evidence, never retargeted.
        maps = {
            'reviewed_paper_sha256': '', 'directly_reviewed_lean_sha256': '',
            'reviewed_lean_sha256': '', 'source_hashes': '',
            'paper_source_sha256': 'paper', 'selected_lean_source_sha256': 'verification/lean',
            'mixed_local_import_closure_sha256': 'verification/lean',
            'supporting_artifact_sha256': '', 'rendered_page_sha256': '',
            'configuration_sha256': 'verification/lean',
        }
        for field, prefix in maps.items():
            if field in receipt:
                require(isinstance(receipt[field], dict), 'Malformed source map: ' + field)
                check_hashes(receipt[field], prefix)
        if 'local_dependency_source_comparison' in receipt:
            comparison = receipt['local_dependency_source_comparison']
            require(not comparison['missing'] and not comparison['mismatches'], 'Reviewed closure mismatch')
            require(comparison['module_count'] == len(comparison['source_sha256']), 'Reviewed closure count mismatch')
            check_hashes(comparison['source_sha256'], 'verification/lean')
        if 'endpoint_manifest_sha256' in receipt:
            require(receipt['endpoint_manifest_sha256'] == report['main_results_sha256'], 'Stale endpoint review')
        pinned_files = {receipt_path: sha(receipt_bytes), context_path: sha(context_bytes)}
        report_path = receipt.get('report')
        if report_path:
            require(sha((ROOT / report_path).read_bytes()) == receipt['report_sha256'], 'Review report changed')
            pinned_files[report_path] = receipt['report_sha256']
        accepted_reviews.append({
            'role': role, 'accepted': True, 'unresolved_required_findings': [],
            'receipt': receipt_path, 'receipt_pdf_field': pdf_field,
            'reviewed_pdf_sha256': pdf_hash, 'reviewed_snapshot': context_path,
            'files_sha256': pinned_files,
            'scope': 'The original receipt defines the reviewed subset and qualifications. The full snapshot binds its frozen context, not a claim to line-by-line review of every module.',
        })
        review_receipts[role] = receipt
    whole = review_receipts['whole']
    require(whole.get('visual_pages_inspected') and whole.get('source_and_pdf_unchanged_during_review') is True,
            'Missing final visual inspection')
    require(not whole.get('unresolved_reference_markers') and not whole.get('existing_tex_log_warnings'),
            'Whole-paper presentation findings remain')

    return (build, pdf_hash, context_path, context_bytes, coverage_input, readme_input, coverage_bytes, readme_bytes, accepted_reviews, whole)


def prepare(audit_dir):
    audit_dir = audit_dir.resolve()
    require(audit_dir.is_relative_to(ROOT), 'Audit directory must be inside candidate')
    audit_bytes = (audit_dir / 'report.json').read_bytes()
    report = json.loads(audit_bytes)
    require(report.get('status') == 'passed' and report.get('snapshot_passed') is True,
            'Cold audit is not passed')
    require(report.get('release_mode') is True and report.get('entry_modules') == ['EnvyFreeResearch'],
            'Expected full --release audit of EnvyFreeResearch')
    for field in ['sources_changed_during_audit', 'configuration_changed_during_audit',
                  'auditor_changed_during_audit', 'release_inputs_changed_during_audit']:
        require(field in report and not report[field], 'Audit input changed or unchecked: ' + field)
    require(set(report['allowed_axioms']) == ALLOWED, 'Wrong axiom policy')
    require(1 <= report['jobs'] <= 3 and report['lean_threads_per_job'] == 1,
            'Unexpected compiler concurrency')
    helpers = verify_release_bindings(report)
    for group, prefix in [('source_sha256', 'verification/lean'),
                          ('configuration_sha256', 'verification/lean'),
                          ('audit_inputs_sha256', 'verification/lean'),
                          ('auditor_sha256', ''), ('release_inputs_sha256', '')]:
        check_hashes(report[group], prefix)
    sources = collect_lean_hashes()
    require(sources == {k: v for k, v in report['source_sha256'].items()
                        if k != 'EnvyFreeResearch.lean'}, 'Audit source set mismatch')
    require(len(sources) == report['release_project_module_count'], 'Project count mismatch')
    module_names = {'.'.join(Path(p).with_suffix('').parts) for p in sources} | {'EnvyFreeResearch'}
    require(report['module_count'] == len(module_names), 'Closure count mismatch')
    rows = report['modules']
    require(len(rows) == len(module_names) and {r['module'] for r in rows} == module_names
            and all(r['exit_code'] == 0 and not r.get('cancelled') for r in rows),
            'Missing or failed module compilation')
    require(report['main_results'] == read('verification/main_results.json')['results'],
            'Main endpoints differ')
    selection = read('verification/module_selection.json')
    selected = helpers['check_selection'](PROJECT, selection, read('verification/main_results.json'))
    require(selected == set(sources), 'Selection differs from the audited exact closure')
    axiom_bytes = (audit_dir / 'axioms.log').read_bytes()
    marker = f"AXIOM AUDIT PASSED: {report['theorem_declaration_count']} theorem declarations"
    require(marker in axiom_bytes.decode(), 'Missing actual axiom success marker')
    require(report['theorem_declaration_count'] > 0, 'Vacuous axiom audit')
    guard = helpers["lean_code_only"]
    authored = 0
    for name in sources:
        code = guard((PROJECT / name).read_text())
        require(not re.search(r"(?<![\w'])\b(sorry|admit|axiom)\b(?![\w'])", code),
                'Forbidden source token: ' + name)
        authored += len(re.findall(r'\b(?:theorem|lemma)\b', code))

    (build, pdf_hash, context_path, context_bytes, coverage_input, readme_input, coverage_bytes, readme_bytes, accepted_reviews, whole) = validate_finalization_inputs(report, sources)

    now = datetime.now(timezone.utc).isoformat()
    cold_prefix = 'review/final_cold_audit/'
    evidence = {cold_prefix + 'report.json': audit_bytes, cold_prefix + 'axioms.log': axiom_bytes}
    for path in report['auditor_sha256']:
        target = cold_prefix + Path(path).name
        content = (ROOT / path).read_bytes()
        require(target not in evidence or evidence[target] == content, 'Audit evidence filename collision')
        evidence[target] = content
    evidence[cold_prefix + Path(__file__).name] = Path(__file__).read_bytes()
    evidence_hashes = {name: sha(data) for name, data in evidence.items()}
    lean = {
        'status': 'passed', 'started_at_utc': report['started_utc'],
        'finished_at_utc': report['finished_utc'], 'evidence_translated_at_utc': now,
        'lean_version_expected': '4.35.0', 'lean_version_actual': report['lean_version'],
        'mathlib_tag': 'v4.35.0', 'allowed_axioms': sorted(ALLOWED),
        'scope': 'Every packaged project module and all four public main endpoints; cold isolated closure rebuild plus exact hardened verifier axiom audit. External pinned package oleans reused.',
        'module_count': len(sources), 'source_sha256': sources,
        'authored_theorem_declaration_count': authored,
        'theorem_declaration_count': report['theorem_declaration_count'],
        'main_results': report['main_results'], 'main_results_sha256': report['main_results_sha256'],
        'configuration_sha256': report['configuration_sha256'],
        'audit_inputs_sha256': report['audit_inputs_sha256'],
        'historical_proofs_sha256': report['historical_proofs_sha256'],
        'module_selection_sha256': report['module_selection_sha256'],
        'verification_script_sha256': report['verification_script_sha256'],
        'verification_method': 'Translation of actual passed --release cold audit; no redundant second build and no inferred mathematical review.',
        'evidence_sha256': evidence_hashes,
        'release_input_sha256': report['release_inputs_sha256'],
        'cold_audit_module_count_including_umbrella': report['module_count'],
        'finalization_draft_sha256': {'coverage.release.json': sha(coverage_bytes), 'README.release.md': sha(readme_bytes)},
    }
    snapshot = {
        'schema': 1, 'created_utc': now, 'pdf_sha256': pdf_hash,
        'paper_source_sha256': build['sha256'], 'lean_source_sha256': sources,
        'coverage_sha256': sha(coverage_bytes), 'review_context': context_path,
        'review_context_sha256': sha(context_bytes), 'cold_audit_report_sha256': sha(audit_bytes),
    }
    snapshot_bytes = encode(snapshot)
    acceptance = {
        'status': 'all_five_reviews_closed_no_required_repairs', 'created_utc': now,
        'pdf_sha256': pdf_hash, 'final_snapshot_sha256': sha(snapshot_bytes),
        'reviews': accepted_reviews,
        'unchanged_proof_and_statement_sha256': {
            name: digest for name, digest in build['sha256'].items()
            if name.startswith('sections/') and
            ('proof' in name or name in {'sections/model.tex', 'sections/general_results.tex'})},
        'cold_audit_evidence_sha256': evidence_hashes,
        'scope': 'Five actual scoped independent AI review receipts and one full cold Lean audit. Neither human referee approval nor a claim that every reviewer read all modules.',
    }
    visual = {
        'status': 'passed', 'pdf_sha256': pdf_hash, 'pages': build['pages'],
        'pages_inspected': whole['visual_pages_inspected'],
        'source_receipt': ROLES['whole'], 'source_receipt_sha256': sha((ROOT / ROLES['whole']).read_bytes()),
        'scope': 'Translation of the actual whole-paper reviewer visual inspection on the listed pages; no additional visual inspection performed by this script.',
    }
    log = ('Evidence translated from ' + cold_prefix + 'report.json\n'
           + 'Original --release cold rebuild; each project module compiled with Lean -j1.\n'
           + ''.join(f"PASS {row['module']} (exit {row['exit_code']})\n" for row in rows)
           + '\nOriginal axiom-audit output follows:\n').encode() + axiom_bytes
    outputs = {**evidence, 'verification/coverage.json': coverage_bytes, 'README.md': readme_bytes,
               'verification/lean_status.json': encode(lean),
               'verification/lean.log': log, 'review/final_snapshot.json': snapshot_bytes,
               'review/acceptance.json': encode(acceptance), 'review/visual_check.json': encode(visual)}
    # Recheck all audited inputs and review bytes immediately before any mutation.
    verify_release_bindings(report)
    for group, prefix in [('source_sha256', 'verification/lean'), ('configuration_sha256', 'verification/lean'),
                          ('audit_inputs_sha256', 'verification/lean'), ('auditor_sha256', ''),
                          ('release_inputs_sha256', '')]:
        check_hashes(report[group], prefix)
    check_hashes(build['sha256'], 'paper')
    require(collect_lean_hashes() == sources, 'Source set changed during finalization')
    require((audit_dir / 'report.json').read_bytes() == audit_bytes and
            (audit_dir / 'axioms.log').read_bytes() == axiom_bytes, 'Audit evidence changed')
    require(coverage_input.read_bytes() == coverage_bytes and readme_input.read_bytes() == readme_bytes and
            (ROOT / context_path).read_bytes() == context_bytes, 'Coverage/context changed')
    for row in accepted_reviews:
        check_hashes(row['files_sha256'])
    return outputs, {'lean_modules': len(sources), 'authored_theorems': authored,
                     'all_theorems': report['theorem_declaration_count'], 'reviews': 5,
                     'pdf_sha256': pdf_hash}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit-dir', type=Path, default=ROOT / 'formalization/logs/refined_release_all')
    parser.add_argument('--write', action='store_true', help='Write derived evidence only after every gate passes')
    args = parser.parse_args()
    outputs, details = prepare(args.audit_dir)
    if args.write:
        for name, content in outputs.items():
            path = ROOT / name
            path.parent.mkdir(parents=True, exist_ok=True)
            temporary = path.with_name(path.name + '.finalizing')
            temporary.write_bytes(content)
            temporary.replace(path)
    print(json.dumps({'status': 'evidence_written' if args.write else 'all_gates_validated_no_files_written',
                      **details, 'output_files': sorted(outputs)}, indent=2))


if __name__ == '__main__':
    main()
