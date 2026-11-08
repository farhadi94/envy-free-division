#!/usr/bin/env python3
"""Pin the independently reviewed final candidate and this review's evidence."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import unicodedata

checks = Path(__file__).resolve().parent
out = checks.parent
focus = out.parent
root = focus.parent.parent
initial = json.loads((checks / 'source_hashes_initial.json').read_text())
previous = json.loads((checks / 'pre_editorial_mixed_receipt.json').read_text())
snapshot = json.loads((out / 'final_snapshot.json').read_text())

def pin(p):
    b = p.read_bytes()
    d = {'path': str(p.relative_to(root)), 'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b)}
    if p.suffix not in ['.pdf', '.png', '.olean', '.ilean']:
        d['lines'] = len(b.decode().splitlines())
    return d

paths = [root / x['path'] for x in initial['sources']]
paths += [focus / 'paper/references.bib',
          focus / 'verification/lean/EnvyFreeResearch/SubmissionMonteCarlo.lean',
          focus / 'verification/lean/lean-toolchain',
          focus / 'verification/lean/lakefile.lean',
          focus / 'verification/lean/lake-manifest.json']
sources = [pin(p) for p in paths]
pdf = next(x for x in sources if x['path'].endswith('/paper.pdf'))
assert pdf['sha256'] == '8370c1da9ee87aedfeec7bfd0472bb63420acbb84f38427a2243baaaeb128a90'
assert snapshot['pdf_sha256'] == pdf['sha256']
previous_pins = {p['path']: p['sha256'] for p in previous['source_pins']}
changed_sources = [{'path': p['path'], 'before': previous_pins[p['path']], 'after': p['sha256']}
                   for p in sources if p['path'] in previous_pins and p['sha256'] != previous_pins[p['path']]]
allowed_changes = {'paper.pdf', 'paper.tex', 'general_results.tex', 'introduction.tex', 'related_work.tex', 'proof_overviews.tex'}
assert all(Path(p['path']).name in allowed_changes for p in changed_sources)
for p in sources:
    path = root / p['path']
    if path.is_relative_to(focus / 'paper'):
        assert snapshot['paper_source_sha256'][str(path.relative_to(focus / 'paper'))] == p['sha256']
    if path.is_relative_to(focus / 'verification/lean/EnvyFreeResearch'):
        assert snapshot['lean_source_sha256'][str(path.relative_to(focus / 'verification/lean'))] == p['sha256']

def appendix(text):
    start = text.index('H     Bounded-error lower bounds for mixed resources')
    end = text.index('I     Formal veriﬁcation artifact', start)
    return text[start:end]

def mixed_main(text):
    start = text.index('2.4   Mixed cake and chores')
    end = text.index('3     Proof', start)
    return text[start:end]

previous_text = (checks / 'paper_layout_final.txt').read_text()
current_text = (checks / 'paper_layout_editorial.txt').read_text()
assert appendix(previous_text) == appendix(current_text)
def normalized_main(text):
    text = unicodedata.normalize('NFKC', mixed_main(text))
    text = re.sub(r'(?m)^\s*\d+\s*$', '', text)
    return ' '.join(text.split())

old_output_wording = 'Ideal-real randomness and arbitrary free finite output endpoints are allowed.'
new_output_wording = 'Ideal-real randomness is allowed, and output cut locations may be chosen without queries, with no bound on their number.'
assert old_output_wording in normalized_main(previous_text)
assert normalized_main(previous_text).replace(old_output_wording, new_output_wording) == normalized_main(current_text)
finite = json.loads((checks / 'finite_lean_check.json').read_text())
assert finite['status'] == 'passed'
probes = json.loads((checks / 'independent_checks.json').read_text())
assert probes['status'] == 'passed'
match = re.search(r'AUDIT PASSED: (\d+) theorem', (checks / 'finite_axiom_audit.log').read_text())
assert match

components = [
    ('signed_relative_definition', 'general_results.tex:57-77; mixed_lower_proof.tex:11-38', 'All signs and zero; exact EF; chore reduction; positive-total global equivalence and own-value bound.'),
    ('main_theorem_quantifiers', 'general_results.tex:78-100; mixed_lower_proof.tex:101-119,713-end', 'Pair chosen before realized tape; unbounded supremum rather than one infinite-cost input.'),
    ('signed_oracle_model', 'model.tex; mixed_lower_proof.tex:40-99', 'Bracketed legality, fixed Borel arbitrary roots, attempted calls, nonreturn, finite canonical outputs.'),
    ('borel_selector_patch', 'mixed_lower_proof.tex:124-152', 'Borel least root and retained old roots on new-legal replay queries.'),
    ('separated_coverage', 'mixed_lower_proof.tex:154-185', 'Atomic/singular coordinate laws; atomless variation; finite separated compact intervals.'),
    ('coarse_insertion', 'mixed_lower_proof.tex:187-272', 'Margin alpha; two nondistinguished rows; weighted forcing; cumulative/restriction distinction; physical supports.'),
    ('legal_query_protection', 'mixed_lower_proof.tex:274-345', 'Adaptive groups; fresh root law; original-measure losses; endpoint exemption; early return and nonreturn.'),
    ('output_coverage', 'mixed_lower_proof.tex:347-409', 'Finite-return quantile; choice order; new variation budget; retained histories; fixed anchors.'),
    ('ownership_discrepancy', 'mixed_lower_proof.tex:411-477', 'Variation-weighted disagreement; K new intervals; indicator bound; gamma>0; V<c case.'),
    ('sampling_and_replay', 'mixed_lower_proof.tex:479-543', 'Independent variation samples; miss bound; 3h occupancy; L/V cancellation; fixed corridors.'),
    ('physical_pulses_and_purity', 'mixed_lower_proof.tex:545-601', 'Measurable positive supports; deterministic width via product dominated convergence; finite variation and net totals.'),
    ('no_repair', 'mixed_lower_proof.tex:603-639', 'Weighted mass surplus; largest split pair; common-row perturbations; overlap; preservation of prior failure.'),
    ('fixed_input_averaging', 'mixed_lower_proof.tex:641-710', 'Explicit measurable majorant; no abstract-input joint measurability; Tonelli fixes profile and selector.'),
    ('expected_query_transfer', 'mixed_lower_proof.tex:712-end', '2q legalizing wrapper; hidden Evals and fixed selectors; exact truncation event; unconditional expectation.'),
    ('overview_and_figure', 'mixed_overview.tex; figures/mixed_pulses.tex; PDF pages 7-8', 'Full sources and final rendered figure; correct (1+alpha)M; no-repair qualification fixed.'),
    ('finite_lean_scope', 'MixedApproximation.lean; R6MixedMonteCarlo.lean; formal_scope.tex', 'Complete source audit; fresh compilation; axiom audit; finite/continuous scope distinction.'),
]

artifacts = [out / 'mixed_independent.md', checks / 'independent_checks.py',
             checks / 'independent_checks.json', checks / 'audit_finite.lean',
             checks / 'finite_lean_check.json', checks / 'finite_axiom_audit.log',
             checks / 'SubmissionMonteCarlo_fresh_lean.log', checks / 'R6MixedMonteCarlo_fresh_lean.log',
             checks / 'MixedApproximation_fresh_lean.log', checks / 'paper_layout_editorial.txt',
             checks / 'page7_editorial.png', checks / 'pre_editorial_mixed_receipt.json',
             checks / 'pre_editorial_mixed_review.md', Path(__file__)]

receipt = {
    'schema_version': 1,
    'reviewer': '/root/focused_review_mixed',
    'completed_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verdict': 'no_blocking_mathematical_gap_found',
    'blocking_findings': [],
    'unresolved_findings': [],
    'fresh_independent_review': True,
    'prior_author_notes_or_review_conclusions_used': False,
    'further_agents_spawned': False,
    'manuscript_edited_by_this_reviewer': False,
    'full_continuous_theorem_machine_certified': False,
    'scope': {
        'main_theorem': 'thm:mixed-mc / Theorem 2.4',
        'appendix': 'Appendix H / mixed_lower_proof.tex complete',
        'parameters': 'n >= 3; 0 < p <= 1; 0 <= epsilon < alpha <= 1',
        'hard_subclass': 'Finite piecewise-constant signed profiles, net totals one, no common variation ceiling.',
        'model': 'Signed bracketed Eval/Cut, fixed Borel arbitrary-root selectors, input-independent measurable ideal-real tapes, arbitrary free finite output endpoints.',
        'expected_cost': 'Unconditional attempted-call count; supremum over fixed profile/selector pairs.',
    },
    'source_pins': sources,
    'initial_source_manifest': str((checks / 'source_hashes_initial.json').relative_to(root)),
    'final_pdf': {
        'sha256': pdf['sha256'], 'pages': 67, 'main_statement_pages': [5],
        'overview_and_figure_pages': [7, 8], 'appendix_h_pages': list(range(57, 67)),
        'inspection': 'Complete original Appendix H and main mixed statement; final editorial PDF reinspection and visual pulse figure. Appendix H text is identical to the preceding audited checkpoint; main mixed statement differs only by layout and the reviewed output-endpoint paraphrase.',
    },
    'editorial_reconciliation': {
        'status': 'closed_no_new_findings',
        'previous_pdf_sha256': previous['final_pdf']['sha256'],
        'final_pdf_sha256': pdf['sha256'],
        'changed_previously_reviewed_sources': changed_sources,
        'mixed_model_appendix_overview_body_figure_and_lean_source_hashes_unchanged': True,
        'mixed_fairness_definition_parameters_and_oracle_model_unchanged': True,
        'output_endpoint_paraphrase_equivalent_under_unchanged_finite_union_model': True,
        'appendix_h_pdf_text_identical': True,
        'mixed_main_pdf_text_identical_after_documented_endpoint_paraphrase_and_layout_normalization': True,
        'prose_reinspected': ['paper.tex abstract', 'general_results.tex mixed statement', 'introduction.tex', 'proof_overviews.tex', 'mixed-facing related_work.tex', 'PDF pages 5,7-8'],
        'fresh_audit_results_retained': True,
        'new_mathematical_tests_or_lean_compilation_run': False,
        'new_findings': [],
        'coordination_snapshot_pins': [pin(out / name) for name in
                                      ['final_snapshot.json', 'editorial_delta.json', 'pre_editorial_snapshot.json']],
    },
    'coverage': [{'component': c, 'source_location': l, 'status': 'verified', 'details': d}
                 for c, l, d in components],
    'checks': {
        'rational_and_budget_probes': probes,
        'fresh_lean_compilation': finite,
        'finite_axiom_audit': {
            'status': 'passed', 'namespace_theorem_declarations': int(match.group(1)),
            'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
            'continuous_scope_excluded': True,
        },
    },
    'resolved_findings': [
        {'id': 'MIXED-EDITORIAL-01', 'severity': 'nonblocking',
         'source': 'paper/sections/mixed_overview.tex',
         'issue': 'Unqualified no-repair wording broader than pure-support lemma.',
         'resolution': 'Statement conditioned on preserved query history and single-owner supports.',
         'final_tex_and_pdf_rechecked': True},
        {'id': 'MIXED-EDITORIAL-02', 'severity': 'nonblocking',
         'source': 'paper/sections/mixed_lower_proof.tex',
         'issue': 'Coordinate-law wording omitted that cake endpoints need no cover.',
         'resolution': 'Pushforwards restricted to U=(0,1) minus protected intervals; 0,1 explicitly exempt.',
         'final_tex_and_pdf_rechecked': True},
    ],
    'external_primary_sources': [{
        'url': 'https://drops.dagstuhl.de/storage/00lipics/lipics-vol261-icalp2023/LIPIcs.ICALP.2023.16/LIPIcs.ICALP.2023.16.pdf',
        'title': 'Barman and Kulkarni, Approximation Algorithms for Envy-Free Cake Division with Connected Pieces (ICALP 2023)',
        'pages_reviewed': ['16:2'],
        'purpose': 'Verify cited nonnegative multiplicative convention; no use as proof of signed lower bound.',
    }],
    'limitations': [
        'Independent mathematical review is not formal certification of the continuous theorem.',
        'Finite probes are error detectors, not exhaustive checks of arbitrary profiles, protocols, or tape laws.',
        'Fresh project sources compiled against installed Lean 4.35.0/mathlib artifacts; library sources were not independently rebuilt.',
        'No verdict on other main theorems or full literature novelty.',
    ],
    'review_artifact_pins': [pin(p) for p in artifacts],
}
(out / 'mixed_independent_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({
    'review': str((out / 'mixed_independent.md').relative_to(root)),
    'receipt': str((out / 'mixed_independent_receipt.json').relative_to(root)),
    'verdict': receipt['verdict'], 'pdf_sha256': pdf['sha256'],
    'coverage_components': len(components), 'lean_theorem_declarations': int(match.group(1)),
}, indent=2))
