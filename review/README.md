# Review and verification records

The current main-result coverage is recorded in
[`verification/coverage.json`](../verification/coverage.json), and the compiler
and axiom-audit status in
[`verification/lean_status.json`](../verification/lean_status.json).
The four public main statements are identified in
[`verification/main_results.json`](../verification/main_results.json).

The final scoped correspondence reviews are:

| Scope | Report | Source/PDF receipt |
|---|---|---|
| Deterministic chores | [Report](final_chores_review.md) | [Receipt](final_chores_review.json) |
| Randomized upper bounds | [Report](final_upper_review.md) | [Receipt](final_upper_review.json) |
| Randomized lower bound | [Report](final_lower_review.md) | [Receipt](final_lower_review.json) |
| Mixed impossibility | [Report](final_mixed_review.md) | [Receipt](final_mixed_review.json) |
| Whole-paper correspondence and presentation | [Report](whole_candidate_final_review.md) | [Receipt](whole_candidate_final_receipt.json) |

Each receipt states its actual scope and binds that review to a frozen source
and PDF snapshot. This binding does not assert that each reviewer read every
included Lean module. The independent reviews are AI source reviews, not human
peer review; compilation and transitive axiom checking provide separate
verification evidence.

`formalization/` preserves development-stage reviews and their later
addenda. Some describe obligations that were still open at the time of that
review and were subsequently discharged. `previous_release/` preserves the
earlier supporting-lemma artifact's review history. Those historical coverage
statements do not describe the completed four-main-result formalization.

The final release records in `acceptance.json` and `final_snapshot.json` bind
the delivered artifact to these scoped reviews. The full cold-audit evidence
is retained in `final_cold_audit/` when that audit has passed. Source and PDF
hashes identify the exact revision covered by each record.
