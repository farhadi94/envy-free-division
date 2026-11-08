# Mixed-result delivery closure

Status: **ACCEPT** for Theorem 2.4 and Appendix H at the exact release snapshot below. No unresolved required finding remains in this scope. This is an independent internal AI review; it is not human peer review or a claim that the complete randomized protocol theorem is Lean-formalized.

## Release snapshot

Canonical PDF: `research/submission_focused/paper/paper.pdf`  
Pages: **66**  
SHA-256: `18391fbfee679da13264a31441dfc167cb69bfa0fa9a6d2a385b270d7d9f76c6`

| Reviewed candidate source | SHA-256 |
|---|---|
| `paper_candidate/sections/general_results.tex` | `cf6772ce8e8b944300a46ca41f754177bd4c284499aad3d708564701aa58cbfc` |
| `paper_candidate/sections/mixed_lower_proof.tex` | `7c1138114db4d71cb4ad56010a8f05834bf6adef393035225390496888ab7f43` |

The candidate files under `research/rounds/round10_pure_extremal/paper_candidate/sections/` are byte-for-byte identical to the corresponding canonical files under `research/submission_focused/paper/sections/`. The hashes above therefore pin both versions. The candidate PDF is not the release artifact; this closure pins the canonical 66-page PDF explicitly.

## Reconciliation with the frozen proof review

The canonical Appendix H has exactly the same hash as the actual-LaTeX appendix accepted in the frozen `constructive_candidate.json` review. That review covered the signed relative-approximation equivalence, arbitrary-fragmentation tail obstruction, continuous first-root replay and measurability, finite randomized tape capture, the legality-checking wrapper, query-free postprocessing after the final allowed query, the expected-query consequence, and rightmost reflection. No proof-source change intervened between that review and this canonical delivery.

The mixed subsection of `general_results.tex` was independently reread for this closure. Theorem 2.4 states the conclusion proved by Appendix H: for fixed n≥3, positive success probability and positive multiplicative factor, no uniform finite expected-query bound exists on the signed domain, already on profiles with net total one. The additive counterpart has 0≤ε<1. The always-leftmost and always-rightmost conclusions, ideal-real randomness, freely chosen finite output endpoints, and absence of a common total-variation ceiling match the proof's scope. The explanatory paragraphs correctly distinguish a uniform lower bound from failure of existence, a bound on necessary output cuts, or infinite expected cost on one fixed input. The positive-net equivalence justifies the multiplicative formulation. No claim about the other three results in `general_results.tex` is added by this scoped closure.

The canonical PDF's hash and 66-page count were checked directly after the final layout rebuild. Text extraction confirms that the revised mixed statement appears as Theorem 2.4, Appendix H contains the reviewed relative-approximation and finite-horizon statements, and the leftmost/rightmost qualifications are present in the rendered document. This is a source-and-delivery reconciliation, not a new full visual or whole-paper review.

## Formal verification boundary

The prior finite-coefficient correspondence review remains separate. Supporting Lean lemmas do not by themselves mechanize the full measurable randomized construction. The coordinator's global 34-module build and axiom audit are **outside this closure**. No global axiom-audit success or completion is asserted by this record.

No frozen review or manuscript source was modified to create this closure.
