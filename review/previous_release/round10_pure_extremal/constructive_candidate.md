# Independent review of the replacement mixed lower-bound appendix

Status: **ACCEPT**. No unresolved required mathematical finding.

Reviewed source: `paper_candidate/sections/mixed_lower_proof.tex`  
SHA-256: `7c1138114db4d71cb4ad56010a8f05834bf6adef393035225390496888ab7f43`

This is an independent internal AI review of the actual replacement LaTeX, separate from the earlier review of the research note. It is not a claim of human peer review or full mechanization.

## What was checked

* The positive-net relative-approximation equivalence, including zero and opposite-sign endpoints, is correct. Positive total forces a positive own bundle value under either equivalent guarantee. Summing the comparisons over the other n−1 bundles gives the displayed proportional-share consequence.
* The cone coefficient in the unsplit-final-interval lemma is correct for all locations of the unique positive density. Its use of a third agent is explicit. The proof handles arbitrary measurable fragmentation of resolved cells because constant densities convert allocations into length fractions.
* Both frontier updates preserve every stated density invariant, all normalized totals, and the strict cumulative barrier below level one. Their finite nature is explicit.
* The first-root replay lemma handles prefix roots, endpoint-one roots, negative targets, zero targets and degenerate brackets. The separate Borel measurability proof is correct: minima over a compact interval depend continuously on the interval endpoints and target; rational-level unions detect a strict upper bound on the least root.
* The finite-horizon theorem works for pointwise-legal partial strategies and preserves real internal computation on an identical tape/transcript. Analytical missing-call descriptors do not invoke an executable divergence test. After h stages every real call is protected because the strategy has at most h calls on every profile and tape.
* Each row restriction and coordinate quantile has the claimed mass loss. A random unbounded but finite output size does not break the final quantile. Subsequent updates preserve both previously captured executions and their output bundle values. Consequently the geometric batch capture bound yields one fixed finite-piece profile, with no adaptive choice after the final execution tape and no infinite limiting profile.
* The final wrapper checks syntax and bracket legality using hidden Eval calls, preserves successful original transcripts, allows all computation after the qth original query, and uses at most 2q calls. Thus its correct-return event is precisely the original success event intersected with Q≤q. The expectation inequality follows on the same fixed input.
* Reflection preserves signed legality via target B−t and reverses first/last roots with at most one extra Eval per Cut. The rightmost conclusion follows.
* The zero-query construction for ε≥α, the distinction between uniform and pointwise finiteness, and the lack of a common variation bound are all accurate.

## Presentation boundaries

The proof is now self-contained at the level of the stated measurable oracle-protocol model. Its invocation of fixed-profile call/output measurability is explicit, and fixed-profile least-root measurability is proved rather than presumed. The finite cone and continuous replay lemmas may be backed by supporting Lean modules, but the full randomized batch construction remains a written argument unless separately mechanized. Existing artifact coverage text should reflect that distinction when the appendix is integrated.

No source change is required by this review.
