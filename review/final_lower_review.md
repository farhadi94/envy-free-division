# Final scoped lower-bound review

**Status: PASS. Accepted: true. No unresolved required findings.**

Reviewer: independent lower-bound reviewer (`lower_final_scope_review`). This is an actual final scoped refresh following my independent mathematical and formal-correspondence review, copied without modification to `review/lower_previous_scope_review.md` (SHA-256 `79f135af1ac89ab9b62cd6194f89ad741888f35192ae5d00e0bef30e2e3c933d`). It is not a whole-paper mathematical review and not a new Lean compilation certificate.

## Exact candidate binding

- Reviewed context: `review/candidate_source_snapshot.json`.
- Context SHA-256: `6feec15ff3c71a532b7f63c0e006419822c3dbe015da3fcfe078476011e42657`.
- PDF: `paper/paper.pdf`, 61 pages.
- PDF SHA-256: `2710485b12dd9caab97bf9af45ed1bc4fc969e3202e9ae20a2779a594594e8c5`.
- Public endpoint: `EnvyFreeResearch.Full.MoatMain.raw`.
- Result: unconditional expected answered-query cost on the uniform profile at least `max{0,n(np-1)/2,n^2 p/4-1}`.

The full snapshot identifies the frozen review context. The subset maps in `final_lower_review.json` identify the actual reviewed scope; this receipt does not imply line-by-line review of every source in the full release.

## Work performed on this final candidate

I parsed the 91-module local import manifest recorded in my earlier review, recursively computed the candidate import closure from `MoatMain.lean`, and compared every candidate source hash and the exact closure membership. All 91 files match; there are no missing files, changed hashes, or added/removed dependencies. I also checked each hash against the current snapshot's Lean map. Thus the inspected physical moat construction, adaptive replay, decoder, retained-failure ledger, probability limits, arbitrary-tape quantifiers, and raw finite-output adapter have no intervening source changes.

The candidate lower proof, lower overview, and model are byte-identical to the sources bound by the earlier review. I reread the current model and main lower theorem and read the final table, introductory lower claim, artifact scope, and endpoint manifest. The shared `general_results.tex` has changed because the randomized upper bounds now read `O(n^12 log(2n))` and `O(n^11 log(2n))`; the lower theorem and its explanatory paragraph still state the result previously reviewed. The current lower endpoint manifest correctly selects `MoatMain.raw` and states its fixed-input success and unconditional answered-cost scope.

The reread confirms that success must be at least `p` on every normalized finite-step profile in the specified density window, while cost is charged on the uniform profile. Illegal requests and nonreturn remain failures. Randomness remains an input-independent arbitrary probability-space tape with a jointly measurable next-action rule. Returned allocations have a finite number of arbitrary real endpoints per return, without a uniform or expected fragmentation bound. The result is stated for cake and chores and already holds for answered calls, so it also bounds the paper's total-call convention. The table omits the trivial zero term but states a valid weaker display and points to the exact Theorem 2.3.

## Final PDF inspection

I extracted text from the actual final PDF and rendered and visually inspected PDF pages **3, 4, 7, 53, 54, 55, and 60**. These are also the printed page numbers.

- Page 3: comparison-table lower row and complete protocol/model definitions.
- Page 4: Theorem 2.3, both quantitative terms, the zero term, answered-query qualification, and resolved Appendix G reference.
- Page 7: the lower proof overview, including one-row and two-row detection and retaining failed returns.
- Pages 53–55: the complete lower appendix G, Theorem G.1, illegal-request correction, physical perturbation, strict decoder, failure retention, deterministic width selection, and final expectation/limit equations.
- Page 60: artifact scope and the lower-bound verified-statement row.

The bound and assumptions in the rendered theorem agree with the reviewed source and public Lean statement. The appendix renders both orientation arguments and the probability accounting correctly. The success-probability elimination has the correct nonnegative difference `(n-2)(1-s)+2(nw-1)s`; both final lower-bound terms are present. Absolute-value delimiters, indicators, fractions, and inequality signs are visible. I found no missing formulas, clipping, overlap, unresolved references, or scope-changing typesetting defects on these pages. Temporary PNGs remain under `/tmp`; only inspected page numbers are recorded because the images are not packaged evidence.

## Acceptance and limitations

The mathematical and formal-scope conclusions of the independent review remain valid for this exact packaged lower result. In particular, the one extra possible uncounted illegal request is charged against failed capped executions, the width is fixed before drawing a tape/input, and no termination or finite expected-output-size assumption has appeared. The earlier report's note about disjoint half-open interval record encoding and nonatomic endpoint reassignment is an encoding explanation, not an open finding.

No mathematical repair is required in this scope. This review accepts the lower result on the bound snapshot and PDF. It does not certify the separate upper-bound revisions or the cold compilation currently owned by the root agent. No Lean compiler, paper compiler, source/script modification, commit, or push was performed. The only packaged writes were this report, its receipt, and the unchanged historical review copy. All scoped source and PDF hashes were rechecked before writing the receipt.

## Refresh after the Snapshot overview clarification

I compared `review/candidate_source_snapshot.before_snapshot_clarification.json` with the current snapshot rather than simply retargeting the acceptance. Their only paper-file differences are `sections/upper_overview.tex` and the rebuilt `paper.pdf`; the entire Lean map, endpoint manifest, configuration, audit inputs, and all lower-scope sources are unchanged. The new sentence distinguishes immediate completion from the positive-margin branch in the upper overview, outside this mathematical scope.

I rechecked the actual bytes of all 91 bound lower Lean modules and every bound lower paper source. I extracted the current PDF text and rerendered and visually inspected pages 3, 4, 7, 53, 54, 55, and 60. The PDF remains 61 pages. Text differences are confined to pages 6–8, reflecting overview reflow. On page 7 the unchanged complete lower overview now begins slightly lower; its final paragraph remains on that page and all lower text and formulas remain legible and unclipped. The theorem, model/table, Appendix G, and formal-scope pages retain their content and page numbers. There are no new findings and acceptance remains PASS for the current exact snapshot and PDF listed above.

The previous snapshot remains packaged under `review/candidate_source_snapshot.before_snapshot_clarification.json` with SHA-256 `b9f81ea295a8f898a173ac5eeb00dd382f629fc7a13e85301202eb341999333f`. This refresh performed no Lean or paper compilation and no source/script edits.
