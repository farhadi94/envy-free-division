# Independent final whole-paper review

**Decision: PASS. No unresolved required findings.**

Reviewed manuscript: *The Query Complexity of Envy-Free Division: Cake, Chores, and Mixed Resources*, 61-page release candidate. This is a fresh review of the complete manuscript and selected actual Lean public statements. The first pass did not consult previous agents' review reports. I read `paper.tex`, all nineteen included section sources, and `references.bib`; checked the four statements against `verification/main_results.json` and their actual Lean endpoints; and inspected fresh renders of the final PDF.

This review binds the entire frozen source context. It does **not** claim a line-by-line review of all 1,391 Lean modules, a new kernel compilation, an exhaustive literature search, or independent re-verification of every imported formal proof. No Lean compiler was run. The separate isolated rebuild and specialized correspondence reviews remain separate evidence.

## Final candidate and integrity

- PDF SHA-256: `9dd32b34f67bcc8ff45ed717e42e93ac07c0b5d3486e15a7ff2ccd791de0a11c`.
- Frozen context: `review/candidate_source_snapshot.json`.
- Context SHA-256: `b9f81ea295a8f898a173ac5eeb00dd382f629fc7a13e85301202eb341999333f`.
- All paper/PDF hashes and all Lean-source hashes in the final context were checked against current files before final visual inspection and again afterward.
- The author made one clarification during the initial review: the contrast-preservation proof now explicitly defines `e_{ij}=w_i(P_j)-t_j`. The new definition was checked in source and on final PDF page 45. Comparing the initial and final frozen maps shows that only `sections/upper_proof.tex` and `paper.pdf` changed among paper inputs; the Lean map is identical. The final acceptance and unchanged-during-review assertion apply to the refreshed final candidate, whose context bytes and source hashes stayed unchanged throughout the final render/acceptance pass.

## Presentation and organization

The manuscript presents exactly four main theorems (2.1–2.4): deterministic chores, randomized exact cake/chores, the randomized nonnegative lower bound, and mixed-resource impossibility. The five comparison-table rows do not introduce a fifth result: cake and chore applications of Theorem 2.2 have separate benchmark rows. The introduction, theorem statements, overviews, appendices, and final formal-coverage table consistently describe those four results.

The main text is compact and readable. It distinguishes query complexity from output fragmentation and bit complexity; states the measurable nonanticipating oracle assumption where the randomized upper bound needs it; and keeps the lower-bound claims precise about success probability, attempted versus answered queries, freely chosen finite output endpoints, net-total normalization, and the absence of a common variation bound. Technical terminology is standard or explicitly defined. The appendix-specific notation is introduced where used. The formerly implicit payment-error notation is now explicit.

The comparison table appears on page 3. All 142 source labels are unique, all source cross-references resolve, all 19 cited bibliography keys exist, and extracted PDF text has no unresolved `??` markers. Current `paper.log`, `paper.blg`, and `build.log` contain no Warning, Overfull, Underfull, undefined-reference, or multiply-defined-label diagnostics. The PDF metadata reports 61 letter-size pages. The bibliography marks the recent cake papers as versioned preprints and does not present the announced cubic lower bound as a proved benchmark.

Fresh PDF pages visually inspected: **1, 2, 3, 4, 5, 8, 9, 10, 11, 15, 19, 23, 28, 31, 34, 38, 41, 43, 45, 49, 52, 53, 55, 57, 58, 59, 60, 61**. These cover the title/abstract, introduction, comparison table, all main statements, related work, both bibliography pages, representative proofs from every technical appendix, the corrected contrast paragraph, final complexity accounting, both lower-bound arguments, formal coverage, and AI methodology. No clipping, overlap, unreadable table, missing mathematical glyph, or broken reference marker was found. The disclosure occupies a short final page; that whitespace is harmless and does not require another source change.

## Mathematical review

### Deterministic chores

I followed the original-snapshot accounting, eligible equalizers, paid permissions, frozen ledgers, and terminal branches through the complete recursive query bound. The deferred-payment argument charges actual own-cost reductions rather than the gross cost of a removed suffix; zero-credit clipped proposals freeze unchanged; the affine terminal routine retains zero-utility whole pieces needed for extraction. The distinction prevents a false material certificate from a stripped assignment.

The capacity inequality `v(a)v(b) <= u(a+b)` follows from the displayed factorial inequality, and bucket grouping works for whichever root the SubCore routine leaves unused. Summed package weight stays constant, so the class-count pigeonhole argument supplies an operation without synchronizing full partitions. The omitted cutter makes the exhausted participant set proper, while the atom scan supplies a proper large-value mask in the atomic branch. Both terminal branches account for the entire actual residue, including previously released material.

I also checked the supporting arguments: hungry anchored existence via the finite matching/fixed-point construction; sign classes and canonical prefix states; the finite persistent-record realization for arbitrary plateau replies; the many-parent equal-value chain and recurrence; clipped versus affine offset implementation using original-measure Cuts; whole-cell multicolor rounding; and whole-piece augmentation/two-group completion. No gap was identified. The recursive ambient-recording charge is explicitly included in the final factorial bound. Appendix I appropriately distinguishes conservative formal implementation choices from sharper auxiliary paper ledgers.

### Randomized upper bound

I followed the proof from ordinary physical queries through Repair, Snapshot, prescribed Shrink, and global completion. The crucial sampling statements are separated correctly: fixed-measure interpolation is used in Snapshot, while sample-dependent compensation domains use deletion stability with arbitrary later normalizers. The maximum-determinant argument handles rank-one and zero vectors; the protected-endpoint exchangeability bound does not condition a fixed-measure theorem on the selected domain.

The whole-cell payment proof keeps owner equations exact, drops discrepancy equations only at bounded fractional support, and uses supported sorted-slot rounding plus trimming while retaining fixed real-color coordinates. The correction analysis includes inherited accepted endpoints, physically restores rejected proposals, and bounds the first exceptional endpoint by a stopped recurrence rather than multiplying by the retry count. The checked margins are strong enough for both cake credits and chore taxes. The parameter choices provide the stated supplies, constant acceptance probability, and polynomial sample/query envelopes.

Snapshot checks actual fairness in its zero-disagreement branch, and its small-disagreement argument retains the immutable original interpolation grid. Prescribed Shrink charges the finite refinement depth. Global completion saves an EF anchor, keeps temporary partitions uncommitted, transports whole old bundles, proves the frozen-agent guards before counting targets, and treats zero residue separately. The new witness comparison increases the original-observer potential. Geometric retry estimates are conditional on the complete preceding history; no independence of successful attempts is needed. I found no missing mechanism in the derivation of `O(n^12 log(2n))` expected queries and `O(n^11 log(2n))` expected Cuts.

### Nonnegative randomized lower bound

The perturbation preserves normalization and the `[1/2,3/2]` density bounds. Recording Cut prefix integrals suffices because the perturbed densities are strictly positive. The possible uncounted illegal terminal bracket is separately retained. The one-row decoding exception has probability `1/n`; using two distinct perturbed rows removes it. The strict wider-arc condition `w>1/n` yields strict envy before the limit.

The treatment of failed uniform runs is essential and is supplied: strict unfairness survives a sufficiently small perturbation, malformed outputs and nonreturns replay, and bounded convergence controls finite output endpoint lists without assuming their expected size is finite. The expected-cost inequalities and the limit as `w` decreases to `1/n` give both displayed quantitative terms. I checked the algebraic elimination of the cutoff success mass. The arbitrary probability-space tape and fixed-input averaging do not require regular conditional distributions.

### Mixed impossibility

The signed relative-comparison lemma correctly treats negative and positive rival values; positive net totals force positive own value under the relative guarantee and give the affine cake inequalities used in the hard family. The unsplit-tail obstruction works for arbitrarily divided earlier intervals: each density-pattern coefficient in the average-envy calculation is nonpositive when `n>=3`.

The frontier update fixes a queried row and all previously protected cumulative values. The strict cumulative ceiling preserves first roots at one, while earlier roots remain in the unchanged prefix. The finite-horizon argument captures a fixed positive mass fraction of tapes per batch using coordinate quantiles, preserves already captured failures, and ends after finitely many batches with one fixed finite-step input. It does not choose an input after seeing the realized execution tape. The legal-query wrapper accounts for its extra Evals, and the expected-attempt lower bound follows from the success mass beyond the horizon. Reflection correctly uses bracket value minus target and preserves the legal signed target interval. The text correctly avoids claiming a single input of infinite expected cost or hardness under a fixed variation ceiling.

## Actual Lean endpoint correspondence

| Main statement | Directly inspected public endpoint | Assessment |
| --- | --- | --- |
| Deterministic chores | `RefinedChoresMain.deterministic_chores` | Actual adaptive run from empty history, bound `n! * 2^(25*n+18)`, complete disjoint closed-unit shares, chore EF, legal queries, and inherited/Cut endpoint provenance. The `Costs` structure supplies finite nonnegative measures and null singletons. The population condition is `n>=3`, with paper direct bases for one/two agents. |
| Randomized exact upper bound | `RefinedUpperGlobalPhysical.randomized_exact_envy_free_oracle` in `RefinedUpperGlobalOraclePublic.lean` | One jointly measurable next-action function, almost-sure complete EF output, and actual sup-fuel query/Cut expectations with the paper's exponents. Hypotheses are finite measures, null singletons, a legal adaptive policy, and measurability of its answer function. A fallback element enforces nonempty population. |
| Actual-cost measurability | `single_protocol_actual_costs_aemeasurable` and `single_protocol_actual_costs_totalized_expectations` | Supplemental results concern the same actual cost functions and same oracle assumptions; the expectations are not merely finite-prefix surrogates or a nonmeasurable formal lower integral presented as a random variable. |
| Nonnegative lower bound | `MoatMain.raw` | Arbitrary probability-space tape, jointly measurable protocol, raw finite interval outputs, normalized finite-step admissible rows, both cake/chore directions and flagged/unflagged ordinary replies. `ENNReal.ofReal` adds the maximum with zero to the two stated lower terms. Cost is unconditional on the uniform profile. |
| Mixed impossibility | `MixedIntervalMain.attempted_expectations_unbounded` and `relative_attempted_expectations_unbounded` | Both constructors of `RootRule` are covered. The affine endpoint has positive alpha and epsilon below alpha; the relative endpoint has `0<alpha<=1`. Raw validity and fairness are part of success, and the cost is attempted calls. The actual density input subclass is sufficient to prove impossibility over the manuscript's broader signed nonatomic measure domain. |

Supporting model definitions were checked in `ChoresComponentPopulationProgram`, `NonnegativeRawMain`, `NonnegativeMain`, `NonnegativeInputClass`, `MixedPhysicalMain`, `MixedDensity`, `AdaptiveOracleReturnedCostSup`, and `AttemptedQueries`. In particular, the upper actual cost is the supremum over one execution's fuel bounds, the mixed attempted cost includes a terminal illegal request, and the nonnegative admissibility definition has normalization, density bounds, and a finite-step condition.

As limited primary-source spot checks, I read the archived extracted primary texts for the Mackenzie–Suzuki abstract, Ye–Bai abstract, and Barman–Verma Theorem 10, as well as the manuscript's complete bibliography. These support the principal benchmark descriptions and the signed-existence comparison. This is not a renewed exhaustive external citation audit.

## Resolution and limits

The only finding raised by this review was the missing explicit payment-error definition in the contrast-preservation proof. It is resolved in the final source and rendered PDF. There are no unresolved required mathematical, correspondence, terminology, reference, or layout findings. Acceptance is for the reviewed manuscript and the explicitly inspected formal statement/model subset in the frozen context; final release still requires the separate full-kernel and packaging gates.
