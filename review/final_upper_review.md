# Final randomized upper: candidate correspondence review

**Accepted for the randomized-upper theorem's source/PDF correspondence and scoped presentation. No blocker identified. This is not cold-audit certification or release acceptance.**

Reviewer: `/root/randomized_main_fresh_review`. Candidate: `/Users/alireza/temp/ef/research/formalization/final_release_candidate`. The inspected PDF has 66 pages and SHA-256 `5b24cbca4d65952a80ee85608842807a1e0104c26db7c4be99fc0fe25cde60a5`. No proof/configuration edits, Lean builds, paper builds, or publication actions were performed. Only this report and its new JSON receipt were written into the candidate.

## Source continuity and scope

I reused my independent detailed proof review and strict-protocol addendum only after checking exact source identities. All 61 Lean files in the original review manifest and all 16 included proof files in the strict addendum manifest match the candidate byte for byte. Four earlier scoped `*Audit.lean` print harnesses are not included; these are audit drivers, not missing theorem dependencies. Independently traversing local imports of `UpperGlobalOraclePublic` and `UpperGlobalOracleCostMeasurable` finds 680 candidate source files, all present and byte-identical to the reviewed `all_main_results` workspace. The three Lean configuration/pin files also match. This is a source-continuity check, not a claim that I individually re-reviewed all 680 modules or rebuilt them. The receipt records all closure hashes.

The candidate `model.tex` and entire `upper_proof.tex` match my original manuscript snapshot. The revised `general_results.tex` clarifies that an oracle policy is a measurable function of the answered query transcript and current query. I read that clarification and the final formal-scope paragraph directly. Every current paper-source hash matches the whole-candidate final receipt. The candidate manifest now names the strict `UpperGlobalOraclePublic.randomized_exact_envy_free_oracle` endpoint, with its actual-cost measurability companion and supporting module, rather than relying only on the earlier phase-process theorem.

## Theorem/model correspondence

Theorem 2.2 and Appendix F state complete exact EF for finite nonnegative nonatomic cake/chore measures with unconditional expected query/Cut orders `O(n^21 log²(2n))` and `O(n^20 log²(2n))`, uniformly over legal measurable ordinary adaptive policies and including rejected work. The reviewed strict public theorem supplies these claims under the same intended model:

- `OracleNext.next` is one input/profile-independent, jointly Borel tape/transcript ordinary-query next-action function. It returns a completed coded physical state or asks an ordinary query; the measurable interval-code output map provides the finite allocation. Its countable search skips internal live-phase returns and is well defined even on inconsistent histories, as permitted by the paper's query-free nonreturn convention.
- The actual `AdaptiveOracle.run` with the full-history Option oracle is linked to the concrete finite phase prefixes, using proved stability of observable prefix actions. No correspondence or successful-producer premise is supplied to the final theorem. The actual run reaches a finite `.returned (.done a)` almost surely on the original infinite stream.
- The returned finite interval lists decode to a literal pairwise-disjoint partition of `[0,1]`, with exact cake/chore EF. Endpoint ownership, null pieces, zero rows and frozen observers are accounted for by the previously reviewed physical proofs.
- Costs are the actual ordinary run's `queryCost` and Cut-marked cost, each the supremum over all fuel bounds of answered counts. They equal the returned trace counts on returning tapes and include all rejected internal work and `2n` initialization Evals. Almost-sure legal return makes answered/all-call expectation correspondence legitimate; it does not discard positive-measure illegal or unsuccessful work.
- `single_protocol_actual_costs_aemeasurable` proves actual costs AE measurable under the unchanged answer-only Borel policy hypothesis. The totalized proxy reproduces actual returning traces without assuming that proxy globally legal. The expectation-equality companion therefore identifies ordinary unchanged-law expectations, not successful-run conditional expectations.

The constants are explicit: `100*A*n^21*log₂(2n)^2` queries and `49*A*n^20*log₂(2n)^2` Cuts, `A=(2^42)^18*45^2`. `fallback : Fin n` expresses a nonempty population. The formal finite null-singleton measures on ℝ cover the manuscript's unit-interval measures by the usual zero extension. The independent finite-label/permutation and continuous random-coordinate encodings are standard ideal-uniform sampling; no additional universal uniform-stream recoding theorem is being claimed here. The public assumption on the total real answer function is no stronger than a measurable Option-valued policy, and the transcript clarification removes the earlier ambiguity about access to unexposed private randomness.

## Conservative accounting is correctly qualified

The formal pre-envelope ledger charges at most `N+1` normalizations, where `N=n(n-1)`. Its bounds are `96*n^2*(n-1)*m + (n+1)*(N+1) + 2n` queries and `48*N*m + (N+1)` Cuts. These yield the advertised main polynomial orders but do not themselves certify Appendix F's sharper `O(n)`/`O(1)` additive overhead, conditional fewer-than-eight trials per iteration, optional tail wrapper, or accepted-endpoint storage refinement.

The final formal-scope appendix explicitly says the formal protocol charges each normalization separately, preserves the main bounds, and does not claim every sharper auxiliary ledger verbatim. This is the necessary accurate qualification. The paper's sharper auxiliary account refers to initial totals and a terminal two-agent base; the conservative formal bound is not a contradiction of that paper argument. No weakened main theorem or mathematical repair is required by this comparison.

## PDF and release boundary

I freshly extracted text from the hashed current PDF, independently confirmed 66 pages with `pdfinfo`, and freshly rendered and visually inspected pages 4 and 66. Page 4 displays Theorem 2.2, both powers/squared logarithms, and the transcript-policy clarification clearly. Page 66 displays the randomized formal-coverage row and conservative-normalization qualification without clipping. Fresh text inspection also checked the completion/cost passages on pages 53 and 56 and the model text on page 3 against the source. The whole-paper layout and the other three mathematical roles remain outside this scoped approval.

The final candidate's all-included-source cold Lean/axiom audit and the release acceptance gate remain separate and pending for this receipt. Neither an old scoped audit nor matching source/PDF hashes is treated as evidence that that final audit has passed. Once root's audit finishes, release metadata must record its actual outcome. No unresolved required upper-correspondence finding remains in the present snapshot.

## Frozen review-context binding

The receipt is bound to `review/candidate_source_snapshot.json`, SHA-256 `43e15783371fa35ef8cec39ab6358d5201f9eb167574f44675c9df5454c3deee`. I checked the snapshot identity and all listed current file hashes (PDF, paper, 1,188 Lean files, configurations, audit inputs, and main-result manifest), finding no mismatch. This binds the scoped upper review to the same full frozen context; it does **not** claim semantic review of all 1,188 sources or certify the separately running cold audit.
