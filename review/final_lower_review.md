# Final lower-bound release review

**Accepted for lower-bound statement/source correspondence.** No required mathematical or model finding was identified. This is a role-specific review of the current candidate, not certification of its pending full cold audit, the other three results, or human approval for publication.

Reviewer: `/root/lower_release_review`. Recorded at 2026-11-08T03:10:45.263457+00:00. Candidate: `/Users/alireza/temp/ef/research/formalization/final_release_candidate`. The current 66-page `paper/paper.pdf` has SHA-256 `5b24cbca4d65952a80ee85608842807a1e0104c26db7c4be99fc0fe25cde60a5`. Its complete build-manifest hash map matches current files; extracted text on pages 57 and 66 agrees with the quantitative theorem and the new formal-scope/AI sections. This was not a visual layout review.

## Exact theorem and model

I independently read Appendix G in `paper/sections/nonnegative_lower_proof.tex`, its model and main theorem in `model.tex` and `general_results.tex`, the lower overview, and the new formal-scope and AI text. I then inspected the actual candidate public declaration and its input, success, cost, normalization, and quantitative dependencies. Earlier reports supplied hash/provenance evidence, not a substitute for that inspection.

`NonnegativeRawMain.SucceedsOnClass` quantifies over actual integrable rows satisfying `NonnegativeInputClass.Admissible`: total one, density between 1/2 and 3/2 almost everywhere on the resource, and finitely many step boundaries. `uniform_admissible` and `inputRows_admissible` prove that the baseline and all concrete pulse profiles belong to that class. Endpoint values and values outside the resource do not alter these nonatomic valuations. The public probability space is arbitrary, and the same next-action function is jointly measurable in tape and history. There is no finite-support randomness, expected fragmentation, finite-expectation, termination, detector, replay, or decoder assumption hidden in the endpoint.

`RawFair` is the literal signed-density measure comparison of physical bundles, with the correct opposite inequalities for cake and chores. Success requires an actual finite return, valid geometry, and those comparisons. The flag parameter selects counted unavailable-target replies or terminal illegal requests. Positive hard densities make successful Cut roots unique; `cut_reply_preserved` uses only the left-to-returned-root integral, not an uncharged extra bracket-total reply. Malformed bracket geometry remains terminal in both variants.

The quantitative correspondence is exact:

| Declaration | Conclusion |
| --- | --- |
| `all_windows` / `all_windows_attempted` | The maximum of zero and `(np−1)/w − (n−1)/(2nw²)`, for `0<w≤1/2` |
| `optimized_attempted` | `n(np−1)²/(2(n−1))` for `n≥2`, `0<p≤1`, and `np≥3−2/n` |
| `quadratic` | A positive constant `p²/8` times `n²` when `np≥3`, first on answered cost |

The proved pointwise answered-to-attempted domination transfers the quadratic conclusion to the paper's all-call interpretation. The optimized threshold is precisely the admissibility condition for the selected window, and the `p=2/3`, `n≥4` specialization is consistent. For fixed positive p these statements imply the advertised asymptotic order; they do not claim a stronger order or a fixed positive approximation tolerance. `verification/main_results.json` selects the correct two public declarations and describes their different cost formulations accurately.

## Failure accounting, free endpoints, and proof chain

The executor returns or diverges even at exhausted query fuel; only a pending request is capped. `queryCost` is the supremum of answered lengths. `AttemptedQueries.attemptedCost` adds exactly one for an exposed terminal illegal request and adds nothing for an unconsulted pending request. Expectations integrate over the entire tape space on the uniform profile, including wrong returns, malformed outputs, finite-query divergence, and infinite querying.

`RawIntervalPartition` accepts a finite unsorted record count and arbitrary real endpoints, with no relation to query coordinates and no common count bound. `valid_iff_geometry` identifies its valuation-independent test with bounded, disjoint `(left,right]` records covering `(0,1]`, plus an explicit owner of zero. `decode_some_iff`, `decoded_share`, and `decoded_value` preserve physical shares and values. The rational-coverage proof uses the finite set of right endpoints below a hypothetical uncovered point; it does not infer full coverage from density of rationals alone. `decode_measurable` supplies the required measurable normalization.

`OutputPostprocess.run_normalized` preserves the answered transcript exactly and turns invalid returns into query-free divergence. Its answered and attempted costs are pointwise unchanged. `normalized_success` identifies the full success event, and `malformed_return_failure` rules out later success after an invalid terminal return. Thus failed costs are preserved instead of discarded during normalization.

The precise encoding is a disjoint partition-record grammar. Redundant overlapping same-owner union expressions and arbitrary malformed program bytes are not a verified parser domain. Endpoint changes preserve every density value by `value_eq_of_endpoint_change`; no universal endpoint-tag or union-expression compiler is asserted. This is compatible with the paper's standard finite interval-output model and the new appendix's finite-representation claim. It does not limit arbitrary finite fragmentation or free endpoint choice.

I also checked the current probability/retention assembly. Detection is a union bound over the whole fixed baseline transcript, with probability at most `w/n` per determining request; it does not condition adaptive requests on nondetection. The physical decoder uses equal ownership fibers of every uniform EF output and the correct favorable owner for each orientation. `retained_event_inclusion` supplies replay and wrong-output gap persistence for actual executions. `capped_retained_lower` combines that inclusion, the actual decoder/detection estimates, and fixed-input failure probabilities. The scalar retention lemma absorbs the terminal-illegal contribution using old failures, without an extra one-call loss.

`NonnegativeLower.all_windows` first disposes of infinite expectation, then chooses a deterministic finite cap and a deterministic sufficiently small width before sampling the tape/input. Endpoint and positive-gap losses tend to zero; only pointwise finite output counts are needed. It sends both errors to zero. This formal cap argument is a valid implementation of the paper's direct finite-query dominated-convergence argument, not an assumption of almost-sure termination. The same protocol and fixed-input guarantee remain in force throughout.

## Prior evidence and remaining release gate

All 95 candidate source hashes match the prior `lower_bounds_complete_closure/report.json`, whose recorded result is passed for 1,692 theorem declarations, with only the allowed axioms and external pinned-package oleans reused. All 13 hashes match `lower_adapters_targeted/report.json`. The earlier core-review hash of `NonnegativeMain.lean` also matches exactly. The model, Appendix G, and lower-overview hashes match the earlier final correspondence report. These comparisons establish preservation of that reviewed source evidence; they do not turn the prior worktree audit into a new whole-candidate cold audit.

The new appendix's lower-bound coverage claim is supported by the inspected endpoint. Its whole-package verifier and four-result claims still depend on the separate root-owned final audit and other role reviews. No expensive build, fresh compiler elaboration, or source mutation was performed here. No publication/human approval is inferred.

The JSON receipt records all directly reviewed paper/Lean source hashes, the endpoint manifest hash, PDF hash, prior audit-report hashes, and exact scope. No other review file was changed.

## Reviewed source hashes

| Candidate-relative path | SHA-256 |
| --- | --- |
| `paper/paper.tex` | `5fea7cd8956f9d6d01e3b18722214057de1f90364ab784bff88b5202b9cec590` |
| `paper/sections/model.tex` | `534b15490f651f91bad820971e5bd3a4e144cb277336b79808668c0cfee75b11` |
| `paper/sections/general_results.tex` | `d22b1b2152ba7c6efdf175b8db56015cdd39bc8d5ef6cd4813ae38cb10a6928b` |
| `paper/sections/nonnegative_lower_proof.tex` | `0e46119b7acce914a668234ebe3a322ff84fd983f874c2b4dd7c3c2498d68d8e` |
| `paper/sections/lower_overview.tex` | `91738d525c21c3c04b79ccfe529bdc36bf47a818498a18c47890b13561fd3b7f` |
| `paper/sections/formal_scope.tex` | `9bbb767af07618b809fcf0d09064a81ca6c3d7802cf3d9d99385364e47f39136` |
| `paper/sections/ai_methodology.tex` | `0991f71b9b0ff36a01c8ef74b0e6bc47351ab7ab2f6e06845c6e494a7bef530c` |
| `verification/lean/EnvyFreeResearch/Full/NonnegativeRawMain.lean` | `f7502eef7163684e13f51bf221d1a5038147bdfeee8a4321ef39701b22845a84` |
| `verification/lean/EnvyFreeResearch/Full/NonnegativeMain.lean` | `ecff9065c2e89b5f4671e0fe2937f59bb194f00f121124c400763e0d2dd8ee65` |
| `verification/lean/EnvyFreeResearch/Full/NonnegativeInputClass.lean` | `ead3ef0d53ec3ca5e8002e25a58ec2d444e94c13a2d5e800cc6b03660282ba49` |
| `verification/lean/EnvyFreeResearch/Full/NonnegativeLower.lean` | `afdbdcc7ce9c21e14c668391c615ba06f7e03b25f4d006741ff19b32cf64b889` |
| `verification/lean/EnvyFreeResearch/Full/NonnegativeHardFamily.lean` | `546e02d257d9127542239ec46e5077bf2fbd67e8cc18038223af6ac33dd12f59` |
| `verification/lean/EnvyFreeResearch/Full/NonnegativeMainEvents.lean` | `f0006666e39a1d9f553f7ac00cee4166ddfd457c641235cb45fe08ecf70df29b` |
| `verification/lean/EnvyFreeResearch/Full/NonnegativeOracle.lean` | `634ec2f7473898e1eab8472e1be8dba6a352140ccc37748746b0bcfeb160abc7` |
| `verification/lean/EnvyFreeResearch/Full/NonnegativeDetection.lean` | `563db8f8f690de3e18c0962c084e427babd3e6e4533dc045114bfb3747a7acc7` |
| `verification/lean/EnvyFreeResearch/Full/NonnegativeDecoderLedger.lean` | `e5a0766b0a2297cdc44d73f20400306787a9b0aa3b61159e8112615a5a43fc19` |
| `verification/lean/EnvyFreeResearch/Full/NonnegativeProbability.lean` | `804b4ff5b64348923836063b87b4d083775a76a1060741b9eee5d36c5c788a95` |
| `verification/lean/EnvyFreeResearch/Full/RawIntervalPartition.lean` | `dd4d9bb3aac7d463dacb50ca00bc6e5c85c0719dc3c2c3b090e59f799c5b923a` |
| `verification/lean/EnvyFreeResearch/Full/OutputPostprocess.lean` | `30fc79a185950c7a667803960a81a0d826e79da89ced595be95396ad359e9df5` |
| `verification/lean/EnvyFreeResearch/Full/AttemptedQueries.lean` | `711bf8c9e5bd1c9bfc08224856d5ac18b767fdd937f208f6d20d057417b71238` |
| `verification/lean/EnvyFreeResearch/Full/OracleProtocol.lean` | `2850d7f5b3c7da9eefdd9da82b62fae8b3ec90d84db46a18214fc1d5ebcf1270` |
| `verification/lean/EnvyFreeResearch/R8Lower.lean` | `1c1c28defbc1b063f8ec4e718af03cb9605c79e6d60eb5666fe7c933f1979379` |
| `verification/main_results.json` | `92713387ec533e57a59250226784c63ae133e18db38e95ae5e91767f70e82dfb` |
