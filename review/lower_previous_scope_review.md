# Independent lower-bound final-scope review

Review date: 2026-11-10. Reviewer: independent `lower_final_scope_review` agent.

**Verdict: PASS for the scoped mathematical result and the correspondence of its current public Lean endpoint. No blocking defect found.** The reviewed bound is

\[
\mathbb E Q_{\rm unif}\ge\max\{0,n(np-1)/2,n^2p/4-1\}.
\]

This is a source review of the lower-bound result, not a new whole-paper review or a compiler certificate. I ran no Lean compiler, paper compiler, tests, or commits and changed no manuscript or Lean source. I did not read or rely on earlier review conclusions. The complete final paper/PDF snapshot has not yet been supplied; a later binding refresh should check the source hashes below and the assembled theorem/appendix links.

## Scope and public statement

I read the lower appendix and overview, the lower theorem in `general_results.tex`, and the model, then followed `MoatMain.raw` through the moat proof and its probability, oracle, and raw-output dependencies. The endpoint assumes a single jointly measurable protocol, an arbitrary measurable tape type with a probability measure, `n >= 2`, `0 <= p <= 1`, the cake/chore Boolean, the unavailable-target convention, and correctness probability at least `p` for **every** admissible fixed profile. The manuscript restricts to `p > 0`, so Lean's allowance of zero is harmless strengthening.

`NonnegativeRawMain.SucceedsOnClass` quantifies over actual density rows satisfying normalization, almost-everywhere bounds `[1/2,3/2]`, and finite-step structure. Correctness is the measure of the actual finite-return event with valid complete geometry and literal row-value fairness. It is not an assumption that the hard-distribution average is correct, nor an assumed replay/detection contract. `MoatMain.normalized` applies this fixed-input guarantee to every center and row selection using `MoatFamily.admissible`. Endpoint values of finite-step densities have no effect on any value query; the almost-everywhere formal convention and the paper's density-window convention therefore agree for this result, and the concrete moat rows satisfy the pointwise bounds on the unit interval.

The conclusion uses `ENNReal.ofReal (max (...) (...)) <= expectedCost`. Because expected cost is nonnegative, `ofReal` supplies exactly the additional maximum with zero. `expectedCost` integrates the extended answered-query cost over all uniform-input tapes, including failures; there is no conditioning on success or termination.

## Independent mathematical checks

1. **Admissible hard inputs.** The positive bump has mass `h/2`; the compensating moat term also has mass `h/2`. Since `0 < h < w < 1`, both density orientations are normalized finite-step rows between `1/2` and `3/2`, with strictly increasing cumulative functions. Circle arcs are only a device for sampling and accounting. The physical queries and shares remain subsets of `[0,1]`. The Lean density, physical-integral, and admissibility definitions implement these same objects, including wrapped arcs.

2. **Replay uses one interval per answered call.** An Eval is determined by its queried interval. A successful Cut is determined by `[a,z]`, where `z` is its baseline returned root: preservation of that integral plus strict positivity preserves uniqueness, and the existence of this root in the original bracket preserves target legality without separately preserving the bracket total. An unavailable target is determined by its full bracket. Syntax-invalid brackets are input-independent. `NonnegativeOracle.oracle_eq_of_determined` handles all these cases; `flagged_run_replay` derives adaptive replay from the actual executor. The request rule sees only the fixed tape and answered transcript.

3. **Uncounted illegal calls are correctly charged.** The execution stops at the first illegal request. A capped determining list has at most the answered count plus one terminal illegal request. The indicator is zero on capped success, giving its expectation at most `1-s_T`. Lean conservatively includes even a syntax-invalid request in the list, which only weakens the estimate. `flag=false` is the paper's ordinary legal Eval/Cut convention with an uncounted illegal terminal request; `flag=true` additionally covers counted unavailable replies. The proof does not silently replace answered cost by attempted cost.

4. **Detection does not condition on an adaptive history.** For each fixed uniform tape the entire capped list is fixed. A specified endpoint lies in the width-`w` moat with probability `w`, while a row is selected with probability `1/n` or `2/n`. The union bound is respectively `2w/n` or `4w/n` per determining interval. The cyclic successor is distinct for every `n >= 2`, including `n=2`. `MoatTranscript.integrated_detection_le` establishes the product-measure version directly.

5. **The decoder has the right strict margin and chore orientation.** Uniform success gives every share length `1/n`. When the bump lies within one owner's share, every other changed row has a cake-envy gap at least `h/2*(1-1/(nw)) > 0`; reversing the density produces the stated chore-envy gap. A single uniform changed row equals the bump owner with probability exactly `1/n`, regardless of how the owner varies with center. With two distinct changed rows at least one is a nonowner. The proof keeps `w > 1/n` throughout decoding and takes the boundary value only after the probability losses are removed. It never relies on decoding at the problematic equality case.

6. **Failed baseline returns are retained.** Each bundle's value moves by at most `h/2`, so one observer's comparison moves by at most `h`, even in the two-row experiment. Every incorrect complete uniform return has a positive longest-minus-shortest gap. If this gap exceeds `h`, the appropriate cake or chore witness remains strictly unfair. Malformed output, query-free divergence, and illegal termination are preserved by replay/validation. Infinite querying is handled by the infinite-cost case or the cap-exhaustion loss, rather than being presumed to terminate.

7. **A deterministic width suffices without bounded fragmentation.** For a fixed cap every returned endpoint list is finite, with no uniform or expected-size restriction. Pointwise endpoint-hit probabilities tend to zero, bounded by one. The small-positive-gap event also has probability tending to zero. Thus one width can make their combined loss arbitrarily small before the center, selected row, and tape are sampled. Lean's `small_geometric_loss` uses a slightly larger finite list (also containing capped determining endpoints and 0/1) and radius `h` rather than merely `h/2`; the same shrinking argument proves this stronger safety condition. This additional loss introduces no assumption or asymptotic cost term.

8. **Cutoffs and limits are valid for nontermination.** Here a cutoff is query fuel, not a wall-clock timeout. With finite expected answered cost, almost every uniform tape has finitely many answers. In this model it then has a returned, illegal, or explicit query-free-divergent terminal action, so cap exhaustion decreases to a null event. The small width may depend on the cap and width `w`, never on the sampled tape/input. The baseline success probability need not stabilize before choosing widths. The displayed elimination inequality is correct: after multiplying its right-minus-left difference by `n^2`, the result is `(n-2)(1-s)+2(nw-1)s >= 0`. Taking cap and geometric losses to zero and then `w` down to `1/n` gives exactly both claimed terms. At `p=1` the first becomes `n(n-1)/2`.

## Measurability and output scope

The next-action map is jointly measurable on tape times finite history; the tape itself is not assumed standard Borel, countably generated, atomless, or finitely supported. Joint measurability of the concrete densities, cumulatives, unique Cut replies, share values, capped runs, and eventual-success events is established in the inspected dependencies. `NonnegativeSuccess.fixed_input_failure_bound` averages the actual fixed-input eventual-success guarantee over an independent product law. Tonelli and product-coordinate swapping suffice; no conditional-distribution existence assumption is present.

`RawIntervalPartition.Raw` has arbitrary real endpoints and an arbitrary finite used-record count, with no query-endpoint restriction. Unused padded coordinates are irrelevant. Validity checks boundedness, pairwise separation, and coverage; the rational coverage test is proved equivalent to full coverage for finite half-open records. A measurable, valuation-independent decoder maps valid records to complete allocations and malformed records to query-free divergence. `normalized_success` gives equality of success events, and `answeredCost_normalized` gives pointwise equality of answered cost, including divergent executions. Thus the raw endpoint is not restricted to protocols carrying geometric proof fields.

The formal record convention is a finite disjoint interval decomposition, right-closed cells plus an explicit owner of 0. Arbitrary finite-union allocations admit such a decomposition up to reassignment of finitely many endpoints; `value_eq_of_endpoint_change` proves value invariance under such changes. This is the usual nonatomic endpoint convention and is compatible with the manuscript. The public raw theorem does not claim to accept every redundant textual representation of a union (for example overlapping records assigned to the same owner); those must first be represented by disjoint cells. This is an encoding convention, not a fragmentation or oracle-information restriction.

## Verification limits and source binding

The source path from the public endpoint to replay, physical decoding, and fixed-input averaging was inspected; no assumed outcome-level correctness contract was found. A read-only scan of all 91 project-local files in the transitive import closure found no `sorry`, `admit`, `axiom`, or `unsafe` implementation declaration; keyword hits were explanatory prose in `R4SignedLinear.lean`. This scan is not a replacement for the root agent's compiler/axiom checks, which were deliberately left undisturbed. Some old imported nonnegative results state weaker bounds; `MoatMain.raw` actually calls the new moat chain and does not select those old conclusions.

No correction is required within the reviewed lower-bound scope. Final release binding remains contingent on unchanged scoped sources or a scoped review of any subsequent differences.

### SHA-256 of directly inspected source files

The table binds the source bytes present when this report was written. Some shared foundational files were inspected by relevant sections rather than reread in their entirety.

| Source | SHA-256 |
| --- | --- |
| `research/submission_focused/paper/sections/nonnegative_lower_proof.tex` | `70ccd2452fba58437a68b8a287d79745538d07def0245ad9456cc9215a8e45aa` |
| `research/submission_focused/paper/sections/lower_overview.tex` | `7d7ea770ffbeaad8f4083cb106c8442f20b91b9a7e6d9c829694b5b124913d1d` |
| `research/submission_focused/paper/sections/general_results.tex` | `7bb8325969c0093e0022d0282414be8f13cd4702c5029b77f7403aa7a771871d` |
| `research/submission_focused/paper/sections/model.tex` | `534b15490f651f91bad820971e5bd3a4e144cb277336b79808668c0cfee75b11` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatMain.lean` | `b5e3b1ee1200571dc000cf09e55cf5b0a7210d91a915e4ee9cc067f1b9f284ca` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatLower.lean` | `4aaaffda0be95722aa0282d7ae61090c55183761363686d1426ae103f4cc40e3` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatCapped.lean` | `a08994c785b7cacf5e5586157877b637b97a205f745f6cf2b7a13e3aff1337dd` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatLimits.lean` | `930f0b76fa3f176b0ae5b3aac89f86a455de9037d7588105e079dc2452abef77` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatRetention.lean` | `8366c4a14da16cca0c0996d6dfc4ff2fbd5c8f6b8adec23f8913c8fcbbdf3504` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatReplay.lean` | `5a7e15f01f2dd1be3896ba70ce2dd54ed32f8c1097fe888af696db7534505a8f` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatReplayGeometry.lean` | `73dc5990149ca92486aac22eb5d74613ca5d70f4358fe92b7588350acfa63680` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatTranscript.lean` | `b67e9298f7d564becdff5e1767544bae142c3ba722fab6224c75c5a4fda9631e` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatExperiment.lean` | `eebd4a1619373e259e6c593ad99d3d195e5305ff86ad844d71120978c7416fca` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatFamily.lean` | `9932e3caaaa89b9715dfc4eea4d83007e6bee2e1c1251fb6da4feaf2c34e5b50` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatDensity.lean` | `25206bde85a2be7f1677286b83aca113033e7701efc8e77005e95990cd2835dc` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatPhysical.lean` | `589befec7709bbb1e1bf1f643a33c525f1ad52dbce13c2bf555ee8885550b09d` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatMeasurable.lean` | `d70f4fd3cd2264fa94c624be34025358a6c616d4d96be917488509f7434651e0` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatDecoder.lean` | `13de19a38a2e0df6b1478c3b246b9a27475739c2efb6a1c3b376a97f9220e7bf` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatSelection.lean` | `776ea5a99fecba514b38aac2f058352d07d6d6711030bddbc6beddd6c8c457d1` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatDetection.lean` | `614268beab093d2a80dff39a322443a055cb14d7210611a07bba7da4e8d3be47` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatLedger.lean` | `b939f5e431262aa8c71c6c48847d73d79423cb82613a3014383f324fb3cee2f6` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeRawMain.lean` | `f7502eef7163684e13f51bf221d1a5038147bdfeee8a4321ef39701b22845a84` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeMain.lean` | `ecff9065c2e89b5f4671e0fe2937f59bb194f00f121124c400763e0d2dd8ee65` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeOracle.lean` | `634ec2f7473898e1eab8472e1be8dba6a352140ccc37748746b0bcfeb160abc7` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeReplay.lean` | `b5b125814d9a912c216f8faa08159e4271d811474b16b9e098457e47c1b229d2` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeCostLedger.lean` | `084f64917767558dfb9ec5a8138d4fa182564a13e5d5e9e6e0f8ca6dea22ba7f` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeInputClass.lean` | `ead3ef0d53ec3ca5e8002e25a58ec2d444e94c13a2d5e800cc6b03660282ba49` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RawIntervalPartition.lean` | `dd4d9bb3aac7d463dacb50ca00bc6e5c85c0719dc3c2c3b090e59f799c5b923a` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/OracleProtocol.lean` | `2850d7f5b3c7da9eefdd9da82b62fae8b3ec90d84db46a18214fc1d5ebcf1270` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeSuccess.lean` | `39ae6ef32c9fdbabe505efeb5c4d0b27c5086b9439bdf969ac8f1b72664c47c8` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeProbability.lean` | `804b4ff5b64348923836063b87b4d083775a76a1060741b9eee5d36c5c788a95` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeRandomOutput.lean` | `7efb17ccf3f84d691fbc697e68ff49f979a17a7bf4d83c1fca2ea23bb9187e8d` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeMeasurableOracle.lean` | `c977f72579202835441e8a6c9d6da0fb73ca70a06798f72c900d3d99c170d28a` |
| `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/IntervalAllocation.lean` | `cca957bc5419474896dacad68c6f1444948cc043e8ad49d3e022a56b8387ff36` |

### Transitive local import-closure binding

The SHA-256 of the sorted manifest below (each line is `path`, a space, SHA-256, newline) is `564498c0edd1fb7df66b2267b99802848dc096d638e7f5bf5acb5577e903fd66`. This binds imports; it does not claim every line received a new human review.

```text
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/CoordinatedFamily.lean 407fd0a322ab1298f1c2a52b6ff9de391256a0cdafcb055c478bc6bd4022b451
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/AdaptiveOracle.lean 98ae4573285668d74df0e013a505e2f08c33e0428d40b1d5194a800841013331
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/AttemptedQueries.lean 711bf8c9e5bd1c9bfc08224856d5ac18b767fdd937f208f6d20d057417b71238
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/FiniteCapture.lean 9ac1d5ab2f4fef30ebdfd9de3ee52d6e56b3145c7780de61c46e4e85d3ca56ca
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/FiniteStepDensity.lean 7a7faf1428b410e08a5ce3a324f94c70618026f9b75a1b037703e32b87569656
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/IntervalAllocation.lean cca957bc5419474896dacad68c6f1444948cc043e8ad49d3e022a56b8387ff36
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/IntervalOracle.lean aa35aae155492d7425fd387e9efbd7f736bf10cb5d6d2e5f2620f9d7fa1b60e3
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/IntervalValues.lean 78fd1e45d4c9e86a96accbba41a3288090b68786d24c49d18b6ea12545ab73c2
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedBatch.lean 9f64a54e042eda57fc2b1b610983ec2cca360bc17f5d6f2b694d9d888ff25768
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedCaptureStep.lean 73f1dc4c41ea6263a528cd74066920d9435539b348601f296297972af2195fcd
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedCoordinates.lean 810c9aa467260184b53c21f952e24eff110e7cdf4c40624e9386da7a18a0db00
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedDensity.lean 7334170f28a7fa2e63c5626a77d30e49bd42fbb8b9c7fedf0049ba48407187de
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedExecution.lean 3fab5969712a24ff65830b224d0bd415b71439aaaffdbcc4f8883771d1b0452b
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedFiniteStep.lean 6445e01f307810c0ab793e43ebc61080c065f8a4d76986beffba340c2d469bb6
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedFrontier.lean 29e012e7f56381bf919860b57ae042961bb2a7eea130573f9b6aa46009032fb0
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedMeasurableOracle.lean 1d9547d4cdc2785c7e63d692f9da3ecb2db79173c5b4ef03f797fa490f4359b7
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedObstruction.lean 359220d7da8bab29f37dc3b18bb77a11fb5ea78f27a974fe88ffd938c83c6033
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedPhysicalFailure.lean d55696cf7dba6381b1ca2f629ab6835f9928ef4287f7dfbdca7a96ee42867c62
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedReplay.lean 8c9e4d014b3db3aa4a0a0ad51f64bac191f28a0e5a4d21493d765946159be6cf
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedViews.lean 5414c80253ff872621c52b5dc13b9ec9854ed2d9099ce17fe8e9d5a133d49e66
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatCapped.lean a08994c785b7cacf5e5586157877b637b97a205f745f6cf2b7a13e3aff1337dd
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatDecoder.lean 13de19a38a2e0df6b1478c3b246b9a27475739c2efb6a1c3b376a97f9220e7bf
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatDensity.lean 25206bde85a2be7f1677286b83aca113033e7701efc8e77005e95990cd2835dc
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatDetection.lean 614268beab093d2a80dff39a322443a055cb14d7210611a07bba7da4e8d3be47
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatExperiment.lean eebd4a1619373e259e6c593ad99d3d195e5305ff86ad844d71120978c7416fca
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatFamily.lean 9932e3caaaa89b9715dfc4eea4d83007e6bee2e1c1251fb6da4feaf2c34e5b50
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatLedger.lean b939f5e431262aa8c71c6c48847d73d79423cb82613a3014383f324fb3cee2f6
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatLimits.lean 930f0b76fa3f176b0ae5b3aac89f86a455de9037d7588105e079dc2452abef77
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatLower.lean 4aaaffda0be95722aa0282d7ae61090c55183761363686d1426ae103f4cc40e3
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatMain.lean b5e3b1ee1200571dc000cf09e55cf5b0a7210d91a915e4ee9cc067f1b9f284ca
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatMeasurable.lean d70f4fd3cd2264fa94c624be34025358a6c616d4d96be917488509f7434651e0
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatPhysical.lean 589befec7709bbb1e1bf1f643a33c525f1ad52dbce13c2bf555ee8885550b09d
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatReplay.lean 5a7e15f01f2dd1be3896ba70ce2dd54ed32f8c1097fe888af696db7534505a8f
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatReplayGeometry.lean 73dc5990149ca92486aac22eb5d74613ca5d70f4358fe92b7588350acfa63680
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatRetention.lean 8366c4a14da16cca0c0996d6dfc4ff2fbd5c8f6b8adec23f8913c8fcbbdf3504
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatSelection.lean 776ea5a99fecba514b38aac2f058352d07d6d6711030bddbc6beddd6c8c457d1
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MoatTranscript.lean b67e9298f7d564becdff5e1767544bae142c3ba722fab6224c75c5a4fda9631e
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeAllocation.lean 8f2e8fd89dcdcee47cbc26352a13f1644879a892d7fff9df8d09c013efc8b1e2
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeAllocationDecoder.lean 5c5150719d67c264eb3c426ff75593c6b0d20fb305483229e236c522afe3d93e
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeCircle.lean 8e1812674c2fe72cee5efd7e6c55306e17af755109c5499230a91532274e2ffa
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeCostLedger.lean 084f64917767558dfb9ec5a8138d4fa182564a13e5d5e9e6e0f8ca6dea22ba7f
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeDecoder.lean 255778be7171410bbfba6874fd3454fa6d467cd465c81a55f107541fb9944aef
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeDecoderLedger.lean e5a0766b0a2297cdc44d73f20400306787a9b0aa3b61159e8112615a5a43fc19
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeDetection.lean 563db8f8f690de3e18c0962c084e427babd3e6e4533dc045114bfb3747a7acc7
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeEndpointCapture.lean 7fca41c8a714e18824b6bb554e8286e78f4b235b3b34af431b8040f935cfd2b9
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeEndpointLaw.lean 12732e70b7fbdf2dac951edac7dc1da0fa3fdf01bef0de9d204a5bd2cc973941
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeExperiment.lean c650d64f1355ab61c285101453aa678046cd1203461dfc4b80d2b133e21caabd
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeFailure.lean 31eafb7aa8fbd48ab0a7855e3f74f49955ba3002fa869f855363baaa8e0359ac
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeGeometry.lean 0d0c9dd06c9c8d8557ff289fee05d38bc2040d0d1bcab6408c52d77cd79a0f00
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeHardFamily.lean 546e02d257d9127542239ec46e5077bf2fbd67e8cc18038223af6ac33dd12f59
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeInputClass.lean ead3ef0d53ec3ca5e8002e25a58ec2d444e94c13a2d5e800cc6b03660282ba49
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeLower.lean afdbdcc7ce9c21e14c668391c615ba06f7e03b25f4d006741ff19b32cf64b889
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeMain.lean ecff9065c2e89b5f4671e0fe2937f59bb194f00f121124c400763e0d2dd8ee65
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeMainEvents.lean f0006666e39a1d9f553f7ac00cee4166ddfd457c641235cb45fe08ecf70df29b
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeMeasurableDetection.lean f297e42726df1c34f69a1b0eb988dab93ffd7ac4f47fc27bbe0aa528c2df437f
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeMeasurableOracle.lean c977f72579202835441e8a6c9d6da0fb73ca70a06798f72c900d3d99c170d28a
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeMeasurablePulse.lean c74c33242ea884358c203533b55ff53372ce850939c1dde2c9d8d9084c052bfa
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeOracle.lean 634ec2f7473898e1eab8472e1be8dba6a352140ccc37748746b0bcfeb160abc7
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeOutputMeasurable.lean 7f149b7882c897f25d6d98e047506f3052b73fc5e616c843916f83c01f2a1614
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeProbability.lean 804b4ff5b64348923836063b87b4d083775a76a1060741b9eee5d36c5c788a95
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeProfile.lean 10b1e8b6e9d7c9d18350f5e24e3697a7e71c16a871dafa1ffed73f9dc8f10280
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativePulse.lean 49dc97bfe22dacd475fde01f3905c3723254de75d2ae67f84f5a1e3a100f63a6
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativePulseGeometry.lean 0e53e6ce5780fac709e9e064a9c3a460411b1a584eaa585bdfc6b6351219070d
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeRandomOutput.lean 7efb17ccf3f84d691fbc697e68ff49f979a17a7bf4d83c1fca2ea23bb9187e8d
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeRawMain.lean f7502eef7163684e13f51bf221d1a5038147bdfeee8a4321ef39701b22845a84
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeRealLedger.lean 5bb12288b30b65a03bd3e234a6f1611348bbb76ec6462624f548ece61136145d
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeReplay.lean b5b125814d9a912c216f8faa08159e4271d811474b16b9e098457e47c1b229d2
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeRetainedFailure.lean 7cb59ddacc2dd59c247a7753e60f7d8a25d8539a7dcf08a8cd39be96f9601eb4
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeShift.lean 4528c7fcaa1d3b2e983e6e319bf92b3adeddf9a27df04ae73900f0d619ccb2ad
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeSuccess.lean 39ae6ef32c9fdbabe505efeb5c4d0b27c5086b9439bdf969ac8f1b72664c47c8
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/OracleProtocol.lean 2850d7f5b3c7da9eefdd9da82b62fae8b3ec90d84db46a18214fc1d5ebcf1270
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/OracleStep.lean 3232eba2733094c9221893536cbdaadbf9aa3f348b0af4617c6a3f58111a56bf
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/OutputPostprocess.lean 30fc79a185950c7a667803960a81a0d826e79da89ced595be95396ad359e9df5
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/PhysicalReflection.lean 69aa5d8a341eca53ff341cd4edf936bc3b656e6527e74f165077ac3a97b82bfc
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/ProtocolMeasurable.lean 9f713d33c3815f85d1ae5ae2b7d6f530d83ea5191e22d6b73aa408698c3663b3
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RawIntervalPartition.lean dd4d9bb3aac7d463dacb50ca00bc6e5c85c0719dc3c2c3b090e59f799c5b923a
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RawPartition.lean dcc8646ed916bb2f777c5870c08e180f516c8ad6c3ff8dd3a514aab5cec126d6
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/MixedApproximation.lean 8c05d27553a859ed033a3283dc6f24daa9185e5b32ed59ee0f208a345a5488ea
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/QueryProbability.lean c050c1da43d681952b4529a783dbb11efcf42ab70e26d27665c20cc37ea47241
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/R2Variation.lean 0a9fa545e122d716e8efcb2d461425becdb8c82068efd1b3416347e3e38f94ad
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/R3PrioritySelector.lean 4212e5fb9f09e33f9b61f50c0d9866552c9234f45abfb39f0d029d726cdab949
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/R3QueryLower.lean c0b02f530fb6b5ae55956c9a2033b1c434eec0ae46396204898a774180210d61
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/R4SignedLinear.lean 54dfa3931c9f46c8207a2b75153e25737fb4a1488057b5942d7ac3d7eacc99e1
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/R6Lower.lean a0c5959b5f57b7fe91193810aafc2e8edce43652278b3a420e86266af07c64b6
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/R6MixedMonteCarlo.lean 4687f618d3d87757a310fa248396f0a34cdbfdfd9d673a687157e6e72b5d9a04
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/R7Lower.lean e01cc88998e40ff364df74a56205e561a743944095c8c288a74ded3ae3ea937e
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/R8Lower.lean 1c1c28defbc1b063f8ec4e718af03cb9605c79e6d60eb5666fe7c933f1979379
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/RootPreservation.lean 56a0fb03138da1e852b3f0fdda8390ea693323290eefb238b24a657de813d723
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Signed.lean c7d94938de433d6c4422005f946741eb3f806aa99cd51dc284e37be0426b8199
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/SubmissionMonteCarlo.lean bc95434ba31de8616bb915203b21f7cc4ad93e3099b581765d20ca65e6a1386f
research/formalization/all_main_results/verification/lean/EnvyFreeResearch/TranscriptAdversary.lean a6f46cba0c168260e2863e0caf0fe9ec3d0d9e7ef1438e8adb2cc203d3a6bae3
```
