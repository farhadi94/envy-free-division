# Independent scoped review: mixed impossibility

Review date: 2026-11-10. Reviewer: independently delegated `mixed_final_scope_review` agent. Scope: the mixed paper theorem, relative-envy definition, proof, overview, and `Full.MixedIntervalMain` with the concrete dependencies described below. This is a one-result source review, not the mandatory fresh final whole-paper proofread and not a binding of a final PDF. No existing reviewer conclusions were read or used. No source edits, compilers, or commits were performed; this report is the only written artifact.

**Verdict: no blocking mathematical or endpoint-scope defect found.** The stated impossibility follows for each fixed n >= 3, success p > 0, multiplicative factor 0 < alpha <= 1, and separately additive tolerance 0 <= epsilon < 1 in net-value units. Both prescribed root policies are covered separately. The conclusion is unbounded supremum of unconditional expected query costs over normalized finite-step signed inputs, not infinite expectation on one input.

## Paper proof checks

1. **Relative comparison and normalization.** The displayed signed relative comparison has the claimed sign-sensitive threshold. For a complete allocation and a positive observer total, at least one bundle has positive value; comparison with it forces strictly positive own value. All negative-bundle comparisons then hold automatically, while nonnegative comparisons reduce to own >= alpha times other. This supplies the reduction on totals-one inputs without interpreting signed ratios at zero or negative totals. The stated own-value lower bound follows by summing only the n-1 nonself cake comparisons. Taking epsilon = 0 yields relative multiplicative EF; taking alpha = 1 yields additive epsilon-EF.

2. **Unsplit-tail obstruction.** Starting with everything assigned to c gives each nonowner comparison alpha. Moving a fraction of a resolved cell to k changes the average by the stated coefficient. I checked all four positions of the unique positive entry: absent, c, k, and another agent. The required extra nonowner exists precisely because n >= 3. With K = (1+alpha)/alpha the coefficient is nonpositive in each case. Fractional assignment of every cell is allowed, so the argument does not assume resolved intervals remain intact. At least one gap remains >= alpha > epsilon.

3. **Finite physical update.** Preserving queried row j everywhere and using -K d_j on the new prefix for other rows retains their net total one and a strictly positive remaining-tail slope. A changed cumulative decreases from a value < 1 and then increases to one, so no earlier attainment of level one is introduced. Every finite sequence of updates has finitely many finite constant densities and finite total variation. No uniform bound on those variations is used or obtained.

4. **Least-root replay.** Frozen bracket endpoints preserve interval values and signed-target legality. A frozen reply <= frontier remains least because the entire interval from the left endpoint to that reply is unchanged. A reply at one has absolute cumulative target one and remains least by the strict barrier. The a = b = 1, t = 0 case is separately harmless. Negative targets, zero targets, full-bracket targets, degenerate brackets, and zero-total brackets are not silently excluded. Preserving an entire selected row protects its newly observed response before it becomes part of the frozen history.

5. **Fixed-input randomized capture.** The row pigeonhole step retains >= 1/n of the current measurable tape set, and continuity from below supplies a deterministic coordinate threshold retaining >= 1/2 of that row set. After h query stages and an output stage, the newly failed mass is >= u/[2(2n)^h]. The threshold may be chosen with coordinates <= r; equality with the new frontier is sufficient. Arbitrarily long finite output records still have a proper-coordinate maximum < 1. No expected or uniform bound on output size is needed. The h = 0 case is covered.

6. **Permanent failure retention.** Earlier captured tapes keep their real transcripts and returned records under every later extension. Their output values are also preserved because cumulative values at all finite endpoints and at one remain fixed. Nonreturns stay nonreturns because the same tape and real history determine the same next computation. Thus adding the new subset to H is valid; repeatedly capturing a positive fraction of the complement is not merely repeatedly finding possibly different failures. Finite geometric amplification yields one final profile fixed using the tape law before the realized tape is drawn. No distribution over profiles, joint profile measurability, infinite adversarial limit, or tape-dependent input is required.

7. **Measurability.** The model's jointly measurable next-action convention, including query-free nonreturn, supplies the fixed-input call/return data used by the proof. The root-below-q event is Borel by minimization of a continuous function over a varying compact interval; rational thresholds recover strict sublevel sets of the least root. Finite record encodings give measurable proper-coordinate maxima even for unbounded record lengths. The argument does not require a computational test for nontermination. Arbitrary probability tape spaces, including atomic and ideal-real tape laws, are permitted.

8. **Ordinary-query wrapper and expectation.** Aborting before attempted call q+1 and checking a Cut target by an extra Eval produces a pointwise-legal strategy using at most 2q calls. The hidden Eval does not alter the simulated protocol's history, and the prescribed least-root rule produces the same legal Cut replies. The wrapper permits finite output or query-free divergence after call q, and validates geometry without testing fairness. Its success event is exactly S intersect {Q <= q}. Consequently the same hard input has E[Q] >= (q+1)(p-delta), with no conditioning on success and no assumption that failures terminate or have finite costs. Taking arbitrarily large natural q gives the required lack of a uniform finite bound.

9. **Reflection and sharp range.** With reflected cumulative F*(x) = F(1)-F(1-x), the bracket value B is unchanged and target t becomes B-t on [1-b,1-a]. This maps the signed legal interval onto itself even when B < 0 and reverses root order. One Eval plus one least-root Cut simulates a greatest-root Cut with at most twice the cost; values and fairness are preserved by reflecting outputs. Invalid calls can be rejected as in the preceding wrapper. At epsilon >= alpha a whole-resource allocation satisfies the combined linear comparison on totals-one inputs, so the stated threshold is sharp for that combined predicate. This is not a variation-normalized statement.

## Lean endpoint and dependency checks

The public endpoint reviewed is `EnvyFreeResearch.Full.MixedIntervalMain.finite_step_attempted_expectations_unbounded`; the relative specialization is `relative_attempted_expectations_unbounded`. The general-input lift is `attempted_expectations_unbounded`.

- `StepInput` contains actual integrable real density rows, normalized by cumulative value at one, with finite-breakpoint certificates. `MixedDensity` proves the signed-measure realization, interval/cumulative correspondence and atomlessness; `MixedFiniteStep` and `FiniteStepDensity` retain the finite-step property through updates and reflection. Hardness on this subclass is sufficient to rule out a protocol on all finite atomless signed Borel measures. The formal domain does not purport to enumerate every singular atomless signed measure.
- `RootRule` has exactly the constructors `leftmost` and `rightmost`. `IntervalOracle` defines the ordinary signed bracket and constructs its least root from continuity. `RightmostOracle` and `RightmostCorrespondence` prove that the direct physical rightmost oracle returns the greatest root, including the reflected query legality identity. The formal rightmost endpoint proves capture directly on reflected states; it need not formalize the paper's two-query simulation to establish the claimed endpoint.
- `OracleProtocol.run` is a recursive executor over the tape and answered history, with returned, diverged, illegal, and exhausted outcomes. The fuel test applies only when another query is requested; returns and query-free divergence after the last allowed answer remain visible. `AttemptedQueries` adds the final illegal attempt and takes the supremum over caps. Infinite-query executions have infinite extended-natural cost. Failed executions are retained in the unconditional integral.
- The finite-horizon chain is concrete: `MixedFrontier.advance` -> `MixedReplay` / `MixedCaptureStep` -> `MixedBatch.exists_batch` -> `MixedAmplification.exists_almost_all_protected` -> `MixedFiniteStepMain.left_finite_horizon` (and the reflected chain). The endpoint does not assume a capture theorem, an adversary guarantee, or an EF result as an input field. `Extends.steps` preserves finite-step certificates through every batch.
- `MixedExecution.protected_of_extends` proves preservation of old protected executions, and `Extends.preserves_output_values` explicitly proves preservation of their physical bundle values. The formal obstruction uses two arbitrary distinct nonowners and pair coefficients, whereas the paper averages all nonowners. Both are valid consequences of the same density invariant. The formal output-capture update preserves an arbitrary designated base row instead of using the paper's optional all-negative update; this still satisfies the obstruction and all replay requirements.
- `MixedMeasurableOracle` proves Borel least-root selection (including failure outside the legal domain). `MixedViews` derives the concrete capture views from the ordinary measurable next-action map. `MixedSuccess` proves success measurability and the exact successful-cost-below-cap identity. `QueryProbability.supremum_expectations_eq_top` applies an actual indicator/integral bound and proves an infinite supremum, rather than postulating an expectation transfer.
- `RawIntervalPartition` permits arbitrary unsorted finite records. `Valid` checks boundedness, disjointness and complete coverage; its rational coverage condition is proved equivalent to exact finite-interval coverage. `decode_measurable`, `decode_ofAllocation`, and endpoint-null value preservation support the finite-union output interpretation. `OutputPostprocess.run_normalized`, `returned_normalized_iff`, and `attemptedCost_normalized` show that discarding invalid outputs preserves success exactly and does not change actual attempted costs. The countable-function padding in raw records allows additional irrelevant coordinates; canonical padded finite encodings are included.
- The endpoint assumes finite agents with measurable singletons, an arbitrary probability tape space, a measurable next-action map, n >= 3, alpha > 0, epsilon < alpha, p > 0, and success at least `ofReal p` for every normalized finite-step input. It does not assume pointwise legality, termination, finite expectation, queried output endpoints, bounded output length, or bounded variation. The relative specialization additionally assumes alpha <= 1. The linear theorem's lack of epsilon >= 0, alpha <= 1, or p <= 1 hypotheses is a harmless strengthening; the paper's parameter range specializes it directly. Additive impossibility uses alpha = 1.
- I scanned the 55 local transitive Lean modules for `sorry`, `admit`, custom `axiom`, and `unsafe` declarations and found no matches outside comments. This is a source-level observation, not a fresh kernel or axiom audit. I deliberately ran no compiler and do not certify a build or imported Mathlib trust closure.

## Findings and limits

No required mathematical correction emerged. One low-priority notation clarification is recommended in `mixed_lower_proof.tex`: replace “Fix q >= 0” in the expected-query proof with an explicit q in the natural numbers. The q+1 call, horizon 2q, and bound (q+1)(p-delta) already make the intended discrete parameter clear.

The claim must retain the present restrictions: finite-union interval outputs on every successful return; signed bracketed Cut; a separately fixed always-leftmost or always-rightmost selector; n >= 3; positive fixed success probability; the stated multiplicative range or additive epsilon < 1 in net-value units; and no common total-variation ceiling. This review does not establish impossibility at n = 2, at additive epsilon >= 1, with infinite output partitions, under variation-normalized error, under a fixed variation ceiling, or for an unspecified stronger query oracle. It does not establish existence or nonexistence of fair allocations, a minimum output-boundary lower bound, or one input of infinite expected cost.

Any subsequent change to a hashed source requires a scoped recheck; changes elsewhere in the full paper/PDF are outside this verdict. The final whole-paper proofread remains separate.

## Source binding

SHA-256 values below bind the four paper sources and all 55 local transitive Lean source modules of `MixedIntervalMain`. Dependency-manifest hashing does not mean every supporting lemma in every module was independently re-proved; the substantive review followed the chain documented above. Compiler outputs, old reviews, and PDFs are not included.

Hash capture (UTC): 2026-11-10T14:38:48.438079+00:00

SHA-256 of the exact sorted manifest block below, including its final newline: `3027537f460b8747fc3f03988d858babfe46bb2399340533b400198a1eca76c9`.

```text
407fd0a322ab1298f1c2a52b6ff9de391256a0cdafcb055c478bc6bd4022b451  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/CoordinatedFamily.lean
98ae4573285668d74df0e013a505e2f08c33e0428d40b1d5194a800841013331  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/AdaptiveOracle.lean
711bf8c9e5bd1c9bfc08224856d5ac18b767fdd937f208f6d20d057417b71238  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/AttemptedQueries.lean
9ac1d5ab2f4fef30ebdfd9de3ee52d6e56b3145c7780de61c46e4e85d3ca56ca  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/FiniteCapture.lean
7a7faf1428b410e08a5ce3a324f94c70618026f9b75a1b037703e32b87569656  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/FiniteStepDensity.lean
cca957bc5419474896dacad68c6f1444948cc043e8ad49d3e022a56b8387ff36  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/IntervalAllocation.lean
aa35aae155492d7425fd387e9efbd7f736bf10cb5d6d2e5f2620f9d7fa1b60e3  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/IntervalOracle.lean
78fd1e45d4c9e86a96accbba41a3288090b68786d24c49d18b6ea12545ab73c2  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/IntervalValues.lean
c9cafa818af0573f1b5b479816a97da3e61a2ee047dc1090e032f6dad13c9ed8  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedAmplification.lean
9c2a23740405a7380311424acdae1e25ca40a4ab5a41c5875b29da0aed65cadc  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedAttemptedMain.lean
9f64a54e042eda57fc2b1b610983ec2cca360bc17f5d6f2b694d9d888ff25768  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedBatch.lean
73f1dc4c41ea6263a528cd74066920d9435539b348601f296297972af2195fcd  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedCaptureStep.lean
810c9aa467260184b53c21f952e24eff110e7cdf4c40624e9386da7a18a0db00  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedCoordinates.lean
20d61e74af43f98d517403aee09a76417b852246f16c569db30e51d2274b2ba8  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedCorrespondence.lean
7334170f28a7fa2e63c5626a77d30e49bd42fbb8b9c7fedf0049ba48407187de  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedDensity.lean
3fab5969712a24ff65830b224d0bd415b71439aaaffdbcc4f8883771d1b0452b  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedExecution.lean
6445e01f307810c0ab793e43ebc61080c065f8a4d76986beffba340c2d469bb6  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedFiniteStep.lean
7df5ade635d44549625c13eb77545716f253eab6ca96525bb2e87abf86c3c17f  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedFiniteStepMain.lean
29e012e7f56381bf919860b57ae042961bb2a7eea130573f9b6aa46009032fb0  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedFrontier.lean
51750ebc1ee0f3e83d72aab6c57887901f3c1711026945de01be943daa314bfc  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedIntervalMain.lean
78b49a9c335443843473ad629df28e9e123c7daed0946308b7cf673c1154848d  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedLeftmostMain.lean
1d9547d4cdc2785c7e63d692f9da3ecb2db79173c5b4ef03f797fa490f4359b7  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedMeasurableOracle.lean
359220d7da8bab29f37dc3b18bb77a11fb5ea78f27a974fe88ffd938c83c6033  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedObstruction.lean
d55696cf7dba6381b1ca2f629ab6835f9928ef4287f7dfbdca7a96ee42867c62  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedPhysicalFailure.lean
b739574dc13087fb78ffee57d12ef017267c1fcbcd7e367306a0f735b777522b  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedPhysicalMain.lean
bfb5f26ce0c940f1ee18acc3359bf94271cc7da85c3e40bbabffc4ee0920cd06  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedRawMain.lean
8c9e4d014b3db3aa4a0a0ad51f64bac191f28a0e5a4d21493d765946159be6cf  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedReplay.lean
9e6d0925ae274dfe7c2336c28e1b43ea5de861611485cfce9d264c1cb1affb59  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedSuccess.lean
5414c80253ff872621c52b5dc13b9ec9854ed2d9099ce17fe8e9d5a133d49e66  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedViews.lean
7f149b7882c897f25d6d98e047506f3052b73fc5e616c843916f83c01f2a1614  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeOutputMeasurable.lean
2850d7f5b3c7da9eefdd9da82b62fae8b3ec90d84db46a18214fc1d5ebcf1270  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/OracleProtocol.lean
3232eba2733094c9221893536cbdaadbf9aa3f348b0af4617c6a3f58111a56bf  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/OracleStep.lean
30fc79a185950c7a667803960a81a0d826e79da89ced595be95396ad359e9df5  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/OutputPostprocess.lean
69aa5d8a341eca53ff341cd4edf936bc3b656e6527e74f165077ac3a97b82bfc  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/PhysicalReflection.lean
9f713d33c3815f85d1ae5ae2b7d6f530d83ea5191e22d6b73aa408698c3663b3  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/ProtocolMeasurable.lean
dd4d9bb3aac7d463dacb50ca00bc6e5c85c0719dc3c2c3b090e59f799c5b923a  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RawIntervalPartition.lean
dcc8646ed916bb2f777c5870c08e180f516c8ad6c3ff8dd3a514aab5cec126d6  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RawPartition.lean
f9feee1af851dbbfe9d58d9f1250fa9305413bcd734bf7dec9b5e67b34c76434  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostAmplification.lean
5babed92f848c737931284c9467c73a7aeffe7b988dddf8927a1b748c8bde48c  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostBatch.lean
b5ac9f422bc2e71d6748482c6b18d1ad098ae0c8694fa636d30fa994c02a00a6  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostCaptureStep.lean
7d95f93f6b7bf024f77bfea8484f9abbc9a2f92ef02da96adbcf355667ee1f13  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostCorrespondence.lean
a88f03024801cc1f5a187e14670b4d05303484fba7e2cf828a38972da60aba3c  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostExecution.lean
42ccfbe078c74d3653a749eb5c6f383eef1bb87df3521258f001be49ff0570f2  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostFailure.lean
58df8a5d8c33af21c71d41dd2b24b7c7003c572c0a27a54123b0cd692c19bf56  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostMain.lean
2ad77b55d5ab1054e292325fd7a4d4dba0c4224ea3bbc2e2ed9d0b5bee105f10  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostOracle.lean
4bac05eaf1611e65a8630dfad5914a50ad9f7d9b48a76a5f3b671cdd662efdea  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostOracleMeasurable.lean
8a4864ecc9239f5b9ba91efc5923ae5558c0a15264a9008d143901c2108f922d  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostReplay.lean
fc12efc661cc38ac8e25cecc66d42c1d6e7f360618d2be5829fa642bde7179c6  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostSuccess.lean
01994c323ec2ade266927bbd83da7f6c8a7b46ecb0f6dd6ba022a282c8182e38  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RightmostViews.lean
8c05d27553a859ed033a3283dc6f24daa9185e5b32ed59ee0f208a345a5488ea  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/MixedApproximation.lean
c050c1da43d681952b4529a783dbb11efcf42ab70e26d27665c20cc37ea47241  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/QueryProbability.lean
4687f618d3d87757a310fa248396f0a34cdbfdfd9d673a687157e6e72b5d9a04  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/R6MixedMonteCarlo.lean
56a0fb03138da1e852b3f0fdda8390ea693323290eefb238b24a657de813d723  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/RootPreservation.lean
bc95434ba31de8616bb915203b21f7cc4ad93e3099b581765d20ca65e6a1386f  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/SubmissionMonteCarlo.lean
a6f46cba0c168260e2863e0caf0fe9ec3d0d9e7ef1438e8adb2cc203d3a6bae3  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/TranscriptAdversary.lean
7bb8325969c0093e0022d0282414be8f13cd4702c5029b77f7403aa7a771871d  research/submission_focused/paper/sections/general_results.tex
7c1138114db4d71cb4ad56010a8f05834bf6adef393035225390496888ab7f43  research/submission_focused/paper/sections/mixed_lower_proof.tex
3c354a9219e6b922d06b6ce59bf2ef34c00d95ba2a827bfb18a84668b639bde3  research/submission_focused/paper/sections/mixed_overview.tex
534b15490f651f91bad820971e5bd3a4e144cb277336b79808668c0cfee75b11  research/submission_focused/paper/sections/model.tex
```
