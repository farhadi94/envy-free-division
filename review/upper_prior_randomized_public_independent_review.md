# Independent semantic review of the revised randomized public protocol

Review date: 2026-11-10. Reviewer: independent source-review agent. No source edits, compiler executions, publication, commits, or pushes were performed. This report is separate from final whole-paper proofreading and from the parent's compilation work.

## Conclusion

**No blocking semantic defect was identified in the targeted source chain reviewed here.** The public theorem states the intended exact cake/chore output and expected query exponents for a single protocol; the revised original-population parameters are connected to the local physical/probability statements and the reachable-state induction. Rejection histories and initialization are included in the cost chain.

This is a bounded mathematical/source review, not a certification of all 838 transitive local modules. In particular it does not independently reprove the deepest endpoint anti-concentration, interpolation, isolation, and correction-probability arguments. It supplies no compilation receipt and makes no inference from compilation success. The public integration was still being compiled by the parent when this task began.

## Concrete findings

### 1. The public contract does not assume successful execution or a physically valid output

`randomized_exact_envy_free_oracle` in `RefinedUpperGlobalOraclePublic.lean` takes finite atomless nonnegative measures, an `AdaptiveOracle.IsLegalPolicy` for their measure profile, answer-only `MeasurablePolicy`, a fallback agent, and the cake/chore flag. There is no public `SuccessFacts`, positive residue, good-grid, physical invariant, conditional acceptance, expected-runtime, or termination hypothesis.

The fallback inhabitant makes the result a positive-population theorem; it does not assert a zero-agent partition. Normalization supplies the small-population cases and handles the positive active population required by the paid primitives. `unitInitial_valid` discharges the initial invariant; `step_valid` proves the concrete transition invariant by cases; `run_valid` and `finiteRun_valid` perform induction on all finite tape prefixes. `unitRun_done_output` applies that invariant to an actual terminal phase.

### 2. The single next action is independent of both valuations and oracle policy

The definition `next fallback chores` has only the random stream and complete answered history as runtime inputs. It obtains its next observable action from `unitPrefixProgram`, which also has no measure or oracle-policy argument. Thus the public result is not a separate valuation-aware protocol for each measure profile.

The least-prefix construction uses countable search; `observable_actions_eq`/`next_eq_prefixAction` establish agreement with every observable prefix. `executes_observable_run` and `unit_prefix_next_run` then link the same fixed `next` to the actual macroexecution and trace. This is stronger than unrelated finite-prefix execution theorems. `next_measurable` proves the selection Borel on all tapes/histories, rather than only on successful executions.

The oracle contract permits arbitrary history-dependent choices among legal Cut roots. `AdaptiveOracle.Policy` receives history and query, not the unobserved random stream. `IsLegalPolicy` is the ordinary soundness/completeness condition at every history; no allocation, progress, or probabilistic success is embedded in it. This review found no forced extremal-root selector in the public hypothesis.

### 3. The output has literal physical meaning, including endpoints

`SingleProtocolOutputCorrect` asserts an actual returned `.done a` trace, pairwise disjoint decoded shares, union exactly `Icc 0 1`, and exact envy-freeness of the measures of those shares. `RefinedUpperGlobalUnit.output` produces finite lists of real interval endpoint codes with two endpoint-ownership bits. `decode_component` and `output_share` identify that decoding with the recorded physical component domains. The coverage statement is literal set equality, not equality modulo null sets, and degenerate/null fragments are retained. `output_measurableSet` supplies measurability of the decoded shares.

The raw returned object is a terminal phase/anchor. The finite interval allocation is its fixed, query-free decoding. The public theorem explicitly states fairness and coverage for that decoding, so this is not a value-matrix-only result.

### 4. Revised original-population Repair parameters reach actual executions

`RefinedUpperRepair` fixes all numerical scales from the original `n`, retaining active `k` only in the local tape/indexing and injection. The definitions are

- `s = 2^40 * max 4 n`, `ell = logarithm s`;
- coarse count `q = s^8 * ell`;
- sample count `m = s^9 * ell / 128`;
- repetitions `L = s^4 * ell`;
- cell bound `2/(s^8*ell)`, multiplier `s`, near-error `1/(4*s^2)`.

`scale_divisible` and `samples_cast` discharge the integral-division issue. `original_count_facts` obtains the required population bounds from the active injection `k <= n`.

`RefinedUpperRepair.failure_lt` delegates to `original_population_failure_lt`, which instantiates the raw actual-program failure theorem with the revised counts and proves its numerical envelope, parent budget, target budget, cell count, and retry bounds. `RefinedUpperRepair.success_facts` independently instantiates the actual physical-success theorem using the same revised parameters. The conditional success hypothesis there is an intermediate theorem premise used on the actual accepted branch, not a hidden public assumption.

One potentially suspicious old-parameter reuse was checked: `RefinedUpperRepairParameters.batch_allowance` uses the old arithmetic lemma only after rewriting both old and revised `repetitions * fineCap` to the identical expression `2/s^4`. It does not silently substitute the old sample count or old coarse count into the actual protocol.

### 5. Snapshot and Shrink are connected to those revised scales

Snapshot's `preparation_bad_bounds` passes the actual revised coarse/sample counts to the zero-branch and small-branch endpoint/interpolation estimates. `prepared_fiber_chance` treats zero, small, and large disagreement separately and uses the actual fresh Repair law. `snapshot_acceptance_probability` integrates the fixed preparation fibers and the three preparation exceptions under a measure-preserving tape rearrangement. It does not assume that a preparation happened to be good, or condition the final expected-cost estimate on inner success.

The old `small_configured_tolerances` reuse in `RefinedUpperSnapshotProtocolSmallReadyParameters` takes only the unchanged scale/accuracy inequalities; the revised near-error bound is proved explicitly. This is not an old-`m` substitution. Large-branch acceptance uses the revised Repair execution and the physically prepared candidate/reserve.

For Shrink, `carving_valid` applies the deterministic initialized carving theorem with `RefinedUpperShrinkPrecision.depth` and the revised near-error; its precision premise is discharged through `actual_precision`. `success_facts` and `failure_lt` pass that concrete carving validity into the revised Repair adapter. The explicitly assumed carving validity in the intermediate `RefinedUpperShrinkRepair` module is therefore discharged before the global theorem. The retained conservative depth is `32*k*ell`; it does not reintroduce the old coarse/sample exponent.

### 6. All attempted queries, including failures, feed the expected bound

The local cost theorems are statements for every tape, with no acceptance condition: Repair costs at most `6*n*m` queries and `3*m` Cuts; Shrink at most `8*n*m` and `4*m`; Snapshot at most `12*n*m` and `6*m`. Each provides an executed trace and a final-history append identity.

The outer failed-Repair transition refreshes the pending state with `result.2.1.history`; failed Snapshot refreshes its anchor similarly; the Shrink restart preserves the original cells while retaining the complete result history. Hence physical rollback does not erase paid queries. Snapshot's cost proof includes coarse preparation, attempted small-branch candidates, and optional fresh Repair.

`actual_prefix_counts` bounds actual history increments by the sum of reached phase caps. `totalQueries`/`totalCuts` are suprema of those actual history increments. The cost mean uses a bound on the actual `paidCount`, not accepted calls alone. `finitePrefix_attempt_bound` integrates the actual finite past and a fresh universal draw, using pathwise validity rather than assuming the reached valid-state set is measurable. The successful-call and normalization budgets are proved by finite-prefix induction and then passed to infinite sums. `actual_paid_mean` discharges the mean premise, and finite mean implies almost-sure termination.

Initialization contributes `2*n` Eval queries. Normalizations contribute the explicit `(n+1)*(n*(n-1)+1)` query allowance and `n*(n-1)+1` Cut allowance. The final bounds are `100*n^3*m` queries and `49*n^2*m` Cuts. Substitution of `m = O(n^9 log(2n))` yields the stated exponents 12 and 11 with a constant independent of `n`, the measures, and the legal Borel policy.

### 7. The public costs are those of the one protocol, with the measurability qualification stated accurately

The public theorem bounds `AdaptiveOracle.queryCost` and `markedCost isCut`, not just the macroexecution proxies. On almost-sure return, `single_protocol_actual_costs_ae` identifies the real protocol costs with its returned trace counts and bounds them by the macro totals.

`RefinedUpperGlobalOracleCostMeasurable` proves **AEMeasurable**, rather than claiming pointwise Borel measurability of the partial Option-valued policy or its actual costs. The totalized proxy uses `some ((oracle ...).getD 0)`. Returned-run replay makes its costs equal almost surely; its global legality is not assumed. The integral equalities and AEMeasurable conclusion therefore match the answer-only Borel oracle hypothesis. No stronger Option-policy Borel hypothesis was found hidden in the reviewed adapter.

## Qualifications and small documentation issue

- “Ordinary queries” here means the explicit `IntervalOracle.Query.eval agent left right` and bracketed `cut agent left right target` contract. This review does not prove equivalence with every differently defined Robertson–Webb convention.
- This is an exact-real query-complexity result with noncomputable/Borel internal definitions. It does not establish bit complexity, an effective numerical implementation, or bounded internal computation time. The countable next-action construction is consistent with the stated query model.
- Oracle policies are fixed functions of complete answered history and current query, with the answer adapter jointly Borel. The theorem is not a statement about a policy with additional access to unrevealed random tape, nor about arbitrary nonmeasurable root selectors.
- The result concerns nonnegative atomless measures, with the cake/chore flag reversing the fairness comparison. It is not a theorem for arbitrary signed utilities.
- Some inherited module comments are stale or locally scoped: `UpperCircularStage` says the global adapter “remain[s] open”; `RefinedUpperShrinkTrial` says carving remains to be discharged. Later reviewed modules do discharge those obligations. These comments do not create a mathematical gap, but can mislead a reader if quoted without following the imports.

## Audit procedure and source identities

A static traversal of the two public entry modules found **838 local `EnvyFreeResearch` modules**, no missing local import paths, and no `sorry`, `admit`, or standalone `axiom` declaration token lines in that closure under the simple source scan used. This is a source hygiene check only; it is not a substitute for a fresh compiler/axiom receipt, proof elaboration, or a full semantic audit. No `.olean` files or build logs were relied upon.

The following files were directly read in the targeted review. Hashes are SHA-256 of their bytes at report creation. The workspace is shared and was not frozen; later source changes require checking these identities. Merely imported or search-matched files are not counted as directly reviewed here. Every filename below is relative to `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/`.

| File | SHA-256 |
|---|---|
| `AdaptiveOracle.lean` | `98ae4573285668d74df0e013a505e2f08c33e0428d40b1d5194a800841013331` |
| `IntervalOracle.lean` | `aa35aae155492d7425fd387e9efbd7f736bf10cb5d6d2e5f2620f9d7fa1b60e3` |
| `UpperCircularStage.lean` | `df60987a9edf1fa9c6e331acdb3b08c607299bb48458e0fcb5436f409452add3` |
| `AdaptiveOracleReturnedCostTotalized.lean` | `ce63de4df0c76136a0f6723cc05bd99f78cbd73ad397cd67a8262c0d57b1f774` |
| `RefinedUpperGlobalOraclePublic.lean` | `9bcf8fd61157a9f2989b166550fe1814f8d9e6cfda64cab9ad139738b5f0ecd7` |
| `RefinedUpperGlobalOracleCostMeasurable.lean` | `613eea55414ec85cdda27f47c77c0a53edefbd8f1112aafe4c406dc278f14bd1` |
| `RefinedUpperGlobalOracleExecutionUnit.lean` | `5c6ac12bab640f872ca3169af44981a75a8b6ebed7dbb1e67a0a3b10b4e558b0` |
| `RefinedUpperGlobalOracleNext.lean` | `267b43122f5e0446bab33d5889afdd8c5339f1bdf105cc9d1978d5a37b3a87ee` |
| `RefinedUpperGlobalOracleExecution.lean` | `59706bd7947be2788d614af50e4c54dae04a2cce985e656f590ce22fc31e0fff` |
| `RefinedUpperGlobalOracleStabilityNext.lean` | `30e0b10f5ba2b650c86dbe965073c3ebd6cecb984912ca993c89cbea6babf925` |
| `RefinedUpperGlobalOracleNextMeasurable.lean` | `4103009624d05f439652f1db04d133c1c566073e207e582d828a6c921b712496` |
| `RefinedUpperGlobalProtocolPublicPolynomial.lean` | `bd5a3fe5818ca9e1d03eca29808bd16943ccbc6591656abc62da08cd67175691` |
| `RefinedUpperGlobalProtocolPublic.lean` | `697422b5c1e10428ce05f9fe1b630df2a96ba3467dc9d6dd3e4c963a77ee4eab` |
| `RefinedUpperGlobalProtocolCostLedger.lean` | `f41455b219bd1bb0e7923a2b2750d21ef418eead2c70de7c0ffda60ec2dc627c` |
| `RefinedUpperGlobalProtocolUnitRun.lean` | `e03cf8218c1894f02983a5be8ebcb5f92011b91e3fbefd8594f3f19989fe0b39` |
| `RefinedUpperGlobalProtocolValidity.lean` | `e576ef02c570366e3a910bc15e0416c60539c286ecb30c39e8760de61ee4d677` |
| `RefinedUpperGlobalProtocolFiniteValidity.lean` | `023c6b39457f3bbe6796f47c5a4d56ceba165675608203cf365b6625fbd22cd0` |
| `RefinedUpperGlobalProtocolCorrectness.lean` | `7f529f1e1a8e61227a069e92f908b4dee6ec8da0f7caf227af2a91b92ca01fe6` |
| `RefinedUpperGlobalUnitOutput.lean` | `5a15bc0fab33e7014a485d8c4133bcb9c2eda00f3d55e625c9fabb04cc484769` |
| `RefinedUpperGlobalProtocolDispatch.lean` | `eef0ec1195981e3137daf807a6450f875985d2a6d6ddfff3a88aca3910cccf46` |
| `RefinedUpperGlobalProtocolStageActions.lean` | `7780bcc466c421c461e7eea3e091bb1fdb211873d18149b0faf68932b7c1c1d4` |
| `RefinedUpperGlobalProtocolRepairAction.lean` | `2ee4abf12a0c339e7b24f8ae5f0e588997479e0d7f4c56fc48a9cdf5296c913e` |
| `RefinedUpperGlobalProtocolSnapshotAction.lean` | `cf7ff7a92127a7b474123a5da832b4f7c8c2392554fce266c635533113b81a39` |
| `RefinedUpperGlobalNormalizeCorrectness.lean` | `bdc3e4573140619b30f9eeb610a34cdc67667b0b9ab9cfe8822a61e1fcb25bcd` |
| `RefinedUpperExpectedRuntimeActualPaid.lean` | `d80b224482d93a3841d4ee92d96894784e35cf43ca974de3c45acdf0ffbe8e40` |
| `RefinedUpperGlobalRunCostMean.lean` | `553d765f867cde9a2690234927d669e35e85f567b89832dd8fc3ff654c8c0b65` |
| `RefinedUpperGlobalRunChancePrefix.lean` | `88921b0febc33f37b6deae542389a54d2f2858814574754f0e247d66e0d864ab` |
| `RefinedUpperGlobalRunBudgetPrefix.lean` | `3cd85a2402624950ea8a54a0a09ce819ba2049aeb8cfff862552346bf2b7540e` |
| `RefinedUpperGlobalRunBudgetTsum.lean` | `f9d01d88d0df22feb306ea4d23b49ca87b044a6e9f53c9b6e520c7ff1de215aa` |
| `RefinedUpperGlobalRunTerminationCounts.lean` | `1d83ce82d97b2679337a5631417bc662bee8443adcaca9df30df7a8fe86245a4` |
| `RefinedUpperGlobalRunTerminationFiniteMean.lean` | `d28218ee95bf479152a685bc141b75fa0451ec5d315e610188f7713e46fcb302` |
| `RefinedUpperGlobalQueryEnvelopes.lean` | `3b3d0f27e072cc096044cd5ec7bc767e86e40c93538b5fb46a33e226b035bbb0` |
| `RefinedUpperRepair.lean` | `e5f45147c2ed21990fb43948134fe8479ad20c505cd602665bb17bd6c85911a7` |
| `RefinedUpperRepairFailure.lean` | `4dbfe5e7a7cdac86a9e26c5024555eaf7f735d35a99999314bd86ed49982577f` |
| `RefinedUpperRepairProbability.lean` | `6241d4eab104c9a1bd74b736ca2b236c1c10f21ae6e12c6f31493fd25bca0d19` |
| `RefinedUpperRepairParameters.lean` | `afdd9f2d955892bb028125d1fc24ad664f73696e29adbe88f335b4ee921ad2e5` |
| `RefinedUpperParameterCounts.lean` | `0182bd00e7e2ee1c8c9e57ec3a6ae174d2b34cacc81dc55e865f2381185048a3` |
| `RefinedUpperRepairSnapshotConfigured.lean` | `40cadd24632eefa6a7e65fa9b20a49dc1a41596927766a2059698309df43e53b` |
| `RefinedUpperSnapshotParameters.lean` | `7c97eeae51cb0cab28dcb5a84c499438177da937d27f670e69393f2ec10a4f7d` |
| `RefinedUpperSnapshotProtocolSmallOriginalExecute.lean` | `0e20ca49bd553c32cd8210e23d658c9a26a6c6679f5fcae8302c5e4f91e4ca43` |
| `RefinedUpperSnapshotProtocolSmallReadyParameters.lean` | `bf5dba0f73b590b27a11458832d9280074fc6b5743dfc3f606c8c48cf2f000a2` |
| `RefinedUpperSnapshotProtocolProbability.lean` | `8b53552e39eccdd1d8c31255084fdf6045f341327559d17e91cca90656acd851` |
| `RefinedUpperSnapshotProtocolPreparationEvents.lean` | `1a88a7e5726602db8f62c82f0cdcc9f91846c0dd2072e0289250094e8611aced` |
| `RefinedUpperSnapshotProtocolProbabilityFiber.lean` | `a45dce29e27a5be358579ce09fdaf6db37f5ed060ad4572f3640fea9a94ca395` |
| `RefinedUpperSnapshotLarge.lean` | `0c355fe05f5c266ce5885d97ebea0b7fe6bc48089657d07ebcf659f7789fb935` |
| `RefinedUpperSnapshotProtocolCost.lean` | `4f8427ca441d43f2239a108f8470825ba4296a2c2e7febf31cdb8ea754fcd8cb` |
| `RefinedUpperShrinkParameters.lean` | `1e1003d8fa697fbb51f668600a101d020daeca7cdaee31c84d0c53f6418f19ce` |
| `RefinedUpperShrinkPrecision.lean` | `51aeb124a963ef0af4ba825e4c1136c5e45b62409a5bb565b2d07ad0d51058a8` |
| `RefinedUpperShrinkTrial.lean` | `b5d9b81fed91e0359bf5b3f6ee2088ea6cf851e62e8cc34ce126b9c1e808334c` |
| `RefinedUpperShrinkRestart.lean` | `467dd454fbf5f27180509e3ed7195859d63aef75cf8882206142fcbf86ced7cf` |
| `RefinedUpperShrinkCorrectness.lean` | `0038269769715440e90d1c2c9334918ebeae5a932ad1f9f52809d7517dea8ee2` |
| `RefinedUpperShrinkProtocol.lean` | `bd7b9299d098c4e792a3a6ed959fe544e2209cfd2262f62857bdfc5f74bcc374` |
| `RefinedUpperShrinkRepair.lean` | `eb997296401425df660ab7bb248b556200cf49432a943d3e9ac584ca354ecd7d` |
