# Independent deterministic-chore correspondence review

Review date: 2026-11-08 UTC. This was a read-only mathematical/source review, not a new compiler or axiom audit. No Lean source, configuration, or manuscript was changed. The review covers the previously compiled root grouping modules and `ChoresTerminalScan`, with their local prerequisites and the corresponding canonical `paper/sections/chore_proof.tex`. Concurrent new integration modules are outside this snapshot.

## Conclusion

I found **no demonstrated mathematical error** in the reviewed local results. I also found no circular use of the final chore theorem in these modules. This is **not certification of the main upper bound**: the concrete outer driver, terminal physical join, actual global call ledger, and native population-step instantiation are still necessary. Most risks below are outstanding proof obligations, not counterexamples to the manuscript.

## Findings and required closure

### High priority — complete-state transition and end-to-end driver remain unproved

`ChoresOuterBatchProgram.batch_executes` (line 49) proves execution of each cohort at its actual accumulated query history, correctness of its returned local package, and a sum of per-group Q/C bounds. It does not itself construct a new committed `Outer.Data`, prove its fifteen-field `Good`, or prove exact global physical coverage.

The theorem deliberately accepts an arbitrary list of cohorts; overlap is possible for that interface. Physical simultaneous commitment must use actual `cohorts` or an equivalent flattened-root disjointness proof. `ChoresOuterBatchSlots.actual_slots_distinct` supplies this from `outputs.map GroupResult.group = cohorts`. `group_result_ids` retains the input package roots, including frozen ancestors, but global package permutation still has to join these local identities with old closed packages and actual leftovers.

**Important integration constraint:** `Cohort.state` is a locally filtered copy whose `closed` list includes every excluded old package. These temporary local closed lists must not be summed across groups. Only the actual group output packages, the original global closed pool, and the actual old-pool leftovers belong in the global commit. The batch-commit owner acknowledged this constraint and reports that its new constructor follows it; that new code is outside this review snapshot.

The immutable original-piece disjoint geometry must also be carried externally: `Data.Good` has correct root IDs and cached values, but does not by itself assert global disjointness of all original piece sets. Distinct IDs alone are not a geometric disjointness theorem.

### High priority — actual terminal physical allocation and whole-residue margins remain to be assembled

`ChoresTerminalScan.scan_common` (line 51) derives owner membership, participant containment/properness, nonnegative participant whole affine values, and protection of omitted observers from actual classified scans and clearance. Its explicit `hprotected` condition is used correctly: exhausted properness for a full component requires the protected cutter to be omitted; a proper component already suffices. The final scheduler must derive this condition while retaining the distinguished representative.

`scan_atomic_bounds` (line 109) proves a nonempty proper large mask, a real large atom inside the offered suffix, and outside-mask smallness. These facts alone do not prove that an actual affine assignment keeps a whole offered parent or that extracted material is disjoint from the base allocation. Those need the actual closed-program result and its whole-parent witness, including zero-credit affine assignments.

`scan_exhausted_bounds` (line 92) proves a per-root positive deviation. The manuscript's exhausted exit needs the aggregate positive-surplus inequality over **every ancestor and every closed/rejected package**. A single-root deviation cannot simply be renamed the entire allocation's envy margin.

Atomic residue accounting must remove the actual extracted X before applying the small-residue bound. An affine terminal suffix can be large to agents in the large mask, so the open-group theorem bounding the entire complement cannot be reused unchanged at that terminal step. These obligations are acknowledged in the implementation handoffs and were sent to the terminal owner.

### Medium priority — the compiled local query bound differs from the manuscript's sharp auxiliary bound

The manuscript operation table (roughly lines 246–252), masked-parent lemma (around lines 350–365), and final nonrecursive ledger (around lines 917–934) use `n*S_k`, where `S_k = 2^(k+1)-2*k-2`, for each compensation call.

The actual compiled executor uses:

```
ComponentRecording.budget n k
  = n*(2*n+1)*SubCore.sourceBudget k + n*k
```

This identity is `ChoresComponentRecordedSubCore.budget_eq` (line 55), and this larger bound is exactly what `cohort_executes` and `batch_executes` conclude. It includes generic physical-interpreter overhead and final endpoint recording. Snapshot execution also uses its actual recorded-domain budget rather than treating a disconnected domain as one free interval.

This discrepancy does **not** show that the manuscript's sharper implementation is impossible or incorrect: a larger proved upper bound is not a lower-bound counterexample. It does mean the present artifact does not certify the manuscript's `n*S_k` auxiliary statement or its displayed exact `F_n` ledger. To claim full correspondence, either formalize the more efficient implementation, or explicitly distinguish the verified implementation and prove the same headline bounds using its larger actual ledger. `BudgetLocal`, `PopulationCapacity`, and `BudgetGlobal` already pursue the second route; final actual driver counts and the leading-coefficient asymptotic still need completion. Do not replace the larger proved budget by `n*S_k` in the final theorem without a separate proof.

### Medium priority — private complement caching is a computational invariant, not a consequence of a subset bound

`ChoresOuterData.Data.Good` (lines 71–89) stores truthful retained caches, their inclusion in original pieces, and numerical complement bounds. It does not store a truthful finite cache of the entire complementary domain. A set-level inclusion or numerical bound does not provide its observer costs for free.

The planned independent persistent private-cache map is the appropriate implementation bridge. Its initial empty complement, original equalizer suffixes, and donor `proposalResidueCache` can be obtained from actual recorded data. Every filter, reveal, batch patch and terminal exit must preserve this map. This is a missing formal interface, not a flaw in the manuscript, which explicitly retains actual suffixes and exact private complements.

### High priority for certification — the population theorem is still an induction kernel

`ChoresComponentPopulationCoordinates.recursive_complete_specification` (lines 142–147) explicitly assumes `hstep`, a complete local scheduler contract with actual execution, physical output, cost, and coordinate provenance. `recursiveProgram` does use real strong recursion on smaller populations, and wrappers charge `Q_child+n*C_child`; however, these facts do not discharge `hstep`.

The scalar `BudgetGlobal.total_with_initial_evals` proves a numerical recurrence envelope, not that the current unfinished scheduler executes within that recurrence. There is no circular proof in the audited statement: its limitation is explicit. A final artifact must exhibit one concrete `step`, prove its local contract from actual preprocessing, scheduling and terminal programs, instantiate all proper child populations, and only then derive the main theorem.

## Positive checks

- **Full histories:** `batchProgram` sequences calls with `bind`, and the inductive proof invokes the tail at `prior ++ t₁`. It accounts for both trace lengths and Cut counts through concatenation. It does not assume history-independent Cut choices.
- **Old-pool semantics:** each cohort program reads the same immutable old `data`; the batch accumulates query history, not mutations of that state. Output reentry is absent by construction.
- **Restriction and frames:** `restrictCycle` keeps the same cycle vertices and derives its follows condition from `restrict_outgoing`; `restrict_selected`, `restrict_nextAgent`, and `restrict_advance` preserve the actual recorded choices. `GroupResult.live_frame` identifies the local survivor with the common global advance.
- **Root provenance:** `active_ids_distinct` is derived from the exact global root permutation, `source_injective` follows from actual live frames, and `group_result_ids` derives preservation from real compensation correctness rather than assuming it. `actual_slots_distinct` and `batch_survivors_distinct` correctly require genuine group disjointness.
- **Whole-complement control:** `proposal_complement_small` splits executed/unchanged proposals. For an executed donor label it bounds `P \\ (P \\ removed)` by `removed`; other labels use allowed equalizers. It bounds the entire resulting complement rather than just newly removed material. `ordinary_complement_small` derives removed-set smallness from actual suffix containment and the scan. `patched_complement_small` handles untouched frozen roots through the old invariant.
- **Terminal branch distinction:** the scan lemmas keep participant and large masks distinct. They do not silently promote clipped zero utility to a retained whole physical suffix. Exhausted properness is explicit rather than inferred from nonemptiness.
- **No unnecessary computational criticism:** standard Lean axioms, noncomputable finite choice, and zero-cost finite combinatorial computation are consistent with the stated query model. Their presence alone is not a proof gap.

## Limits of review

I did not independently rebuild the full closure, redo the previously audited continuous Core/fixed-point construction, or certify the unfinished new batch/terminal/driver modules. This review is not an independent review of a completed main theorem. It found correspondence and integration obligations, not a counterexample to either headline chore bound.

## Reviewed grouping/terminal source hashes

The following hashes identify the stable compiled grouping/terminal snapshot inspected here, rather than concurrently changing integration files.

- `ChoresOuterGroupRestriction.lean`: `b75dff14bcbaf5b56aec27a6e129c59402b9aa39fc4b62cae937ef75b52daf41`
- `ChoresOuterCohorts.lean`: `25629e50659bb14bfcfb70b916c07510805cba6d16d5a40d4e145c8b09f135d2`
- `ChoresOuterGroupProgram.lean`: `798b83628853b29fbdc165d654d9f88391bb43b9ff9c10f82f3dda8314eca912`
- `ChoresOuterBatchProgram.lean`: `b234a89590426cf6d26b4c5e5b701db6ef77678bf2204642d072ce45453b710e`
- `ChoresOuterGroupFrames.lean`: `50d5dbcaa83cfd034393d9042b258fa552af55b22c89743ed4d33a6b50e6f70c`
- `ChoresOuterBatchSlots.lean`: `2bf46ab5b8388eb68adb47e74645d2e9412d0481c7021833472f984ac5a8f683`
- `ChoresOuterGroupIds.lean`: `0fa151f9269d61f2f409fff243113f76b8f00cbdc269fc696b2c5b9ee86aaaab`
- `ChoresTerminalScan.lean`: `7d775b33c9997262a42169354855fe897e9791ce9cdfe89353b35d29ee2129bf`
- `ChoresOuterComplement.lean`: `b03903f9a69945537ec97d1a83b30e3f7f22a355a8c2872f136b8044342e0db5`
- `ChoresOuterNextCache.lean`: `4e6c043b7954366905a8f5362872dedc4ad81ad6c457a0556e11c1296a726194`
- `ChoresOuterData.lean`: `f29a9c42cf834f1dfb41c8c3cf8c5f8abd0f755146913b62ab9f9ec1e880cc3c`
- `ChoresComponentRecordedSubCore.lean`: `a0477deb1739e4ecb975bdbb4045d9c4e374f2df1fbbe5ba42d6b1bd0967151d`
- `ChoresComponentPopulationCoordinates.lean`: `240ad7c6f8d293e0d73bf22a74ac94a8f987604ab248f9588e1cfdfc77545734`
