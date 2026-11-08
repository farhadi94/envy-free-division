# Independent review of the randomized upper formalization

Date: 2026-11-08 UTC. Reviewer: `upper_independent_review`, a fresh agent.
Scope: the concrete Repair endpoint, its oracle/history/probability adapters,
and the interface to the unfinished global construction. This is a read-only
source/correspondence review. I did not run a fresh kernel rebuild; the separate
`repair_audit` worker owns that check. Reviewed source hashes are in
`upper_resume_independent_review_sources.json`. No Lean or manuscript source
was changed by this review.

## Conclusion

I found no concrete mathematical contradiction or circular target assumption
in the inspected Repair endpoint chain. It supports a finite actual ordinary
query primitive with unconditional original-tape failure probability below
1/64, every-attempt query caps, legal queries on rejecting as well as accepting
branches, and physically valid accepting outputs. This does **not** certify
the complete randomized upper theorem. Its remaining construction and
probability obligations are substantial and explicitly separate below.

The stronger two-sided reserve guard is already in the manuscript. The
formalization's earlier weaker guard was an incomplete implementation of that
interface, not evidence that the manuscript required a new rejection term.

## Checked local correspondence

All Lean paths below are relative to `verification/lean/EnvyFreeResearch/`.
The manuscript reference is canonical `paper/sections/upper_proof.tex` in
`research/submission_focused`.

1. **Actual finite program and all-attempt cost.**
   `Full/UpperRepair.lean:48` (`program_cost`) constructs an execution of the
   actual query program, with final history equal to prior history appended
   with its entire trace. It bounds that trace by `6*n*fine n` queries and
   `3*fine n` Cuts. There is no success premise. The underlying
   `UpperRepairTrialFull.program_cost` and `UpperRepairProgram.program_cost`
   preserve the trace through the cached final guard and physical output
   postprocessing. This matches the manuscript's accounting of rejected
   correction trials at lines 635–640. It is not a cost statement about only
   the surviving allocation or only the retained cache.

2. **Every attempted request is legal.**
   `Full/UpperRepairLegality.lean:29` (`all_attempts`) has no success or Borel
   premise. `UpperRepairHistory.final_history_truthful` at line 41 explicitly
   covers preparation rejection and correction/rollback paths. Truthful means
   every entry in the full history, not merely entries referenced by final
   cache cells (`UpperEndpointCache.lean:25`). The comparison policy in
   `UpperQueryLegality.lean` agrees with the real policy on legal requests and
   supplies an invalid answer on illegal requests. For Eval, the cumulative
   difference plus one fails `ValidReply` even when endpoint geometry is bad;
   for Cut, `right+1` violates the endpoint bound. Universal truthfulness under
   this admissible comparison policy forces legality. `truthful_replay` at
   line 45 then transfers the entire execution to the original policy.
   This avoids the invalid inference that a correct retained cache alone
   proves legality of discarded queries.

3. **Genuine Option-valued oracle, including prior history.**
   `UpperRepairLegality.option_run` at line 65 uses the actual oracle with
   `origin.history ++ localHistory` and a finite fuel bound. The default-value
   adapter is not being used to answer an illegal request: legality plus
   `option_replay` yields an execution with genuine replies. Starting the
   subprogram with an empty local history does not erase the enclosing
   history from the oracle's input.

4. **One original-law probability statement.**
   `UpperRepair.failure_lt` at line 100 invokes the configured full trial
   probability, not a law conditioned on a good sampled grid.
   `UpperRepairTrialLaw.lean` defines a product law carrying sampled owners
   and value targets, reserve labels, isolation randomness, and fresh
   correction-circle starts. Its `original_samples_law` at line 47 derives
   the iid *point projection* from actual sequential sampling. It does not
   declare complete adaptive query histories independent.
   `UpperRepairTrialFullProbability.original_population_failure_lt` at
   line 88 instantiates all numerical allowances from original-population
   parameters, `k >= 2`, and injectivity into the original population.
   Neither the advertised failure bound nor successful correction execution
   is a premise of this endpoint.

5. **Both reserve tails share one exception.**
   `UpperSnapshotCandidatesGuardProbability.snapshotGuard_fiber_probability`
   at line 22 defines bad mass as the union of the lower and upper tails and
   charges the pre-existing two-sided mass estimate once. The count and
   selected-parent exceptions are added separately. Its product theorem at
   line 82 integrates this fixed-draw estimate before conditioning on guard
   success. The full trial union also charges isolation and correction
   failure. This matches the manuscript's `[q/2,3q/2]` check at lines 338–347
   and five grouped budgets at lines 619–635.
   The Lean implementation defers the cached upper-tail check until after
   the attempted trial. That can perform additional work on a doomed trial,
   but its worst-case cap and failure-set union explicitly cover that order;
   it does not invalidate the guarantee.

6. **Physical successful output.**
   `UpperRepairSuccess.SuccessFacts` at line 24 includes well-formed recorded
   allocations/residue, literal pairwise disjointness, exact material union,
   residue containment, more than three quarters of every active buffer mass,
   exact cake/chore EF, and a common full history. `success_facts` at line 72
   derives these from the actual accepted branch and elementary input
   invariants. In particular, the output EF and full partition are conclusions.
   The old states must be pairwise disjoint and disjoint from the buffer;
   their histories must already be available in the enclosing history.
   Those are appropriate caller obligations, not circular EF hypotheses.
   The input `Near` is precisely a raw buffer-normalized additive envy bound,
   with the correct sign reversal for chores.

7. **Measurability has the right scope.**
   The probability endpoint requires a jointly measurable full-history policy,
   consistently with manuscript theorem lines 16–19. The pathwise execution
   endpoint does not. `UpperRepairOutputMeasurable.execute_measurable` at
   line 73 handles varying recorded inputs and fresh tape. The actual query
   program has a certified measurable next-action theorem as well. No new
   leftmost-root restriction is introduced. These statements do not on their
   own complete the infinite adapted retry/global stopping argument.

## Integration findings and required follow-through

These are incomplete proof interfaces or obligations, **not demonstrated
errors in the manuscript**.

| Priority | Finding | Required discharge |
|---|---|---|
| High | The global table theorem is conditional on completed concrete events and a terminal allocation. | Construct those events from the actual physical programs, and prove the returned terminal allocation and its residue partition. |
| High | A uniform bound for each fixed past history is not yet the formal global adapted retry theorem. | Use joint measurability and fresh conditional tape laws to obtain a.s. completion and charge all rejected attempts, without claiming independent adaptive outcomes. |
| High | Repair requires strictly positive active buffer rows. | Implement zero-row/small-population handling and prove it preserves frozen-observer comparisons, material, caches, and costs. |
| Medium | `SuccessFacts` does not export the whole-old-bundle permutation/additions decomposition required by global transport. | Derive and export it from the actual assignment/package construction; do not infer it from EF and conservation alone. |
| Medium | The current actual Repair-to-Snapshot margin adapter still takes a candidate baseline contrast premise. | Derive that premise from each actual accepted candidate and a measurable pre-seed selection before calling Snapshot complete. |

The relevant exact references are:

- `GlobalCompletion.lean:229`, `ConcreteStep`, includes physical-result
  numerical data such as `snapshot_EF`, `shrink_EF`, `final_EF`, partitions,
  spending, and `repaired_identity`. These are valid local certificates when
  supplied by actual program theorems. They are not the construction of those
  physical programs.
- `GlobalCompletion.lean:629`, `no_infinite_completed_events`, rules out an
  infinite sequence of completed events. Its comment correctly distinguishes
  a single request that fails to return. It is not alone an a.s. termination
  theorem for the randomized oracle algorithm.
- `GlobalCompletion.lean:836`, `finite_global_completion`, assumes the finite
  event run and terminal active EF/full-residue allocation. Its scope is
  honestly documented; substituting it for the main theorem would be an
  overclaim.
- `Full/UpperRepairAllocation.lean:29`, `allocation_domain`, and
  `Full/UpperRepairPackages.lean:73`, `packages_domain`, supply the underlying
  whole-bundle construction. The actual maximizing/minimizing assignment is
  a permutation. This is the correct source for the missing exported
  transport interface. The global worker has been notified.
- `Full/UpperRepairSnapshotProbability.lean:54`, `original_trial_margin`,
  assumes measurable `chosen`, positive `Lambda`, and `hbaseline` on successful
  trials. Joining, reserve bounds and rejection probability are derived;
  the candidate contrast still needs its own actual construction proof.

## Limits of this review

I inspected the public endpoint chain and its key implementation/probability
adapters. I did not independently re-prove every interpolation or assignment
isolation lemma in the transitive closure, nor re-run the kernel audit.
No manuscript correction is justified by the two-sided-guard or legality
issues inspected here. Full-paper or main-upper-bound certification should
wait for the remaining physical construction, global probability/accounting,
and a final independent correspondence review of the completed theorem.
