# Fresh independent deterministic-chore review

Status: **PASS — exact final main theorem passes independent source and manuscript-correspondence review.** The frozen transitive import-closure/axiom audit is a separate release gate owned by root and was still pending at this review. No source/model blocker remains in the inspected main integration.

Reviewer: fresh `chore_main_review` agent, independent of the implementations reviewed here. The only authored artifact is this report. No Lean source/configuration edits or builds were performed. Root confirmed the targeted pinned Lean 4.35 build of `ChoresMain.lean` exited 0; its log is empty. I inspected the exact final theorem and the newly completed local physical/coordinate assembly. This replaces the earlier provisional report that withheld main certification while integration was open.

## Exact final theorem and assumptions

Reviewed endpoint: `EnvyFreeResearch.Full.Chores.Main.deterministic_chores` in `verification/lean/EnvyFreeResearch/Full/ChoresMain.lean`.

Its only assumptions are `n >= 3`, `Population.Costs n` (finite nonnegative atomless measures), an ordinary full-history `AdaptiveOracle.Policy`, and that policy's legality. There is no supplied valuation cache, future transition-success hypothesis, final-state invariant, EF hypothesis, local-step specification, arbitrary program, recursive correctness contract, or unproved budget premise. The returned execution is of the actual cost-independent `Main.program n` and begins at empty history.

The theorem concludes a bounded actual `AdaptiveOracle.run` returning a finite encoded allocation, complete pairwise-disjoint coverage of `[0,1]`, exact chore EF, measurable shares, all interval endpoints within `[0,1]`, inherited-or-Cut output endpoint provenance, query scope starting from `{0,1}`, and legal queries/correct replies throughout. The finite-union-of-intervals property is carried by `UnitEntry.Output`'s finite lists and `Output.share`; `UnitEntry.finite_interval_output` exposes it explicitly, including the uniquely owned singleton `{0}`. It is not merely a numerical EF table or an active-cohort-only allocation.

`Main.native_complete` instantiates `Population.recursive_complete_specification` with **actual** `Outer.concreteStep` and **proved** `Outer.concrete_step_complete`. The latter uses only the smaller-population IH, combines `large_program_correct` with `large_program_known`, and handles singleton/pair base cases using their complete specifications. This closes the previously open circularity/integration concern.

## Final integration inspected

* `ChoresOuterLocalTerminalCorrect.lean`, `finish_terminal_correct`: derives the cohort from the actual terminal choice; preserves all unselected roots by `cohort_good`; obtains the actual terminal compensation result via `terminal_executes`; derives the protection/properness facts; and runs `finish_class_correct` at `prior ++ terminalTrace`. The private-cache complement remains exact through cohort filtering.
* `ChoresOuterLocalFinish.lean`, `prepared_finish_correct`: derives original snapshot soundness, geometric separation, exact final-residue cache, full-root bound, and every scale inequality from the actual preprocessing result and named parameters. It concludes Sound on the complete mutable preprocessing domain.
* `ChoresOuterLocalContinue.lean`, `continue_prepared_correct`: executes the concrete driver, passes its returned invariant to completion at `prior ++ driverTrace`, then applies `preprocessing_attach_sound` to the actual `(batchAllocation out.clearance).join inner` return. Both full trace costs include the terminal and recursively wrapped child execution.
* `ChoresOuterLocalLarge.lean`, `large_program_correct`: binds the actual preprocessing trace and continuation trace, rules out `.failed` using the proved preprocessing result, and covers the complete zero-residue exit. No branch returns an empty allocation under the legal input hypotheses.
* `ChoresOuterDriverBoundaryLarge.lean`, `large_program_known`, and `ChoresOuterDriverBoundaryContinue.lean`, `continue_prepared_known`: synchronize their analyzed execution with the physical execution by determinism of `Executes`; preserve both clearance endpoints and private-cache endpoints; and use exactly the actual accumulated histories.
* `ChoresOuterDriverBoundaryUnit.lean`, `unit_program_known`: starts with only 0 and 1, incorporates the paid initial Eval trace, and applies the parametric native coordinate specification. `Main.deterministic_chores` invokes this theorem for the same returned execution used in its physical and query conclusions.

## Final budgets and manuscript qualification

`Main.bound n = min (n^(3*n) * 2^(27*n)) (2^(14*weight n))`, with `weight n = n * (Nat.clog 2 n + 1)`. `Main.capacity_bound` independently proves the complete query capacity, including n initial whole-interval Evals, is at most **both** quantities before taking their minimum. The actual successful trace length is bounded by that capacity. C is then bounded by the same minimum through `virtualCuts trace <= trace.length`; this is sound even though the proof does not use the sharper separate C capacity at its final step. Thus neither component of the minimum is being inferred from the other.

This establishes the advertised leading exponent `3n log₂ n + O(n)` and the explicit `2^(14n(ceil(log₂ n)+1))` envelope. It does **not** establish literal equality of the formal protocol's auxiliary ledger with manuscript equation `(r8c:node-query)` (`F_n`) or the stated cached `B_SC`. `ChoresComponentBudgetLocal.lean` deliberately budgets actual `Snapshot.queryBudget` and `ComponentRecording.budget`, including generic interpreter and observer recording overhead, proves `localQueries <= 5*n*referenceBudget` and `localCuts <= 2*referenceBudget`, and absorbs these polynomial overheads plus ambient recursion recording. The formal clearance length is a sufficient fixed `14*n*weight n`, whereas the manuscript defines the least sufficient integer. These are conservative implementation refinements; the same main asymptotic and explicit envelope are proved. A publication claim that every sharper manuscript intermediate ledger was formalized verbatim would overstate this review.

## Manuscript/model correspondence

Compared against canonical `sections/model.tex`, `sections/general_results.tex` (`thm:deterministic-chores`), and the scheduler/completion portion of `sections/chore_proof.tex`.

* `ChoresComponentPopulationProgram.lean`, `Population.Costs`, assumes finite nonnegative measures on real Borel sets and `NullSingletonClass`; it does not assume positive totals, a density, common support, or normalization. On the real Borel space this is the intended finite atomless measure setting. A manuscript measure on [0,1] can be regarded as zero-extended; the inspected public interface itself takes a measure on ℝ.
* `ChoresMainProtocol.lean`, `Main.nativeProgram`/`Main.program`, and `ChoresOuterLocalProgram.lean`, `Outer.concreteStep`, are independent of `Costs` and receive only population, cache, and oracle replies. Finite choice/tie-breaking in this noncomputable exact-real presentation does not give the program a measure oracle outside Eval/Cut.
* `AdaptiveOracle.lean`, `IsLegalPolicy`, universally quantifies the entire finite history. `driver_executes`, `terminal_physical_executes`, and the population specifications quantify any such policy and any prior history. Repeated legal Cuts may return different roots; no leftmost/rightmost root restriction appears in these statements.
* Q is the actual answered trace length, C is its Cut-query count. For successful `Executes`, every attempted call is answered; `UnitEntry.execution_legal` gives legality and reply correctness for each such call. Thus there is no successful-run uncharged failed attempt in these statements.

## Termination and noncircularity

`ChoresOuterDriverCorrect.lean`, `Outer.driver_executes`, is an induction on the actual fuel argument of `driverProgram`. The fuel-zero case is impossible from rank, outside commits strictly reduce rank, and merge commits strictly reduce rank. The proof obtains actual `batch_executes` outputs and proves the updated full invariant using `commit_batch_good`; it does not assume future transitions succeed. Its result remains a terminal entrance before final cohort filtering, exactly as the handoff states.

`ChoresOuterBatchGood.lean`, `Outer.commit_batch_good`, takes old `Data.Good`, immutable snapshot/clearance hypotheses, actual output `GroupResult.Correct`, and exact output-cohort correspondence. Its conclusion is the new full `Data.Good`. The correctness premise here is discharged by the actual `batch_executes` used in `driver_executes`; it is not the target new-state invariant.

`ChoresTerminalPhysicalProgram.lean`, `Terminal.terminal_physical_executes`, derives actual compensation execution, PartsCorrect, PhysicalCorrect, the whole-offered-suffix witness, and physical EF of the retained full pool. It assumes initial/cohort invariants, not successful compensation or desired terminal EF. Atomic/exhausted completion lemmas subsequently consume these produced facts.

`ChoresComponentPopulationProgram.lean`, `ChildPrograms`/`recursiveProgram`, explicitly permit only positive k < n and use `Nat.strongRecOn`. `ChoresComponentPopulationCoordinates.lean`, `recursive_complete_specification`, applies the induction hypothesis to `Costs.pullback agent` at that strictly smaller population. The arbitrary child-specification premise of the local theorem is a legitimate induction interface. The final `Main.native_complete` supplies the concrete step and no such premise survives in `Main.deterministic_chores`.

## Whole-root and clearance accounting

`ChoresOuterBatchCommit.lean`, `commitBatch`, closes old closed packages and actual leftover packages once and installs actual group outputs. It does not concatenate the temporary closed pools of individual filtered cohorts.

`ChoresOuterBatchCommitIds.lean`, `commit_batch_ids_perm`, uses the literal old-pool batches/leftovers partition and group package ID permutations to preserve the entire old root-ID list, including frozen ancestors. `ChoresOuterBatchGoodPackages.lean`, `commit_batch_all_ids`, derives the needed group-ID claims from physical group outputs. This rules out both omitted ancestors and duplication at the global commit interface.

`ChoresTerminalPhysical.lean`, `Terminal.full_allocation_sound`, assembles `finalPool`, includes every old closed package, and concludes Sound on the union of updated caches over **all RootId**, not merely active cohort indices. `ChoresTerminalResidue.lean`, `residue_partition`, makes that retained union disjoint from literal R0 plus every updated private complement, and proves their union is R0 plus every original root piece.

`ChoresTerminalExtractionMarked.lean`, `marked_private_eq_extracted`, equates the actual donor slots with the actual suffix union, including affine-zero assignments. `ChoresOuterLocalTerminalGeometry.lean`, `atomic_domain_partition`, and `finish_atomic_class_correct` use this equality to remove extracted material once before recursive completion. `ChoresTerminalAggregateFullMargin.lean`, `actual_exhausted_full_margin`, compares against literal R0 plus the entire private cache union, including frozen ancestors; `finish_exhausted_class_correct` uses precisely that residue and full-allocation cost difference.

The additional clearance snapshots are kept separate from the immutable original root table: `ChoresOuterPreprocessingGeometry.lean`, `preprocessing_partition`, `preprocessing_disjoint`, and `preprocessing_attach_sound`, prove the fixed clearance domain and complete mutable domain partition the original input. `Outer.continuePrepared` already returns `(batchAllocation out.clearance).join result`; `continue_prepared_correct` now applies the attach theorem to that exact return. The zero-residue exit is independently accounted for by `prepare_finish_sound` and `preprocessing_zero_sound`, which join all original plus clearance snapshots and give the final null residue to a zero-cost owner.

## Actual ledgers and asymptotics

`Outer.driver_executes` telescopes actual executed group traces to `(entrance.size - returned.size) * budget`, with history `prior ++ first` passed to the tail. Its merge charge is `outputs.length + updated.size <= old.size`. Actual terminal cost is one `ComponentRecording.budget n participants` call, monotone to the n-participant allowance.

`ChoresOuterLocalBudgetLedger.lean`, `selected_terminal_charge`, charges this terminal call against the positive remaining pool; `local_query_ledger_of_bounds` and `local_cut_ledger_of_bounds` add preprocessing, driver, terminal, and completion/child allowances separately. `continue_prepared_correct` and `large_program_correct` now supply the actual phase traces to these scalar adapters.

`ChoresComponentPopulationCapacity.lean`, `capacityStep`, takes a maximum over either one proper child or two positive children summing to n. Child query cost is Q_child + n*C_child, and Cut cost is C_child; Q_child is not multiplied by n. The wrap proof actually invokes the ambient endpoint recorder, and `Boundary.record_correct` charges n Evals per fresh Cut-created endpoint. The capacity envelope uses at most 2n-1 nodes and an n² ancestor-recording allowance.

`ChoresComponentBudgetAsymptoticGlobal.lean`, `total_capacity_leading_exponent`, proves both `n + totalCapacity.queries` and `totalCapacity.cuts` at most `n^(3*n) * 2^(27*n)` for n >= 3. The leading exponent agrees with the manuscript's 3n log₂ n + O(n). `Main.capacity_bound` now applies this scalar bound to the actual full protocol execution obtained by `UnitEntry.program_correct`.

## Endpoint ownership and coordinate provenance

`ChoresMainUnitAllocation.lean`, `Output.share`, assigns {0} to exactly one explicit `zeroOwner`. `share_disjoint`, `share_cover`, and `share_envy_free` derive a literal complete partition of Icc 0 1 from the Ioc native allocation, using atomlessness only for the singleton's value. `finite_interval_output` exposes the finite union of Ioc pieces plus that singleton, and `interval_bounds` proves endpoints lie in [0,1]. No uncovered zero endpoint or duplicated endpoint owner remains in this adapter.

`ChoresMainUnitLedger.lean`, `program_ledger`, proves exactly n initial Eval calls, no initial Cuts, and no endpoint-ownership calls. `ChoresMainUnitProgram.lean`, `unit_complete_protocol`, turns successful execution into the bounded `AdaptiveOracle.run` result, with complete partition, exact chore inequality, finite encoded pieces, interval bounds, and per-query legality; `Main.native_complete` now discharges the native specification for this exact public program.

`Boundary.Known` includes only inherited points or actual Cut replies, and `Boundary.Scoped` checks bounds at each trace prefix. `Outer.driver_known` threads both retained and private caches through actual batch/outside traces. The stronger `Population.CoordinateSpec` is needed because mere alignment in a disconnected child's gaps would permit free coordinates; `wrap_coordinates` correctly preserves the explicit parent point set. `Outer.concrete_step_complete` now joins the physical proof and `large_program_known` into the concrete local CompleteSpec, and `Main.deterministic_chores` exports the `{0,1}`-based conclusion.

## Verification scope

Read all requested handoffs (local-budget actual filename: `chore_local_budget_handoff.md`) and the relevant canonical manuscript sections. The previously inspected scheduler (10 modules), batch (11), local-budget (4), unit-entry (3), local-base (4), and path-keyed asymptotic source hashes matched their recorded status. The final local endpoint's scoped axiom log lists only `propext`, `Classical.choice`, and `Quot.sound` for `concrete_step_complete`, `large_program_correct`, `continue_prepared_correct`, and `prepared_finish_correct`. Root confirmed final main targeted compile exit 0. No cold build was launched by this reviewer.

The earlier direct scan found no `sorry`, `admit`, custom `axiom`, `implemented_by`, `unsafe`, or `native_decide` in Main/OuterLocal/OuterDriver/OuterBatchGood/Terminal. The final integration was scanned again with the same result. This source review does not replace the frozen full import-closure and declaration-axiom audit. Root should retain that as the remaining verification gate before release. No substantive proof or model bug was found in this independent review.

Reviewed final source hashes:

* `ChoresMain.lean`: `77308913ad573637030e33e473d8a6ffee115563bfb70999aefc2ba6274b1767`
* `ChoresMainProtocol.lean`: `a49c7323145dc0982bf74b75e0a1a94ad66ace80c5ccd3ef83408ac9b454a3f7`
* `ChoresOuterLocalComplete.lean`: `305a0577f38e2a6b8cb17dd59a80123b2e6072b0daf968c2ba14e4051b729165`
* `ChoresOuterLocalContinue.lean`: `421cbb887ad3a92569513652d9e8cacc563cf8a16b42e94d55ef034e74646b59`
* `ChoresOuterLocalLarge.lean`: `82d086fcd0daf34992cbbc271316c283448afcb065a673f2b3adc9e245ca1ace`
* `ChoresOuterLocalTerminalCorrect.lean`: `73b73e4971bea5f984b132635bc622801d05143328b3fb7113c54b4f60c2abb3`
* `ChoresOuterDriverBoundaryLarge.lean`: `ca9be36e6ddd7163a700baee56243ee1a1959054065e5ef1b2fd185c5b4cb704`
* `ChoresOuterDriverBoundaryUnit.lean`: `e6aa868c9d00cda11c39f489b9e05200a5eb6c69560f5c41de000549a43e4944`

Final review recorded UTC: 2026-11-08T02:20:46.804609+00:00
