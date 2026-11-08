# Concrete finite chore transition formalization

Author: `signed_impossibility`. File owned for this audit:
`verification/lean/EnvyFreeResearch/ChoreComposition.lean`.
The module uses the pinned Lean 4.35.0 / mathlib environment and imports the already audited `R7Chores` and `R8Chores` modules. No inherited source, umbrella import, `AxiomAudit.lean`, coverage file, or global verification script was edited by this author.

## What is now formalized

The new module defines actual finite cost-table states and transformations. It does not merely assume that an invariant remains true.

`Allocation` stores an original root ID, its baseline row, a permutation from labels to recipients, and the actual prefix-cost table. The credit and deficit entries are defined by

```
credit(a,i,p) = 1_{owner(p)=i} (baseline(i)-cost(i,p)),
debit(a,i,j,p) = 1_{owner(p)=j} max(0,baseline(i)-cost(i,p)).
```

`Frame` stores a live root's allowed and forbidden recipients, the original equalizer-cost table, frontier gap, and current permutation. Its reserve is the literal three-case formula `r8c:reserve`. `Frame.Good` checks that every currently executed edge is allowed and that every allowed recipient equalizer has its recipient's baseline cost. A `Package` contains a list of actual frozen allocations and at most one live frame. Its `credit` and `debit` are sums of the actual frozen entries; its reserve is the live frame's reserve or zero when closed. `Package.Valid` contains the live-frame condition, nonnegative actual frozen credits, and `D+H <= L` for distinct observer/recipient pairs.

| Paper obligation | Concrete Lean definitions and principal theorems |
|---|---|
| `r8c:state`, actual delta/lambda and `r8c:reserve` | `Allocation.credit`, `Allocation.debit`, `Frame.reserve`, `Package.credit`, `Package.debit`, `Package.reserve` |
| Reset along an allowed matching | `Frame.reset`, `Package.reset`, `reset_good`, `frame_credit_zero`, `frame_debit_le_reserve`, `package_reset_valid` |
| Closure consumes the actual live deficit and creates no credit | `Package.close`, `package_close_credit`, `package_close_debit_bound`, `package_close_valid` |
| One modified donor label, actual complementary-prefix cost | `Proposal.output`, `proposal_credit`, `proposal_debit_bound` |
| Ordinary positive-only execution and unchanged zero proposals | `ordinaryProposal`, `ordinary_nonpositive_is_unchanged`, `proposal_zero_is_unchanged` |
| Affine execution including own-zero assignments | `affineProposal`, `affine_proposal_good`, `affine_component_payment` |
| `r8c:group-update`, actual selected donor sums | `Donation.frozen`, `donation_credit`, `donation_debit_bound`, `mergeOpen`, `merge_open_credit`, `merge_open_debit_bound` |
| Unique tasks identify the actual sums in `r8c:payments` | `ordinaryTasks`, `ordinary_tasks_payments`, `ordinary_tasks_extras` |
| `r8c:exclusive-payment` | `ordinary_component_cases`, `protected_component_zero`, `ExclusivePayment`, `exclusive_payment_local` |
| Preservation of the open and closed batch ledgers | `merge_open_valid`, `mergeClosed`, `merge_closed_valid` |
| Exact own cost, rather than an assumed own identity | `allocation_own_identity`, `frozen_own_identity`, `frame_own_cost`, `package_frozen_own_identity`, `package_actual_own_identity` |
| `r8c:state-preservation`, committed rounds and finite induction | `GroupUpdate`, `CommittedRound`, `Execution`, `committed_round_valid`, `execution_valid`, `execution_budget` |
| No duplication or loss of original roots | `donation_ids`, `merge_open_ids`, `merge_closed_ids`, `group_update_ids`, `committed_round_ids`, `execution_ids`, `execution_distinct` |

The actual donor output is explicit. If executed, exactly its designated label has new observer cost `baseline(i)-utility(i)`; all other labels use allowed equalizers under the supplied complete permutation. If not executed, the old actual allocation is retained. The proof derives the own credit and the new deficit bound from that table. It does not take the new frozen `D` or `L` tables as arbitrary inputs.

`ordinaryTasks` indexes nominal donors once by their actual recipient. The two sum-identification theorems prove that, at a fixed label, the sum of actual new extras is `batchLoss` on that label's task class and the sum of payments is `retainedCredit` for its designated observer, zero otherwise. This is the finite bridge between the actual donor records and the separate same-component utility proof. Zero-own nominal roots still occur in the input list and retain their IDs when frozen.

## Local hypotheses and what is not assumed

`Proposal.Good` requires the old live frame to be good. For an executed proposal, its supplied permutation maps the modified label to the designated recipient, every other permutation edge is old-allowed, and the own affine utility is nonnegative. Ordinary execution is defined by strict positivity; affine execution retains zero own values as well. Executed group constructors enforce these two respective mode rules.

`merge_open_valid` assumes an **exclusive local payment certificate**, expressed in the computed `extras` and `payments`: either the new donor loss is paid while the survivor reserve does not increase, or the donor loss is zero and the whole new reserve is paid. It does not assume the desired new `D+H <= L` inequality. `ordinary_component_cases` derives precisely these two alternatives from the allowed/forbidden update, same-label clipped envy comparisons, and unused-parent threshold. `protected_component_zero` handles the no-new-deficit observer case. Identifying which geometrically obtained proposal supplies these hypotheses is still part of the written source proof.

The closed-batch theorem assumes that its calculated new extras are bounded by its calculated nonnegative own payments. `affine_component_payment` derives the individual positive-deficit bound from affine envy-freeness, including the zero-own case. Closed-batch geometric equalizer containment and the actual Offset SubCore output guarantee remain paper obligations.

An executed ordinary transition additionally preserves the survivor's original root ID, baseline table, and equalizer-cost table. Its new live frame must be good. The current finite relation does not assert SCC membership, first-outside eligibility, physical realizability of the prefix costs, or that a supplied new mask/frontier comes from a particular continuous execution. Those restrictions are established in the mathematical proof and are stronger than the numeric transition guards.

## Committed rounds and root conservation

`GroupUpdate` is a computation on an isolated input group. `CommittedRound before after` chooses an entire list of groups whose flattening is a permutation of `before`, computes one output for every group, and commits exactly that complete output list. A new survivor cannot be reintroduced into another old input group inside the same formal round. The relation therefore captures the corrected inactive-output-buffer/commit boundary. It makes no common-SCC assertion about transient group computations.

`Execution` is the reflexive transitive closure of these committed rounds. The formal induction proves that every resulting package satisfies the actual frozen-deficit/live-reserve budget. Independently, each step preserves the **multiset of original root IDs**. Initial root-ID `Nodup` therefore implies root-ID `Nodup` after every finite execution, including ordinary zero-donor and closed-affine steps.

The formal pool includes **closed packages retained for permanent allocation accounting**. Its list length is not the active-pool size used in the scheduling recurrence. Closing a leftover group preserves its root IDs instead of deleting those physical allocations. The formalization does not prove the active scheduler's SCC/revelation selection, sufficient live-root survival, termination, or query/cut ledger. Earlier pool-floor arithmetic modules remain separate; no new linkage to those counting theorems is claimed here.

## Own-cost identity and remaining physical boundary

The complete owner permutation gives each observer exactly one assigned prefix in each root. `allocation_own_identity` proves the sum of its label credits equals baseline minus the actual cost at `owner.symm i`. This is summed over frozen roots, and `frame_own_cost` proves that a good live root contributes exactly its baseline. Consequently `package_actual_own_identity` derives the paper's exact own-cost identity for all actual recorded roots from the definitions.

The real entries are finite cost tables. Nonnegative nonatomic measures, interval/finite-union containment, the complementary-prefix realization of the supplied affine values, visited-graph paths, all-small/large-gap geometry, and legal ordinary Eval/Cut implementations are not encoded as measures or protocols in this file. No theorem claims that every state admitted by the finite guards is physically reachable. The result is a stronger verified finite composition layer for the mathematical proof, not a kernel proof of the entire continuous theorem.

## Build and source pin

The author ran only this module's standalone compilation and its own theorem-axiom audit. The aggregate coordinator owns global imports and verification.

The Lean source is **FROZEN** at SHA256 `117e580691cb0b15f0d3c5190cd4602155f4aa3f9a1b092668e25abb637b56f1`. It contains **62 authored theorems, 34 definitions, 6 structures, 1 inductive transition relation, and 1 abbreviation**. Standalone compilation returned exit code zero with completely empty output: no errors or warnings. The source contained no `sorry`, `admit`, or custom axiom declaration. The accompanying mathematical-source snapshot was SHA256 `c05e3fc2c4aaf1cad20f000de2ffbd1ba31340623686b1638cfa1dd6b0762c7d` for `paper/sections/chore_proof.tex`; the mapping uses equation labels so cosmetic line movement does not affect it.

The exact standalone command, from the submission's Lean directory, is:

```sh
cd research/submission_focused/verification/lean
PATH="../../../tooling/lean-4.35.0-darwin_aarch64/bin:$PATH" ../../../tooling/lean-4.35.0-darwin_aarch64/bin/lake env lean EnvyFreeResearch/ChoreComposition.lean
```

The author also compiled a temporary exact copy of the frozen source with a `#print axioms` command for every theorem below. **All 62 theorem audits passed**, with zero warnings and zero errors. The only reported axioms were `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom or `sorryAx` occurred. The source hash was checked again after the audit and remained unchanged. The full local printout is `/tmp/chore_composition_axioms.log`, SHA256 `c862004e2e9cb265bb0eee261282e216779ae9688c5389ad496d0ef8c290bff9`. The aggregate coordinator's audit supplies the permanent bundled log. This local audit neither imports an edited umbrella nor runs the global verification script.

Every theorem below has the namespace prefix `EnvyFreeResearch.ChoreComposition.`:

```text
total_nil
total_cons
total_append
total_add
total_mono
total_nonnegative
total_flatMap
allocation_debit_nonnegative
frame_reserve_nonnegative
frame_credit_zero
frame_debit_le_reserve
reset_good
reset_reserve
proposal_root
proposal_zero_is_unchanged
proposal_payment_nonnegative
proposal_credit
proposal_debit_bound
ordinary_proposal_good
ordinary_nonpositive_is_unchanged
affine_proposal_good
package_reserve_nonnegative
seed_valid
package_reset_valid
package_reset_ids
package_close_credit
package_close_debit_bound
package_close_live
package_close_ids
package_close_valid
donation_credit
donation_debit_bound
donation_frozen_nonnegative
donation_ids
merge_open_credit
merge_open_debit_bound
exclusive_payment_local
merge_open_valid
merge_closed_valid
ordinary_component_cases
protected_component_zero
affine_component_payment
merge_open_ids
merge_closed_ids
ordinary_tasks_payments
ordinary_tasks_extras
allocation_own_identity
frozen_own_identity
frame_own_cost
package_frozen_own_identity
package_actual_own_identity
group_update_valid
group_update_ids
groups_valid
groups_ids
committed_round_valid
committed_round_ids
committed_round_distinct
execution_valid
execution_ids
execution_distinct
execution_budget
```
