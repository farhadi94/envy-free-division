# Finite global completion: formalization receipt and scope

Author: `mixed_signed`. Independent interface reviewer: `cross_disciplinary`.

**Status: PASS; source frozen.** The new source compiles cleanly in the pinned focused Lean project, its targeted named build succeeds, and the module-only all-declaration axiom audit passes. The independent reviewer directly read the source and the imported transport/count proofs and accepted the finite-to-written interface. No existing Lean source, umbrella, `AxiomAudit.lean`, coverage file, frozen round, or global verification script was edited.

## Exact source

* Module: [`EnvyFreeResearch/GlobalCompletion.lean`](../../verification/lean/EnvyFreeResearch/GlobalCompletion.lean).
* Namespace: `EnvyFreeResearch.GlobalCompletion`.
* SHA-256: `dab3c06a639377d8415d43286e4406212dfd47f1ccee938ee80886307ea0e54d`.
* Inventory: **45 authored theorems, 19 definitions, 3 structures, 2 inductives**, plus one table abbreviation.
* Imports: `Mathlib` and `EnvyFreeResearch.R4GlobalPotential` from this same pinned project.
* Toolchain: Lean 4.35.0; Mathlib tag `v4.35.0`.
* Inspected manuscript: [`upper_proof.tex`](../../paper/sections/upper_proof.tex), SHA-256 `66955a399e1eaa71abf7df7f92662b23ba37b57e67998ee59482b75a4634fec9`. Stable source labels, rather than line numbers, identify the claims below.

## What the new composition actually proves

`WholeAddition` records a permutation fixing frozen labels, nonnegative additions that vanish at frozen recipients, the exact whole-bundle value identity, and the **full row conservation identity**

```text
new(i,f(j)) = old(i,j) + addition(i,j),
sum_j addition(i,j) + remaining(i) = residue(i).
```

It does not assume an individual spending bound, global new EF, invariant preservation, domination transport, or potential growth. `addition_budget` derives every individual budget from the sum identity and nonnegativity. `cake_own_bound` and `chore_own_bound` use only active-active new EF; frozen rows use the unchanged-label identity. `whole_addition_preserves_EF_guard` then proves global EF and the directional frozen guards, using the imported, kernel-checked four-case proofs.

`ConcreteStep` records separate nonnegative Snapshot, Shrink and Repair-payment tables, two permutations fixing frozen recipients, and two exact partition identities. Snapshot and Shrink are EF among active agents; final Repair is also only assumed EF among active agents. The source's small-own-loss and large-Snapshot-gap inequalities and quarter-buffer spending are supplied as finite inputs. **The final repaired witness, global EF/guards, target transport, and potential growth are not fields.**

`transferred_margin_identity` proves, in both preference directions,

```text
g(D;i,j) = g(old;i,j) + g(shrink;i,j)
           + g(snapshot;i,alpha(j)) - g(snapshot;i,alpha(i)).
```

From that identity, `transferred_near_EF` derives the −tau·rho lower bound, and `transferred_witness_margin` derives the (2−tau)·rho witness. Repair's actual whole-label identity and payment sums imply the post-Repair lower bound (7/4−tau)·rho. The residue bounds 3rho/4≤remaining≤rho, including strict positivity, are derived from the payment partition and quarter spending. The tolerance hypothesis tau<3/4 makes the repaired witness strictly larger than the new residue.

`concrete_step_composition` combines these proofs: new global EF and guards hold, and the saved-anchor domination potential increases by at least one. The old missing edge is supplied at the saved anchor; the theorem never compares to a temporary Snapshot potential.

For old targets, `whole_addition_positive_image` proves proper image inclusion only when the new observer residue is positive. `whole_addition_zero_row` instead proves exact saturation to `univ.erase i` at zero. The row-count proof therefore does not assume the false claim that every transported old proper target stays proper at zero residue.

## Finite run and terminal composition

`CompletionEvent` has only two constructors: a successful concrete continuation, or a freeze with unchanged value/residue tables, a retained subset, an explicitly removed agent, and the directional cross-boundary comparison certificate. It does not contain a potential-growth field. `event_preserves_valid`, `event_potential_growth` and `event_combined_growth` derive the invariants and progress from these constructors.

* `finite_run_valid`: all intermediate states preserve nonnegative values, nonnegative residue, global EF and the appropriate guard.
* `finite_run_iteration_bound`: the number of successful nonterminal iterations is at most n(n−1), even with interleaved freezes.
* `finite_run_with_terminal_bound`: including a final iteration still gives n(n−1) when its starting state has a proper missing domination edge. This avoids an unsupported extra +1.
* `finite_run_event_bound`: counting both successful continuations and actual freezes gives at most n(n−1)+n completed events. This uses the independently derived decrease in the finite active-agent count at a freeze.
* `no_infinite_completed_events`: an infinite sequence of returned concrete certificates is impossible. This is **not** a theorem that any particular randomized request returns.
* `finite_global_completion`: a finite concrete run followed by a nonnegative, complete additive active-EF allocation of the residue has a globally EF final value table, the zero-residue guard, and the proved iteration bound.

The terminal theorem assumes the final active allocation's EF certificate and its exact full-residue partition; it does not assume global final EF. `zero_chore_recipient_finishes` derives the special case assigning all residue to a zero-cost active recipient. `zero_cake_row_can_freeze` proves the corresponding guard at an already EF anchor. The source's rule to handle the one-agent base before freezing the last recipient remains a caller policy, not an assertion about an uncorrected transferred table.

## Finite physical-ownership support

`atom_partition_identity` uses an actual finite pool of recorded atoms and a single owner map into `Option Agent`: each atom either belongs to one recipient or remains unallocated. It proves total conservation by summing this unique ownership, including zero-valued atoms. `finite_atom_transition` constructs the corresponding whole-label value transition and derives its mass partition and nonnegative budgets.

This finite model proves disjoint ownership of the new pool at the level needed for spending bounds. It does not encode the old bundles as spatial sets, check interval geometry, or establish the freshness of the pool relative to those sets. Those physical facts justify the input value identities in the manuscript. In particular, zero remaining **value** in all rows does not itself prove an empty physical residue; coverage of null fragments is still a physical caller obligation.

## Manuscript-to-Lean mapping

| Manuscript contract or calculation | Exact new declarations |
|---|---|
| `r6u:physical-balance`, exact disjoint spending | `addition_le_total`, `addition_budget`, `residue_decreases`, `atom_partition_identity`, `finite_atom_transition` |
| `r6u:own-transport`, own comparisons before global EF | `cake_own_bound`, `chore_own_bound` |
| `r6u:guards`, global EF and frozen guards | `whole_addition_preserves_EF_guard`, `freeze_preserves_guard`, `event_preserves_valid` |
| `r6u:transfer` and the margin calculation before Repair | `transferred_margin_identity`, `transferred_near_EF`, `transferred_witness_margin` |
| `r6u:repair-contract`, quarter expenditure and whole endowments | `ConcreteStep.repairAddition`, `repair_gap_loss`, `concrete_witness_margin`, `concrete_witness_residue`, `concrete_witness_strict` |
| `r6u:whole-labels` and proper-target transport | `ConcreteStep.wholeAddition`, `whole_addition_domination_transport`, `whole_addition_target_counts`, `whole_addition_positive_image`, `whole_addition_zero_row` |
| `r6u:completion-contract`, finite continuation and anchored potential | `concrete_step_composition`, `finite_run_iteration_bound`, `finite_run_with_terminal_bound`, `finite_global_completion` |
| Zero rows and additive terminal returns | `terminal_additive_EF`, `zero_chore_recipient_finishes`, `zero_cake_row_can_freeze`, `initial_state_valid` |

The imported `R4GlobalPotential` and `R2OnlinePotential` results are proved theorems, not custom axioms. The new module supplies their transport and strict-progress hypotheses from the concrete value identities; it does not merely rename the old theorem that assumes potential growth.

## Remaining scope

The full n21 randomized theorem is **not** thereby completely formalized. The following remain written: construction of the continuous finite-union pieces and their ordinary Eval/Cut implementation; correctness and success probability of Repair, Snapshot and Shrink; the safe-factor/path argument that produces `small_own_loss` and `large_snapshot_gap` with at most two shrinking requests; SCC selection and base-case implementation; measurability, conditional probability, almost-sure request return, expected trial/query accounting, and physical coverage of all null fragments. The finite interfaces state exactly which returned certificates these arguments must supply.

## Validation receipt

Standalone command, with the pinned toolchain on PATH and working directory `verification/lean`:

```text
lake env lean EnvyFreeResearch/GlobalCompletion.lean
```

Result: exit code 0, no diagnostics. Targeted build:

```text
lake build EnvyFreeResearch.GlobalCompletion
```

Result: exit code 0. Only the existing Mathlib module-system compatibility warnings and replayed dependency audit information appear. No global verifier was run by this author, and its generated files were not edited.

The module-only axiom audit inspects every declaration whose defining module is `EnvyFreeResearch.GlobalCompletion`, recursively collects its axiom dependencies, rejects every custom axiom declaration and any dependency beyond `propext`, `Classical.choice`, `Quot.sound`, and checks a nonvacuous theorem count against the 45-declaration source inventory. It runs from standard input and creates no additional project file. The audit covered all 238 module declarations, including 129 kernel theorem declarations. The latter includes generated structure/inductive equations and auxiliaries; **45** is the authored mathematical theorem count.

```text
GLOBAL COMPLETION AUDIT PASSED: 238 declarations; 129 theorem declarations;
only propext, Classical.choice, Quot.sound.
Exit code: 0
Source SHA-256:
dab3c06a639377d8415d43286e4406212dfd47f1ccee938ee80886307ea0e54d
```

The module hash was checked immediately before and after the audit and was unchanged. A source-token scan found no `sorry`, `admit`, or custom `axiom` declaration. The package coordinator remains responsible for the later aggregate import/coverage update and whole-project verification.

## Complete authored theorem inventory

1. `margin_self`
2. `cake_ef_iff`
3. `chore_ef_iff`
4. `margin_add`
5. `addition_le_total`
6. `addition_budget`
7. `residue_decreases`
8. `whole_addition_nonnegative`
9. `cake_own_bound`
10. `chore_own_bound`
11. `whole_addition_preserves_EF_guard`
12. `whole_addition_gap_transport`
13. `whole_addition_domination_transport`
14. `whole_addition_target_counts`
15. `transferred_margin_identity`
16. `transferred_near_EF`
17. `transferred_witness_margin`
18. `repair_gap_loss`
19. `concrete_witness_margin`
20. `concrete_witness_residue`
21. `concrete_witness_strict`
22. `concrete_step_composition`
23. `freeze_preserves_guard`
24. `active_count_le`
25. `strict_active_count`
26. `event_preserves_valid`
27. `event_potential_growth`
28. `event_combined_growth`
29. `state_potential_cap`
30. `combined_potential_cap`
31. `finite_run_valid`
32. `finite_run_iteration_bound`
33. `finite_run_event_bound`
34. `finite_run_with_terminal_bound`
35. `no_infinite_completed_events`
36. `atom_partition_identity`
37. `atom_addition_nonnegative`
38. `atom_remainder_nonnegative`
39. `whole_addition_zero_row`
40. `whole_addition_positive_image`
41. `terminal_additive_EF`
42. `zero_chore_recipient_finishes`
43. `zero_cake_row_can_freeze`
44. `initial_state_valid`
45. `finite_global_completion`
