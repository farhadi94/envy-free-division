# Terminal aggregation and extraction implementation

The earlier `chores_resume_independent_review.md` was an independent read-only review of the preimplementation snapshot. This document records subsequent implementation; these new proofs require a fresh independent reviewer.

## Actual atomic extraction

`ChoresTerminalExtraction.actual_atomic_extracted_bounds` uses the actual immutable-table atomic classification and actual affine payment parts. It includes a whole offered-block witness and concludes the large/small physical measure bounds for the union of every assigned suffix.

`ChoresTerminalExtractionMarked.marked_private_eq_extracted` identifies that union with actual private-cache slots of assigned donor roots. The identity includes all affine donors, even zero-credit donors. `remainingPrivate` removes exactly those slots. `actual_remaining_slot_small` bounds each actual remaining slot outside the extracted union, using the complete original-piece complement and every old frozen root. `actual_atomic_residue_bounds` sums these once over the immutable root universe. The bounds do not assume the extracted set itself is small. Exact complement-cache correctness is supplied by the imported `Outer.full_removed_cache_correct` and the marked-slot identity.

## Actual exhausted margin

`ChoresTerminalAggregateDonor` locates the actual executed donor in the full output pool and proves its recipient and baseline identities. `ChoresTerminalAggregateDonorPhysical` identifies its stored cost with the physical original piece minus its actual suffix.

`ChoresTerminalAggregateMargin.actual_full_allocation_donor_margin` applies the full physical package surplus invariant, including all old closed packages and frozen ancestors, to that donor witness. Its conclusion concerns the actual `fullAllocation` cache, not a nominal payment table or a certificate target.

`ChoresTerminalAggregatePrivate` propagates the small whole-complement bound through actual exhausted donor resets and unchanged/frozen roots. `ChoresTerminalAggregateExhaustedResidue` obtains the actual entire residue bound from recorded complementary caches. `ChoresTerminalAggregateFullMargin.actual_exhausted_full_margin` joins this with immutable-scan exhaustion and the explicit scalar reserve inequalities; its targeted build completed with exit code 0. All 15 new aggregation/extraction modules passed targeted compilation.

## Scope

These results are supporting theorems for the concrete terminal dispatcher. They do not certify the whole deterministic chore protocol. The actual outer/local dispatcher, preprocessing, recursion, and final query ledger remain separate integration obligations. No main-result percentage is inferred from module or theorem counts. No `sorry`, `admit`, or custom axioms were added. Targeted successful builds are recorded separately; a transitive closure audit has not been performed here.

## Scoped axiom audit

The scope consists of 15 implementation modules with 30 handwritten theorem declarations: 29 public and one private. Lean also stores six generated theorem helpers in these modules, for 36 owned theorem constants. The audit enumerates constants by their defining module, including the private helper and generated declarations, and checks each theorem's transitive axiom dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Source and compiled-object hashes are recorded separately.

The generated audit driver is `verification/lean/EnvyFreeResearch/Full/ChoresTerminalAggregateAudit.lean`; the exact per-theorem output and results are recorded in `formalization/logs/chores_terminal_aggregate_axioms.log` and `formalization/logs/chores_terminal_aggregate_audit_metadata.json`. This is a scoped audit against existing compiled dependencies, not a cold transitive-closure rebuild or an independent review of the mathematics.

The scoped audit completed with exit code 0. All 30 source theorem declarations were present among the 36 audited constants. Every axiom dependency was among the three permitted standard axioms; no unexpected axioms were found. All 15 source hashes were unchanged before and after the audit.
