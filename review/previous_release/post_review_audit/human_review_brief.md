# Focused expert review of the two upper bounds

This packet identifies the main proof obligations in *The Query Complexity
of Envy-Free Division: Cake, Chores, and Mixed Resources*, by Alireza Farhadi
and Mohammadtaghi Hajiaghayi. No human expert has reviewed this revision as
part of the present audit. The accompanying internal reviews and Lean checks
do not substitute for that review.

## Materials and scope

The manuscript is `paper/paper.pdf`; its main source is `paper/paper.tex`.
The current formalization coverage is recorded in `verification/coverage.json`.
The three additional modules are `ChoreComposition.lean`,
`GlobalCompletion.lean`, and `QueryProbability.lean`, under
`verification/lean/EnvyFreeResearch/`. Their author notes distinguish checked
statements from their physical and probabilistic prerequisites. Build and
review receipts identify the exact versions checked.

The priority is the deterministic chore upper bound and the randomized
cake/chore upper bound. The lower bounds also received a focused audit of
measurability and the order of quantifiers. None of the four full main
theorems is claimed to be formalized in Lean.

## Deterministic chores: compensation and pool survival

Read Appendix A, especially the root-local state, masked compensation,
component-cycle advance, atomic and exhausted exits, and pool-floor induction.
The underlying Core, SubCore, and completion interfaces are proved in
Appendices B--E.

Please check the following against the actual physical allocations:

1. Every reachable committed state satisfies the reserve inequality
   `L(i,p) >= D(i,j,p) + H(i,j,p)`, the exact own-baseline identity, and
   disjoint ownership of original material. The ledgers must be computed
   from actual allocations, including privately reserved complements.
2. Reset and closure use only available original material. A root that
   supplied a donor modification is never made live again.
3. The same compensation credit is sufficient for every rival comparison
   without being used twice within one comparison. Check the exclusive
   internal-rival and outside-rival cases, zero clipped utilities, and
   affine-zero assignments at closed exits.
4. A component merger reserves disjoint groups and commits the complete
   pool round together. The common component partition is an invariant
   of committed states; transient input and output buffers must not be
   treated as one active pool.
5. Atomic and exhausted exits satisfy their completion interfaces for
   the entire physical residue. Large atoms, unused tails, and old
   private complements are all accounted for.
6. The integer pool-floor induction applies to every permitted schedule,
   with the stated prefix bounds on revelations and mergers, including
   the final closed class.

A useful review should identify any failing transition together with a
reachable predecessor, or explain why the physical construction supplies
each hypothesis in the finite transition lemmas. An abstract counterexample
that violates reachability should be distinguished from a protocol defect.

## Randomized upper bounds: primitive composition

Read Appendix F's interfaces for Repair, Snapshot, and prescribed shrinking,
then its global-completion argument. Please check:

1. Every invocation meets the primitive's hypotheses with the correct
   per-agent normalization. Any lower probability bound used after a
   conditioning step is uniform over the full allowed preceding history.
2. A rejected trial leaves the committed allocation unchanged. Its oracle
   queries, endpoint records, and any deterministic preparation are charged.
3. At most two successful shrinking requests produce the claimed transfer.
   No later shrink invalidates a previously small loss after a nonidentity
   transfer.
4. Whole-bundle transport preserves old domination counts, including
   frozen agents and zero residue rows. The new witness is a proper target
   and is not merely the image of a previously counted target.
5. Progress is measured against the saved committed allocation. Population
   changes, additive exits, and zero-residue cases preserve the same global
   bound of `n(n-1)` iterations.
6. Conditional trial-success bounds justify almost-sure return and the
   expected query bound. No independence between successive requests,
   polynomial bit-complexity claim, or uncharged oracle is needed.

Please trace the numerical/physical compensation interfaces back to their
proofs, rather than treating the interface table as an additional assumption.

## Lower-bound precision and scope

The revised measurable-protocol definition requires joint measurability in
the input-independent random tape and finite transcript. It does not assume
the tape space is standard Borel or require decidable nonreturn. The
nonnegative lower proof uses a fixed endpoint list on its null event of
infinite-query tapes. Check the common-width choice before sampling the
perturbed profile and the integration over fixed inputs.

In the mixed proof, a retained Cut root requires a query legal for both the
old and new profiles, and the truncation guard checks the bracket and row
before issuing an extra Eval. The protected-history construction must
preserve these conditions. Its final profile and selector must be fixed
independently of the realized tape.

The mixed theorem concerns bracketed signed queries with arbitrary legal
roots and no common total-variation ceiling. It does not establish a lower
bound for prescribed first/last-root oracles, a class with a fixed common
variation bound, or variation-normalized approximation.

## Requested report

For each substantive finding, provide the lemma or source location, the
missing implication or counterexample, and whether a local repair suffices
or a theorem statement must change. Separate verified proof obligations
from unexamined ones. Record the manuscript and relevant source hashes.
This packet requests mathematical assessment, not certification based on
the number of prior reviews or supporting Lean declarations.
