# Independent review of the pure-leftmost moving-frontier argument

Reviewer: `/root/r9_extremal_outside_box`.

**Mathematical assessment: accepted at the written-argument level, with the
query-legality interface specified below.** This review concerns the new
round-10 argument in `notes/coordinated_family.md`, not the unchanged cake or
chore upper/lower proofs. No complete Lean formalization of the randomized
construction is claimed.

## Scope checked

I independently derived and checked the following chain.

1. **Density cone.** For each non-tail owner `k`, the change in averaged
   nonowner envy from moving a cell from tail owner `c` to `k` has coefficient
   `alpha sum_{i!=c} d_i+d_k`. Every case of the density cone makes this
   coefficient nonpositive at `K=1+1/alpha`. The case in which the positive row
   is `k` needs `n>=3`; its bound is exactly zero, which is sufficient because
   the requested tolerance is strictly below `alpha`.
2. **Arbitrary earlier fragmentation.** The movement calculation uses fractions
   of each constant-density cell and therefore allows any measurable division
   of the resolved region. It is stronger than a whole-cell obstruction.
3. **Refinement invariant.** Keeping the queried row unchanged and setting every
   other row to a negative multiple on the newly exposed prefix preserves the
   cone. Restoring each total on the final tail gives a positive finite density
   and keeps every cumulative strictly below one before the endpoint.
4. **All first-root cases.** A recorded root at or below the frontier has its
   entire preceding bracket segment unchanged. A recorded root at one is at
   absolute cumulative level one, which the strict barrier excludes everywhere
   earlier. Zero targets, full-bracket targets, negative bracket totals,
   degenerate brackets, and arbitrary cut origins are all covered.
5. **One-row capture.** A newly answered query is preserved by fixing its row
   globally, then choosing a frontier past all of its coordinates below one.
   No endpoint is assumed to have been queried before.
6. **Finite-horizon randomized capture.** At each stage a queried-row class has
   at least `1/n` of the current mass; a fixed coordinate quantile retains at
   least half. After `q` stages a final output-endpoint quantile retains half
   again. The gain is `1/[2(2n)^q]`, including `q=0`.
7. **Previously captured tapes.** Their actual query transcript and capped output
   code replay pointwise. Every old tail lies within one old output share, so
   subsequent zero-total changes on that tail also preserve all old bundle
   values. Thus a captured failure is permanent.
8. **One fixed input.** Finitely many batches reduce uncaptured mass below any
   prescribed positive tolerance. Every frontier stays strictly below one,
   so the final finitely piecewise-constant profile has finite densities and
   finite total variation. Choices depend on the entire fixed tape law, not a
   subsequently realized tape. There is no infinite-limit input.
9. **Measurability.** For a fixed piecewise-linear cumulative, the first-root
   selector is Borel. Finite query descriptors and finite output endpoint codes
   are measurable by the stated protocol assumptions. The maximum of the
   coordinates below one is measurable on the countable union of finite-code
   strata; its sublevel sets exhaust the relevant tape class as the frontier
   tends to one. Captured sets and their finite unions are measurable.
10. **Expected cost and reflection.** The success mass exceeding `q` is at least
    `p-delta`, giving `E[Q]>=(q+1)(p-delta)`. Reflection transforms a requested
    rightmost root into a leftmost root with target `B-t`; one Eval obtains
    `B`, giving at most two oracle calls per simulated Cut. Positive net totals
    and the approximation conditions are preserved.

## Resolved issues

The initial alternative proof that selected only tapes successful at batch
start was insufficient: later unprotected queries can change, so those tapes
need not remain terminating. That alternative has been removed. The main proof
now uses analytical kth-call descriptors, not an executable nontermination test.

The descriptor argument must count all valid-row/valid-bracket illegal-target
attempts whose legality depends on the input, or reduce first to pointwise-legal
strategies. The coordinator's intended manuscript interface is the latter:
prove the horizon lemma for pointwise-legal partial strategies, then use the
existing wrapper that checks syntax and geometry, evaluates a bracket total
before each simulated Cut, and rejects illegal targets. The hidden precheck
gives at most two calls per simulated call and preserves the original capped
success event exactly. The current note also describes how to freeze an illegal
target's endpoints if using terminal failed-call descriptors directly.

Malformed output codes and invalid allocations are failures independently of
the final envy calculation. They need not supply meaningful output endpoints;
valid finite allocations do. Infinite query-free computation is represented by
the abstract nonreturn action already allowed in the paper's model. None of
these conventions grants the protocol an oracle for deciding termination.

## Limits

This is a uniform-bound impossibility, not a claim that one fixed profile must
cause infinite expected cost. It is compatible with the input-dependent finite
protocol in `notes/consensus_reduction.md`. It does not assert hardness under a
common total-variation ceiling. The written probability-space construction is
not certified end to end by Lean.

No unresolved required mathematical finding remains in the reviewed note.
The actual manuscript integration should receive a separate source audit,
especially the legality wrapper and theorem scope.
