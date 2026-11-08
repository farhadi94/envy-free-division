# Independent constructive-agent review: moving-frontier pure-leftmost lower bound

Status: **ACCEPT for the written mathematical argument at the pinned source below.** This is an independent internal AI review, not human peer review or a full Lean formalization.

Reviewed source: `notes/coordinated_family.md`  
SHA-256: `2c6b3f7f74c04bf4baf82fa4d92ae1db304739434087d8dc1d90d05d72c4bf01`

## Scope of acceptance

For each fixed n≥3, α>0, ε<α, finite query horizon q and δ>0, the argument constructs one fixed finite-piece signed net-one profile on which the probability of a correct complete finite-union allocation within q queries is at most δ, with always-leftmost signed bracketed cuts. The expected-query consequence and rightmost reflection are valid. No common total-variation ceiling is asserted. Pointwise finite termination remains compatible with the conclusion.

## Checks

1. **Weighted envy certificate.** Starting from the whole domain assigned to tail owner c gives average nonowner score α. Moving a fraction of a resolved constant-density cell to k≠c changes that average by the stated coefficient. All cases of the one-positive-coordinate cone have nonpositive coefficients. The special case k is the unique positive observer uses an additional nonowner and therefore genuinely needs n≥3. The coefficient is zero at its worst n=3 boundary when K=1+1/α. This proof permits arbitrary fractional fragmentation of every earlier cell.

2. **Profile construction.** Each one-row refinement keeps the queried measure globally unchanged. The other rows decrease on the added prefix, then increase linearly to their fixed total one. Their cumulative functions consequently remain strictly below one before the endpoint. Every finite sequence has finitely many pieces and finite densities; there is no hidden limit profile.

3. **First-root replay.** A protected reply inside the resolved prefix cannot acquire an earlier root, because its entire preceding bracket segment is unchanged. A protected reply equal to one has absolute cumulative level one; the global strict barrier excludes all earlier roots even though later refinements alter the unresolved suffix. Zero targets, full-bracket targets, degenerate brackets, and negative targets are handled. In particular the construction does not rely on a sign-dependent selector.

4. **Batch capture.** At a query stage, restricting to one queried row costs at most n; taking a coordinate quantile costs at most two. On the retained tapes, that whole row is unchanged, while their earlier transcripts are protected. After q stages, one more endpoint quantile costs at most two. Thus the lower retained mass u/[2(2n)^q] is valid. Output endpoint counts may be unbounded across tapes: each returned output is finite, so its maximum endpoint below one is still strictly below one and the quantile argument applies.

5. **Persistence and fixed input.** A captured output has every boundary in the frozen prefix or at one. Its whole remaining tail lies in one share, and all later refinements have zero net mass on that entire tail in each row. Hence both its transcript and every bundle value remain fixed. Old captured failures are therefore preserved simultaneously, even for uncountably many tapes. Finitely many batches suffice to retain mass at least 1−δ. All rows, frontiers and measurable tape sets are selected from the protocol's fixed tape law before any actual execution tape is sampled.

6. **Cap, nonreturn and illegality.** The revised definition includes all query-free computation after answer q; only requesting query q+1 or failing to return produces the cap symbol. Measurable analytical kth-call descriptors, with virtual dummy descriptors after a real execution ceases to call, do not claim an executable nontermination test. An identical tape and real transcript fix the intervening internal behavior. The explicit handling of illegal-target attempts preserves bracket values and hence their failure status. These revisions resolve the two presentation issues raised during review.

7. **Consequences.** Success probability at least p and capped success at most δ yield P(success with Q≥q+1)≥p−δ, so E[Q]≥(q+1)(p−δ). Reflection maps a target t in a bracket of value B to B−t; this remains legal for both bracket signs and exchanges first and last roots. At most one additional Eval per simulated Cut gives the claimed constant overhead.

## Remaining boundaries

The construction uses arbitrary large finite density and total variation, as explicitly stated. It assumes the measurable oracle-protocol model used by the paper. The hard profiles are piecewise affine cumulatives, so their fixed-profile first-root replies themselves are measurable functions of legal query parameters. No bound on arithmetic bit complexity, finite precision, or total variation is derived.

The proposed pointwise finite exact-EF algorithm in `notes/consensus_reduction.md` is compatible: its stopping stage can vary without a uniform bound across these profiles. The known three-agent nonnegative-anchor algorithm is also compatible, because the terminal all-negative prefix makes every row genuinely signed in each captured hard instance.

No unresolved required mathematical finding remains in the pinned written proof. Continuous replay, finite cone algebra and the complete randomized construction should retain separate formalization labels; this review does not elevate partial Lean lemmas into a fully mechanized oracle lower bound.

Revision check: explicitly freezing only the first q call/attempt coordinates is sufficient for the capped execution, and malformed/incomplete output encodings remain profile-independent failures. Both clarifications were reread; acceptance is unchanged.
