# Round 10 integrated candidate review

Reviewer: `/root/r9_extremal_outside_box`.

**Accepted; no unresolved required findings.** This review covers the eight
changed manuscript files listed in the JSON receipt, the complete replacement
Appendix H, its interfaces with the main theorem and protocol model, and the
claimed coverage of the new supporting Lean modules. It is not a new audit of
all unchanged cake/chore proofs.

The mixed theorem now applies separately to a fixed always-leftmost rule and a
fixed always-rightmost rule. It does not claim a lower bound for an oracle that
lets the algorithm request either extremum on each call. The abstract,
introduction, table caption, main statement, and overview consistently express
this scope. The net-total normalization, lack of a common total-variation cap,
arbitrary finite fragmentation, positive success probability, and separate
multiplicative/additive conclusions remain explicit. The manuscript retains
four main results.

I checked the replacement Appendix H line by line. The density-cone certificate
forces a failed envy comparison whenever the final interval is unsplit, even
with arbitrary measurable division of the preceding cells. The frontier update
preserves the cone and the strict cumulative bound before the terminal point.
That bound protects replies at one; agreement on the frozen prefix protects
all earlier replies, including zero/full targets and arbitrary legal brackets.

The finite-horizon theorem is correctly stated for pointwise-legal partial
strategies. Its analytical call descriptors do not require deciding internal
nontermination. The fixed row and coordinate-quantile choices preserve the
selected finite transcripts. The final output quantile is valid with no bound
on the finite number of output endpoints. Protected failures retain both their
execution and all bundle values through later updates. Finitely many batches
produce one finite piecewise-constant input independent of the realized tape,
including the zero-query horizon case.

The hidden-Eval wrapper in the expected-cost proof checks syntax, indices,
brackets, and legal targets; it uses at most twice the original capped calls
and preserves the original capped success event. It allows all query-free
computation after the last permitted query. The expectation inequality and
reflection reduction have the correct direction and overhead. The last
paragraph's zero-query allocation for tolerance at least alpha is valid on
net-total-one profiles.

The new related-work statement concerning Okano--Manabe (2020) was checked
against the archived primary text, Section 4: its first step obtains the
positive/negative-region decomposition of one valuation, with initial cut
count `c_1`. This access is stronger than bounded interval-query access on the
present unrestricted signed domain. No new priority claim for their
one-nonnegative-row special case is made.

The frozen `TranscriptAdversary.lean` interfaces cover continuous first-root
replay, legality, finite bundle-value preservation, affine frontier rebuilding,
continuity, and the terminal ceiling. The frozen `CoordinatedFamily.lean`
provides a finite two-nonowner obstruction under the same density cone; its
pairwise version implies the required existence of a violated envy comparison.
Both modules have clean author compile/axiom receipts, reconciled to the source
hashes in this review. I inspected their statements and proofs but did not
rerun those builds. The manuscript correctly leaves the whole randomized
transcript construction and selector measurability outside Lean.

No stale reference to a removed Appendix H label was found. Candidate PDF
inspection is deferred to the final canonical build and its delivery-closure
receipt; this source review does not claim a full visual audit.
