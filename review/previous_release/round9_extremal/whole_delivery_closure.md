# Round 9 delivery closure: scoped independent review

Reviewer: `/root/r9_extremal_outside_box`.

**Accepted; no unresolved required findings.** This closes the previously frozen
candidate review for the changed mixed theorem and its proof interfaces. It is
not a new line-by-line audit of the other three main proofs or of all unchanged
arguments in Appendix H.

All eight promoted paper source files exactly match the hashes in the frozen
round-9 candidate receipt. The canonical 72-page PDF is pinned by SHA-256
`2085d0199482f1e5c12db7b402bcef2e45393022fd809804a1f69c99b28345fa`.
The current successful 32-module Lean audit receipt matches every current
module hash; this reviewer reconciled that receipt and did not rerun the build.

I inspected the supplied renders of pages 1, 3, 5, 63, and 72. The abstract and
table caption identify prescribed sign-dependent extremal rules; Theorem 2.4
spells out both bracket-sign selectors and explicitly leaves always-leftmost
and always-rightmost rules outside its scope. The updated root-preservation
lemma includes zero/full targets and measurability. The formal-scope table and
paragraphs distinguish the continuous root lemmas checked in Lean from the
remaining transcript and measurability arguments. No overflow, clipped text,
or scope-changing discrepancy was found on these pages.

The source proof review remains the frozen round-9 review. The present receipt
adds source-to-delivery reconciliation and this limited visual check; it does
not claim a complete PDF or four-proof re-audit. All pinned hashes, including
Lean sources and inspected renders, appear in `whole_delivery_closure.json`.
