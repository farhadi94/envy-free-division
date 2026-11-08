# Author audit of pooled chore composition

This is an author/auditor record for the focused post-review revision. I edited the chore appendix and therefore do **not** act as an independent referee of those edits. The coordinator assigned a separate fresh reader to review the resulting source. Frozen rounds and the literature archive were not modified.

**Conclusion:** the focused audit found no counterexample or additional hypothesis requiring a change to the deterministic theorem or either query bound. It found a missing explicit scheduling contract and an overbroad physical-accounting sentence. Both are repaired below. The new text proves the ledger update from actual root allocations and makes the global committed boundary explicit.

## Source and change record

The input `paper/sections/chore_proof.tex` had SHA-256
`f9b805f6f5e6a37c7de31466f8a330d3e3123a8a5cedc0798699b6b2593b035e`.
The final revised source has SHA-256
`c05e3fc2c4aaf1cad20f000de2ffbd1ba31340623686b1638cfa1dd6b0762c7d`
and 974 lines.

The deterministic subsection of `general_results.tex`, through the start of the randomized upper subsection, remains byte-identical, SHA-256
`bdb8814e13efaa162f3d33453e7611c7aa897dfb6256f0fc5b4f7372418801c9`.
In particular, there is no weakening of arbitrary nonnegative nonatomic costs, every legal Cut reply, complete allocation, exact envy-freeness, `2^{3n log_2 n+O(n)}`, or the explicit envelope.

Unchanged proof dependencies read through their required interfaces:

| Source | SHA-256 |
|---|---|
| `sections/core_proof.tex` | `7f7b9233216c488d2de28e659639d0c6d1325a6d0fb1e613b819ffd4356208bf` |
| `sections/baseline_subcore.tex` | `15baaa46e3c96f9e94e8d83500dbc0d66f35ac6ce36642b7d74dc453ec385c01` |
| `sections/offset_subcore_proof.tex` | `8c9ddf586a21189ae2068843683e93dd33d20a598dc845598ef29a3e56492ea2` |
| `sections/baseline_completion.tex` | `6b0ba931c2c3d8204666f40b576d4a0509eb9eab5ed7ada3bfce13684e025d52` |

During this pass other authors added measurable-protocol definitions and revised other theorem prose. The observed `model.tex` hash was `534b15490f651f91bad820971e5bd3a4e144cb277336b79808668c0cfee75b11`, and `general_results.tex` was `1aec573fa9119d53d4fe04bc7d4a7224b588bf82da9df9517726023426b48d9a`. These whole-file hashes are contextual; the unchanged deterministic subsection hash above identifies this theorem's statement.

The first full revised draft was `dc9c5de2c13d243b90083b11259a5b67963ef23b0e7db136e70f0ecbfcd9dd30`. A separate reviewer read all 969 lines and requested two notation clarifications: “fix `i != j` and a label `p`,” and explicitly require `t >= 1` in the continuing-step floor calculation. Those produced `e8f8b47ab08d2459c588b4e03b4572e9ed91a672dbe5f645e0f1737f0e15776c`. The coordinator then replaced the unsupported `\mathscr U` font command by `\mathcal U`, producing `8c27202366b357ac0a0a7f606313a2bb3740e275ce62feafbc49f1274c4b0df9`, and added four thin operation-table separators to produce the final hash. Reversing those exact typography changes reproduces both preceding hashes. None changes a mathematical assertion.

## Issues resolved

**Committed pool boundary.** A local `d+1`-root group produces a survivor with the merged SCC partition. Unprocessed groups still have the old partition. Consequently, inserting that survivor into the active old pool and allowing it to participate in another group or revelation would not satisfy the advertised common-partition invariant. The revised protocol reserves disjoint groups from the complete old pool, computes all outputs tentatively with the old partition/proposals, closes old leftovers, and replaces the pool in one commit. No survivor is available to another operation before that commit. This implements the intended simultaneous round with the same queries and the same grouping factor.

**Formerly private material.** The old sentence “Any formerly private part is included once in `E`” was too broad. A new donor prefix `P\E` can reattach part of the old private complement. Only formerly private material in `E` belongs to the removed suffix. The revision states the exact partition `P=(P\E) ⊔ E` and accounts for both possibilities. The original offset formula already gives the correct own reduction; no extra credit is created by restoration.

**Legal schedule quantification.** A component is revealed only when it lacks a pending proposal. Merger rounds use available pending cycles. Resets and closures are the finitely prescribed substeps of these operations, not arbitrary repeatable scheduling choices. Thus the prefix counts apply to every legal choice among available components and cycles, rather than to an unconstrained sequence that could repeatedly reset or reveal the same component.

**Actual state rather than hypothetical budgets.** The state, local update formulas, and preservation proposition now distinguish real root allocations, actual frozen deficits, actual own reductions, and prospective live reserves. The final reserve inequality is derived from those quantities; it is not supplied as a transition precondition.

## Explicit state and invariant

`r8c:state` records immutable original parents, equalizers, costs, gaps, masks, atoms, `R_0`, and reference costs; a partition of originals into active and closed packages; root bijections `pi_s`; actual prefixes `Y_{s,p}` and exact complements `U_{s,p}`; live graphs and `R,F,Z` data; the common SCC partition, representatives and pending proposals; operation counters; and an optional atomic/exhausted terminal record. An active package has one live root. A frozen root never changes again, and only one label can differ from an equalizer assignment in a donor root.

The numerical entries are computed from actual allocated pieces:

`delta_s(i,j,p) = 1_{pi_s(p)=j} [b_{s,i} - C_i(Y_{s,p})]_+`,

`lambda_s(i,p) = 1_{pi_s(p)=i} (b_{s,i} - C_i(Y_{s,p}))`.

`D` and `L` sum these entries on frozen roots. Live own reductions are zero. The live reserve is exactly the piecewise formula in `r8c:reserve`; a closed package has reserve zero. Admissibility is `D(i,j,p)+h_K(i,j,p) <= L(i,p)` for `i != j`.

The own-cost identity is a consequence of the root bijections and the definition of `lambda`, not an independent guessed budget. The full unallocated domain is exactly `R_0 ⊔ ⊔_{s,p} U_{s,p}`. Original cutter tails have already been accounted for by later snapshots, fixed clearance allocations, or `R_0`; no live reset borrows from any of those other allocations or another root.

The invariant is indexed by a fixed rival. One own reduction legitimately protects comparisons with several different rivals. Within one fixed `(i,j,p)` comparison, however, the ordinary merge must pay either the new donor deficit or the new live reserve using its additional credit. The proof establishes that exclusivity before summing over labels.

## Checked transition obligations

| Obligation | Derivation checked in the revised text |
|---|---|
| Initial reachable state | Singleton original roots use the identity matching and whole original prefixes. Original envy-freeness gives zero deficits, reserves and credits. Original pieces are disjoint. |
| Reset | For an actually assigned allowed edge, `delta_s=H_s`; otherwise `delta_s=0 <= H_s`. Changing the matching within `G_s` preserves each recipient's baseline and uses only its own root's complement. `D,L,h_K` are unchanged. |
| Ordinary closure | Exact updates are `D'=D+delta_s`, `L'=L`, `h'_K=0`. The allowed-edge bound directly yields `D'+h'_K <= L'`. Closure adds no credit. |
| Frozen ancestry | Groups consume disjoint complete packages. Their old frozen lists and all newly frozen nominal donor roots enter the output once. An unused or stripped nominal root is still reserved and frozen; no frozen root becomes a future survivor. |
| Donor recipient matching | The new `p -> j` edge and an old simple `j -> p` path form a complete cycle matching with self edges elsewhere. Every other changed label uses an old allowed edge and supplies the recipient's exact equalizer. |
| Own credit | On a physically removed suffix `E`, the credit is `C_i(E)-g_{s,i,p}`, not `C_i(E)`. Positive clipped own utility equals this affine quantity. A nonpositive affine proposal is not executed in an ordinary batch. |
| Zero clipped proposal | The root retains its old actual matching and has zero new credit. Its old deficits are covered by old reserves. Nominal cake comparisons force every deficit/threshold charged to a zero-credit observer to be zero. |
| Survivor matching | Root-specific old paths lie in disjoint components and join the actual incoming agents to the departing representatives. With the new cycle edges they give one simple permutation cycle. A union of perfect matchings has no edge between distinct SCCs, so exactly the chosen old components merge. |
| Frontier and forbidden update | The first outside eligible mark is after the old local frontier, including formal ordering of coincident physical marks. Earlier eligible agents are internal. Old allowed equalizers contain the new frontier; new forbidden recipients are internal and disjoint from the allowed set. |
| Internal rival payment | For `i,j` in the source component, the one possible modified `p`-donor deficit is at most `a_{i,p}` by masked same-label EF. The survivor reserve is unchanged for an old allowed recipient and zero for another internal recipient. |
| External rival payment | For `i` inside and `j` outside the source component, no `p`-donor is assigned to `j`. The entire new survivor reserve is bounded by the unused-parent threshold `a_{i,p}`. |
| Outside observer | An eligible mark lies at or left of the first outside mark. An omitted mark on the wrong side would express its large original gap as at most `n` small atoms, contradicting `H^2>n`. Both donor extra deficit and new frontier deficit are zero. |
| Nonadvancing label | No extra donor deficit or credit is created, and its survivor reserve is unchanged. Connecting-path assignments use old allowed edges. |
| Closed affine batch | All offered whole affine utilities are nonnegative. Every participant, including an own-zero recipient, is executed. Affine EF and nonnegative own utility give `[u_i(D_j)]_+ <= a_i`. Outside observers' equalizers are preserved. With no live reserve, this pays every new actual deficit. |
| Masks and ordinary queries | Disjoint source components give at most one task per actual observer. A genuinely new primary target lies in that task's own block and locates one recorded physical interval. Masked plateaus reuse records; the protocol never asks the original observer to ignore an irrelevant physical block in an interval query. |
| Global merger commit | Every group uses the old partition and old proposals. Outputs stay inactive until the common commit. The round leaves exactly `floor(M/(d+1))` active packages with the same new partition. |
| Pending proposals | Filtering restricts root-indexed records. If the source is unaffected, its internal graph, frontier and eligible set stay fixed even if the actual matching resets to the identity. A target merged elsewhere remains one external component. Merged sources discard their proposals. |
| Pool survival | Continuing revelation retains at least `floor((M-B_0)/n)` roots; a merger retains `floor(M/(d+1))`, `d+1<=n+1`. For `t>=1`, each sends `M_t=(B_0+n^2+1)(n+1)^t` to at least `M_{t-1}`. No divisibility assumption is used. |
| Finite outer schedule | At most `n-1` merger rounds occur, and only an initial component or a newly created merged component can require a revelation. Thus `F<=n+G` and `F+G<=3n-2`, with the final closed revelation included. The base pool exceeds all scarce losses and class requirements. |

The central local derivation is now displayed explicitly. For one group, let `Dhat,Lhat` sum the old frozen tables, let `h_s` be its old live reserves, and let `e` be the actual extra modified-donor deficit at the fixed indices. Then

`D' <= Dhat + sum_{donors} h_s + e`, and `L' = Lhat + a`.

The four observer/label cases prove

`e + H'_w <= a + h_w`.

Summing old package inequalities gives `D'+H'_w <= L'`. This is `r8c:group-update` together with `r8c:exclusive-payment`. For a closed affine batch, `r8c:closed-update` instead sums all old live reserves and uses `e<=a`, with no live survivor. `r8c:state-preservation` inducts over complete commits using these derived updates, disjoint ancestry, the physical complement identity, and the guarded scheduling rules.

## Atomic and exhausted termination

The atomic scan stops at an eligible mark at or left of the first large atom. That agent is excluded from the participant set `A` and the large mask `B`, so both masks are proper; ownership and largeness make them nonempty. Every participant's offered full suffix has nonnegative affine utility. The whole returned parent is therefore a physical retained suffix even if its own affine utility is zero. Its large atom gives every observer in `B` cost at least `Hr_i` in `X`. For an observer outside `B`, at most `n` parents containing at most `n` small atoms each give the upper bound `n^2 r_i/H`.

`X` is the union of actual final assigned suffixes, including any formerly private portion belonging to those suffixes. Unremoved parts of the large atom remain in actual prefixes. In an unassigned root, the old allowed prefix still contains the large atom. Hence the residue outside `X` has only the original outer residue and small released atoms. This is a physical union bound: original atoms are charged once, regardless of how many resets occurred.

In an exhausted class, the common full eligible set is `A`. Each outsider has an original gap at least `Hr_i`, and each assigned suffix removes at most `n r_i/H`. Distinct recipients have distinct selected-root witnesses of size `(H-n/H)r_i`. The positive-surplus inequality retains those witnesses after all ancestors are added. Since `H>=Jn^2` and `H-n/H>=2`, they cover the complete residue. The full component's representative remains `p_*`, whose eligibility set omits the initial cutter; a terminal exhausted set is therefore proper. Recursion is on a strictly smaller population.

The two-group finisher receives actual disjoint domains `X` and the entire residual complement. Its input inequalities follow from the stated `H`. Whole-cell lower shares and retained whole public pieces protect cross-group comparisons; all reservation tails and unused bundles enter child domains. No endpoint need be evaluated for an inactive ancestor because that ancestor is protected by a whole-domain bound. No null material is discarded.

## Query accounting and theorem scope

The revision adds recorded state descriptions, free arithmetic, and a simultaneous commit boundary. It adds no oracle call, new cut, primitive trial, or additional pool reduction. Tentative computations on disjoint reserved groups use exactly the same SubCore calls as before. Every fresh endpoint is still recorded for current observers. All query expressions and parameter choices are unchanged.

The call charge continues to use a distinct nominal donor root that freezes, including stripped zero proposals. It does not charge only positive donations. The largest masked call may have exactly `n` participants, so `n(2^{n+1}-2n-2)` is retained. The node bound includes all original Core calls, clearance calls, failed DP candidates, original equalizer recording, every compensation call and finisher preparation. Smaller disjoint populations give at most `2n-1` recursion nodes. The existing all-`n` algebra yields the explicit envelope and `3n log_2 n+O(n)` leading exponent.

The unchanged continuous dependencies still supply the following facts. They are mathematical obligations proved in the paper, not conclusions of a finite ledger model:

1. Chore Core exists and its canonical finite dynamic program succeeds on arbitrary nonnegative nonatomic costs, including zero plateaus, for every legal Cut reply.
2. Permanent formal records, exact target equalities and ordinary bracketed Cuts realize clipped and affine SubCore, including affine primary-zero targets of positive original cost.
3. Each cost-table row is the value of the asserted actual physical prefix/suffix under one fixed nonnegative nonatomic measure. The artificial pooled order does not move or duplicate physical material.
4. Root-local path construction, frontier containment, atom masks, and the protected representative supply the geometric/payment premises used by the ledger inequalities.
5. Quantile refinement and finite real linear algebra provide the near-equal splitter, and the augmentation/recursion covers all actual remaining material.
6. The legal revelation/merger schedule has the floor-sensitive pool supply and termination proof in the text.

No hunger, density, common-support, strict-positivity, extremal-root, free disconnected-query, or externally initialized positive-benchmark assumption has been added.

## Finite formalization and validation boundary

I sent the exact root `delta/lambda` formulas, closure updates, four ordinary payment cases, affine closed-batch update, and synchronous group/round distinction directly to the author of `EnvyFreeResearch/ChoreComposition.lean`. I read that module's concrete `Allocation`, `Frame`, `Proposal`, `Package`, `GroupUpdate`, and `CommittedRound` definitions and its composition proofs.

The finite layer computes credits and deficits from cost tables; it explicitly distinguishes nonpositive ordinary proposals from executed affine-zero proposals; it derives reset/closure and open/closed group ledger preservation; and it preserves root-ID multiplicity through complete rounds and finite executions. It does not merely take the final package budget as the output's hypothesis. The local exclusive-payment certificate remains an interface premise, with component-case lemmas explaining the two alternatives. The paper proves that its actual masked primitive output and geometry provide that certificate. The formalization is a projection of the paper's full state, not a formalization of its SCC geometry, physical intervals, query responses, pool supply, or termination. Compilation of this projection is not a substitute for the continuous arguments above.

The formal-module author owns its final source hash, build result and axiom audit in `review/post_review_audit/chore_formalization.md`. This author record does not assert a build that it has not run or certify that collaborator's edits as an independent review.

For the TeX revision I checked matching environment delimiters, unique labels, resolution of every referenced source label, and absence of trailing whitespace. I ran no full-paper build and edited no other manuscript source. The coordinator ran the full build, identified and corrected the unsupported font command, and reported a clean 71-page build with the operation table on page 14. A separate reviewer performed the fresh mathematical read and requested the two notation clarifications recorded above. Final independent acceptance and the rebuilt arXiv package remain the coordinator's responsibility.

There are no unresolved mathematical questions identified by this author audit. The remaining work is final independent source/formal-artifact reconciliation and packaging, rather than a missing compensation argument.
