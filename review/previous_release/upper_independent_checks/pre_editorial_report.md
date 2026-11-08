# Independent audit of the complete randomized upper bound

**Verdict:** No blocking mathematical error or counterexample was identified in the final audited version. On this independent reading, Appendix F supplies the claimed complete Las Vegas cake/chore protocol and the stated expected query and Cut bounds. The one minor local scope clarification found during review is resolved in the final snapshot. This is a mathematical review, not a formal verification of the continuous theorem.

The audit was performed on 7 November 2026 and closed against `final_snapshot.json`, whose PDF SHA-256 is `2cb128afb74e0bd288a08db4db36fcb5a1a4bb4b8165e506254a5544544aa7c8`. Exact input SHA-256 hashes, scope, and check results are recorded in `upper_independent_receipt.json`. This reviewer did not edit the manuscript or other reviewers' files. Earlier author notes and review conclusions were not used as evidence.

## Scope

I read the full actual source `paper/sections/upper_proof.tex`, lines 1–1146, including the caller and all query accounting; the main theorem `thm:general-upper` in `general_results.tex`; `upper_overview.tex`; the model; the formal-scope statement; and the paper's inclusion structure and relevant bibliography entries. I checked the rendered Appendix F in `paper.pdf`, printed pages 37–52, against the source. The proof is self-contained with respect to Appendices A–E: its refinement, repair, and completion arguments do not invoke those appendices' Core or SubCore implementations.

Primary PDFs consulted were Mackenzie–Suzuki's physical repair construction, especially Sections 5.1–5.5 and its main theorem/Remark 1.1; Psomas's Section 3 domination/whole-label transport argument; Shmoys–Tardos's Section 2 sorted-slot construction and Lemma 2.2; and Musco–Musco–Woodruff–Yasuda's Lemma 2.6. These were used to check the provenance and the relevant finite mechanisms, not as substitutes for the submitted proof's chore extension or its treatment of nonhungry measures. In particular, Mackenzie–Suzuki's main theorem is stated for hungry agents, so its remark alone would not establish the submitted general-measure claim. Appendix F gives the needed additional arguments itself.

I did not compile or rely on Lean. The manuscript correctly limits Lean's scope to selected finite statements. Neither this review's finite checks nor a Lean build establishes the continuous random protocol.

## Findings and actions

### U-01 — Minor local population-scope clarification, resolved

**Location:** `upper_proof.tex:936–964`, especially line 961, equation `r6u:shrink-cost`.

The displayed comparison `(12k+34)ℓ ≤ 32kℓ` requires `k ≥ 2`; it is false at `k=1`. The original surrounding standalone shrinking discussion did not repeat that restriction. The actual caller starts such iterations only at `k ≥ 3` (lines 1005–1007), and it handles one or two active agents directly (lines 993–1003). Thus this did **not** invalidate the implementation, the theorem, or its complexity bound.

**Resolution checked:** The coordinating author added “for the active populations `k ≥ 3` used by the caller” at line 959. I inspected this change in the actual TeX and rebuilt PDF. It fully resolves the scope issue. No algorithmic change was needed, and no action remains.

No missing lemma, circular guarantee, incorrect cake/chore sign, or uncharged oracle operation was found that blocks the stated upper-bound theorem.

## Audit of the proof chain

### Ordinary queries, singular measures, and interpolation

Lines 43–91 implement a cumulative Cut on a recorded union using one actual component Cut, with cached values locating the component. Strict interior targets prevent an arbitrary legal nonnegative-measure root from escaping that component. Logical cells can cross recorded joins without adding a factor for the accumulated number of physical components.

The circular sampling law is valid for foreign nonatomic measures charging cutter-null intervals. For each fixed point, the event of inclusion is a translated value-circle arc except at a probability-zero equality of the uniform target and that point's cumulative value. Tonelli then transfers the law to foreign measures. The countability of nontrivial plateau levels removes dependence on an adversarial legal root choice for fresh uniform targets. This also justifies the mixture sampler under measurable nonanticipating policies. No density, absolute continuity with respect to length, common support, or hunger premise is used.

For the integrated interpolation estimate (lines 93–157), the minimum-spanning-tree argument genuinely bounds the maximum pair sensitivity by `k−1`, including identical rows. Deleting a sampled grid point has normalized error at most the sum of the incident sensitivities; exchangeability applies because the measures and permanent grid are fixed before the sample. The argument also handles zero table disagreement.

The aggregate endpoint lemma (lines 159–194) uses conditional marginal laws **before each group's shared fresh start**. It does not assume endpoint independence within a circular group. Its pathwise sum of predictable dominating measures is sufficient after taking conditional expectations. Since every generated endpoint is charged before acceptance, the lemma includes the first rejected correction, rejected candidates, inherited endpoints, and unions selected after all recorded values are seen.

### Corrections, reserve selection, and assignment isolation

The maximum-cell envelope (lines 199–291) bounds the estimated correction for every observer of a fixed recipient simultaneously. Its integral is at most the number of original reserve cells, including when the actual measure is singular. Combining the whole-cell term, envelope term, and actual interpolation term gives exactly the stated half/quarter/quarter error allocation. The owner payment stays exact. There is no extra observer union bound hidden in that calculation.

The reserve is selected by independent coarse-parent labels after representative selection. In the analysis, revealing those labels before the independent sample is legitimate: the reserve-normalized restricted measures and its permanent boundaries are then fixed. The mass, count, selected-parent, and payment failure bounds are not conditioned on a favorable sampled table or on each other's success.

The two-cell representative rule (lines 313–358) remains valid after the two actual reserve normalizations are substituted. Removing parents, rather than just cells, makes the ultimately chosen witnesses disjoint across pairs, repetitions, and batches and keeps them disjoint from the reserve on successful preparation. At every selection, all eventual reserve cells are still available. These facts justify the `A_ij/3` witness increment.

In the isolation argument (lines 379–448), fixing the permutation and all but one threshold leaves both deleted-column assignment scores independent of that remaining threshold. The signed pair comparison moves monotonically in steps at least `A_ih/3`. The clipped reciprocal-gap integration and the simple-cycle argument yield the displayed bound without conditioning on which assignment wins. A two-cycle contributes distinct pair-column triples because its columns differ. Pairs with `A_ih=0` cannot by themselves make an ordinary optimum's cycle positive.

### Physical cake credits and chore taxes

The two directed graphs have the required different orientations (lines 379–384). Their no-positive-cycle potentials imply, respectively,

- cake: `V_i,π(i)+t_i − V_i,π(j)−t_j ≥ 2λA_ij`;
- chores: `V_i,π(j)+t_j − V_i,π(i)−t_i ≥ 2λA_ij`.

The chore construction therefore uses nonnegative added taxes with the correct sign. Its supply argument is not borrowed from cake: the minimum-assignment regret sum bounds the ordinary part of each outgoing chore edge. The maximum-assignment shortfall sum does the corresponding job for cake. Neither bound requires old endowments to be small compared with the buffer.

The fractional reserve plan supplies every observer moment `t_j`. Floating preserves the cell sums and `k²` moments and leaves at most `k²` fractional cells. The sorted-slot matching saturates the full slots, with per-cell capacity respected across recipients. Its neighboring-slot comparisons bound the owner's rounded load within one cell of the target; deleting overpaying matched cells leaves a nonnegative deficit at most `η_R`. Only split-cell coefficients change, which gives the stated `k²A_ij` disagreement bound.

The supply induction (lines 546–569) excludes pending whole-cell payments as well as completed payments. It establishes `w_i(S)>7/8` **before** every reached fresh correction, including a correction that subsequently rejects. Thus the endpoint density and envelope estimates do not assume their own success. Adding the physical errors to the ideal inequalities gives the actual EF margin for both preference orientations. The independent seed/reserve spending bound leaves at least three quarters of every active observer's buffer.

### Snapshot and prescribed shrinking

Contrast preservation uses only the conditional exchangeability of labeled seeds; the whole-trial intersection calculation does not assert a uniform success rate conditional on every sampled preparation. The ideal-payment row ranges are at most `2Δ` in both directions, so the two-row contrast forces the claimed positive actual margin.

Snapshot's zero branch checks actual complete EF. Cell agreement alone is never declared sufficient. In the small-disagreement branch, the two circular groups have domains bounded away from zero in cutter value, despite a possibly very small final buffer. The estimated-witness expectation is valid even when the positive estimated cells have zero cutter value. All `16k` candidate endpoint lists are charged to one immutable table. The unconditional interpolation event can therefore be intersected with the conditional per-candidate witness bound without conditioning on the selected candidate. The subsequent repair is fresh after the entire checked-candidate history.

For large disagreement, comparing a suitably oriented positive or negative witness cell with an empty third endowment survives the unknown reserve normalization. This is why `k ≥ 3` is used. The displayed small- and large-branch constants both dominate `θ`.

The individual-query refinement (lines 884–934) is a finite constructive replacement for a quota oracle: only fractional cells are refined; every row's median halves that row's value in every child; integral cells never reenter; and after `J` rounds the remaining fractional union has value at most `δ`. Nonnegative masses make discarding it to the dummy one-sided. Prescribed shrinking consequently has both the lower and upper residue bounds needed later. Its logarithmic refinement depth, including carving in every rejected attempt, is charged.

### Complete caller, guards, and strict progress

I checked the full caller at lines 970–1125, rather than treating local repair as a completion theorem. Sink-component freezing has the correct orientation: cake freezes the sink; chores freezes its complement. The resulting guards are exactly the comparisons needed when the remaining resource is allocated among active agents.

The scale-selection interval has multiplicative width `16/(3τ)`, smaller than the factor ratio `8/τ`. Thus each nondiagonal row excludes at most one of the `k` factors, and the diagonal excludes none. Both bounds on the shrunk residue imply that the chosen certificate-column entries are either small or large. The subsequent path argument accounts for all three branches: identity at a crossing into the certificate label, a permitted path rotation, or a second shrink followed by identity. In particular, the second shrink is not applied after a nonidentity transfer, so it cannot invalidate previously certified small own losses.

The whole-label identity after final repair is sufficient for frozen comparisons and global EF even though a recipient may change. For cake, final EF makes an active observer's own bundle worth at least its own old label; for chores, it makes its own cost at most the cost of its own old label plus that label's additions. These are exactly the two inequalities used to transport old domination targets.

Positive row residue prevents an old proper target's image from becoming the observer. Zero row residue instead saturates all `n−1` proper targets; the proof explicitly handles this case. The witness margin exceeds `(7/4−τ)ρ_b`, and `μ_b(U')≥3ρ_b/4>0` makes its target proper. Since its old label was a nondomination edge of the **saved anchor**, its image is new relative to the transported anchor targets. Counting only committed allocations avoids counting temporary Snapshot/Shrink gains twice.

Active zero-residue cases are safe before normalization: a zero-cost chore agent can take the rest; a zero-value cake agent can freeze with its old bundle; and the one- and two-agent additive bases preserve the guards. The positive-buffer lower bounds prevent an unhandled zero normalization inside a pending transfer. Thus the `n(n−1)` potential bounds all nontrivial iterations across population reductions.

### Conditional success and total accounting

The parameter substitution makes the five repair failure groups total less than `1/64`. Snapshot has success probability at least `(47/64)(31/64)>1/4`. These bounds are uniform conditional on the complete past at the appropriate fresh-trial boundaries. Geometric tails consequently apply without independence between requests or retries.

Each iteration requests one Snapshot, at most two Shrinks, and one final Repair, for fewer than eight expected full trials. Their caps include inner repair, rejected candidates/corrections, and fresh carving on a rejected Shrink. Recording every new endpoint for all `n` original observers, including frozen ones, accounts for the factor of `n` in queries. Cached sums avoid additional component-by-component oracle calls. This yields the displayed `96n²(n−1)m+O(n)` query and `48n(n−1)m+O(1)` Cut bounds, with `m=O(n¹⁸ log²(2n))`. The optional failure-reporting wrapper also uses fresh full-trial boundaries; it does not reuse an unconditioned success probability after a partially exposed trial.

## Independent checks and remaining limits

`upper_independent_checks/check_finite.py` uses exact rational arithmetic and a fixed seed. Its saved output is `upper_independent_checks/results.json`.

- Exhaustive three-label transport checks passed on 6,570 EF row/permutation states per preference direction. They include 104 cake and 76 chore states where a zero-residue old target maps to the observer, exercising the saturation exception.
- 8,000 transfer cases passed: 5,225 identity crossings, 658 nonidentity path rotations, and 2,117 second-shrink cases. Threshold equality cases and both ends of the permitted shrink interval are included.
- Exact parameter substitutions passed for original populations 3, 4, 5, 10, 100, and 1,000. The uniform algebraic bounds were also checked in the manuscript; testing these populations alone would not establish them.

No blocking issue remains unresolved from this audit. The proof still rests on mathematical reasoning about continuous measures, conditional expectations, and measurable choices; there is no full continuous formalization or executable implementation being certified here. Unrelated deterministic and lower-bound theorems were outside this review's scope.
