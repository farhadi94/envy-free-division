# Independent hard-family review of the fixed-selector candidate

I read the candidate mixed appendix and main mixed theorem, compared the actual TeX with the current submission, and checked the changed construction through finite-horizon hardness, failure retention, fixed-input averaging, expectation conversion and reflection. I did not edit the candidate. This is an internal mathematical review, not human peer review or a full Lean formalization.

## Verdict

Accepted within the stated scope, with no unresolved required finding. The two identified text repairs have been applied and reread: the sampling paragraph now places the positive support on the left, and the output-cover paragraph states transcript preservation in complete sentences. No theorem or construction change was required by this review. The companion receipt pins the exact reviewed source hashes.

## Checked proof bridges

1. **Fixed bracket-sign rule.** S_plus uses the rightmost root for B>=0 and the leftmost root for B<0. When B=0 only target zero is legal, so its reply is b. S_minus uses the opposite choices and replies a at B=0. The rule is a single function prescribed across profiles; there is no algorithm-tape-dependent selector choice.

2. **One-sided root preservation.** If F'>=F and equality holds at a,b,r, then the bracket sign, legality and old root equation persist. For B>=0 there can be no later root because F-c>0 after the last root; for B<0,t<0 there can be no earlier root because F-c>0 before the first root. The t=0,B<0 case returns a. At t=B>=0 the last root is b; at B=0 the same endpoint argument applies. Zero-length brackets are harmless. The existing minimum-over-compact-interval proof establishes Borel least-root selection, and reflection establishes greatest-root selection.

3. **Coarse insertion.** The existing +left/-right pulses already have globally nonnegative cumulative contribution. They preserve old protected cumulative values, every protected interval's restriction, total one, and the distinguished row. Thus the coarse obstruction can be maintained without changing the canonical rule.

4. **Query protection.** Row groups remain frozen according to the first k-1 replies. The current row is unchanged, while earlier rows retain every old selected root by the one-sided lemma. The cover's probability loss is measured in the original tape law. Histories ending in errors or query-free nonreturn are retained. Output covering adds only further upward cumulative perturbations and hence preserves the old query transcript as required.

5. **Oriented random pairs.** The supports around X_r and Y_r are disjoint and spatially ordered within their corridor. Choosing the left support positive makes every cumulative increment nonnegative, including when X_r is to the right of its anchor. The event of different owners is unchanged by swapping positive and negative supports. The amended purity event correctly concerns I_r, since K_r is already pure on the retained output set regardless of its sign.

6. **Preservation of failure and averaging.** For the last separated pair, the positive owner's label replaces the old unconditional label A(X_r). The gain is at least alpha*M_r for every observer except that positive owner. The same earlier-pair bound and mass hierarchy imply failure; coassigned pairs cancel. Consequently no previous error is repaired. Query coordinates lie in protected intervals and, on the replay event, avoid each selected corridor. The upper indicator Z remains measurable on the fixed base tape/sample product space; averaging selects one fixed profile before the tape. No profile is selected separately for individual executions.

7. **Expected cost.** The guard wrapper still uses at most two actual queries per attempted original call. Since the canonical rule is tuple-based, extra Eval calls do not change the simulated Cut replies. The success-within-q event is therefore the same. The unconditional inequality E[Q]>=(q+1)(p-delta) proves an unbounded supremum over fixed profiles, not necessarily one input of infinite expectation.

8. **Reflection.** Reversing [a,b] maps the target t to B-t and reverses the order of all roots. It maps S_plus to S_minus for both signs of B. The endpoint cases t=0 and t=B, and B=0, are included. One Eval supplies B and one Cut implements the reflected query, giving the stated factor-two cost. Signed values, net-one normalization, finite piecewise constancy, completeness and the fairness comparison are preserved.

9. **Restricted pure-leftmost consequence.** A strictly positive legal target implies B>0, on which S_minus is exactly leftmost. Zero-target leftmost replies are always a and can be simulated locally. This establishes the corollary for algorithms using only nonnegative targets. It does not establish unrestricted always-leftmost hardness. The text correctly retains that limitation.

## Resolved findings

- HF-1 resolved: the sampling subsection now says equal opposite pulses are placed near X_r and Y_r with the positive support on the left. This agrees with the actual construction when either point is leftmost.
- HF-2 resolved: the output-cover paragraph now states that every retained query history is preserved and every retained output or nonreturn is unchanged, in two grammatical sentences.

## Independent checks and formal scope

The exact-rational fixtures in `experiments/hard_family_checks.py` check 4,382 bracket-sign root-preservation instances (including endpoint targets), 18,522 oriented pulse-dominance cases, all 27 coarse owner assignments in the pure-leftmost obstruction, and 1,539 post-split EF tables. These fixtures support the local reasoning and are not proofs of the continuous/randomized theorem.

The finite module `lean/HardFamily.lean` supplies an orientation-invariant wrapper around the prior no-repair certificate, the explicit coarse-obstruction/post-split-EF counterexample, and the bounded-cumulative perturbation estimate. Its formalization does not include the continuous root selector or probability construction. The final compilation receipt is recorded separately.
