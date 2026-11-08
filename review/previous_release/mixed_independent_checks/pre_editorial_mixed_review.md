# Independent review of the mixed impossibility theorem

**Verdict:** I found no blocking mathematical gap or counterexample to Theorem 2.4 (`thm:mixed-mc`) under its stated oracle, measurability, output, and normalization assumptions. I checked the complete current Appendix H proof, rather than inferring its validity from the finite Lean results or earlier reviews. The positive-net reduction correctly transfers the combined comparison lower bound to the sign-correct relative multiplicative definition. The argument also proves the separate additive claim for every fixed tolerance below one.

This review is limited to the mixed theorem and its supporting presentation. It is not a verdict on the paper's other main theorems. No prior author notes or review conclusions were used. The receipt `mixed_independent_receipt.json` pins the final reviewed source versions, coverage, checks, and limitations. `mixed_independent_checks/source_hashes_initial.json` also preserves the initial versions read before the two wording clarifications described below.

The reviewed material comprises the mixed definition and theorem in `paper/sections/general_results.tex`, every line of `paper/sections/mixed_lower_proof.tex`, `mixed_overview.tex`, and `figures/mixed_pulses.tex`; the relevant shared model, abstract, introduction, comparison table, related-work paragraph, and formal-scope statement; and both `MixedApproximation.lean` and `R6MixedMonteCarlo.lean`. I read the rendered main statement and the complete Appendix H text in `paper.pdf`, and visually inspected the rendered pulse figure. These occupy pages 4–5, 7–8, and 57–66 of the final 67-page PDF, SHA-256 `2cb128afb74e0bd288a08db4db36fcb5a1a4bb4b8165e506254a5544544aa7c8`. A complete diff of extracted Appendix H text between the initial and final PDFs confirmed that its only revision was the endpoint-exemption clarification below.

**The exact claim and quantifiers.** Fixing (n\ge3), (p>0), and (0<\alpha\le1), the claim rules out a bound uniform over admissible profile/selector pairs for a single protocol that succeeds with probability at least (p) on every such pair. The combined Appendix H statement uses (0\le\varepsilon<\alpha\le1) and net totals one. Its order is

\[
\forall\mathcal A,\ h,\ \delta>0\quad
\exists(P,S)\quad
\Pr_\omega[\mathcal A\text{ succeeds on }(P,S)]\le\delta.
\]

The hard pair may depend on the entire strategy and its tape law. It does not depend on the realized tape. For the expected-query conclusion a different fixed pair may be selected for each cutoff. Neither a single pair with infinite expectation nor an input-independent bound on the number of density steps is asserted. The proof uses no common total-variation bound, no bound on expected output fragmentation, and no countable positive-probability witness extraction.

The oracle restriction is substantive: Cut targets must lie between zero and the bracket's net value, and a fixed Borel selector may choose any root. The proof does not establish the corresponding result for a prescribed first/last root, a richer query returning extra information, or an oracle accepting every target attained somewhere inside a bracket. Its own final paragraph accurately states the extremal-root and variation-relative limitations.

1. **Signed relative comparisons and the positive-net equivalence — verified.**

   The main definition is (y-x\le(1-\alpha)\max\{|x|,|y|\}). For (y\ge0), it is exactly (x\ge\alpha y); for (y<0), it is exactly (x\ge y/\alpha). The same-sign calculations, the always-satisfied case (x\ge y), and the forbidden crossing (x<0<y) are all correct. At (y=0), the condition forces (x\ge0); at (x=0<y), it fails for every positive factor. At (x=y=0), it holds. At factor one it reduces to exact envy-freeness.

   The negative branch is essential: with factor (1/2), (x=-2,y=-1) satisfies the relative comparison but fails the usual cake comparison. Consequently, simply writing the cake inequality on the whole signed domain would have been incorrect. The manuscript does not make that substitution. Instead, for each observer, completeness and strictly positive whole value imply that some bundle has positive value. Comparing against it forces strictly positive own value under either proposed global predicate. Comparisons to negative bundles are then automatic and the remaining comparisons are the nonnegative cake inequalities. Summing the comparisons with the other (n-1) owners gives the stated lower bound (v_i(A_i)\ge\alpha v_i(I)/(n-1+\alpha)).

   The reduction applies to every complete allocation of every constructed profile because every perturbation has total zero in every row. Thus a violation of the combined inequality at tolerance zero really excludes the relative guarantee; it is not a change of fairness model. Taking factor one yields exactly the stated additive guarantee. The combined inequality for intermediate positive tolerance is an auxiliary predicate; the paper correctly does not call it the general signed relative definition.

   On nonnegative cake values the cited usual multiplicative convention agrees with Barman–Kulkarni, page 16:2, which explicitly uses the comparison (v_i(I_i)\ge\alpha v_i(I_j)). I checked the [primary ICALP paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol261-icalp2023/LIPIcs.ICALP.2023.16/LIPIcs.ICALP.2023.16.pdf). This citation supports that convention, not the new signed definition or the continuous lower-bound proof.

2. **Selectors and separated covers — verified.**

   The selector patch tests old legality and the new root equation, retaining valid old roots on new-legal queries and otherwise using the least new root. The least-root construction is Borel: for a fixed continuous cumulative function the minimum of the displayed continuous residual over a compact moving interval is continuous after the stated change of variable. Rational thresholds characterize its strict sublevel sets. Zero targets and degenerate brackets cause no exception. Every actual replay use separately preserves bracket legality as well as the old root equation, so no use relies merely on the continued existence of an old root for an illegal new tuple.

   The separated-cover lemma is valid for arbitrary finite coordinate laws, including singular laws and atomic laws. Its mesh endpoints avoid the countably many atoms; shrinking finitely many neighborhoods around these endpoints has arbitrarily small coordinate-law loss. Uniform continuity of the atomless variation cumulative gives the per-interval variation ceiling. Positive gaps and separation from the cake endpoints can be retained. There is no unproved assumption that query or output coordinates have densities.

3. **Coarse obstruction and insertion — verified.**

   Initially, with one whole cell of value one, an empty recipient has comparison exactly α toward its owner. For insertion, the two selected rows other than the distinguished row exist precisely because (n\ge3). If the children are coassigned, all old bundle values are recovered. Otherwise at least one of the selected rows is not the left owner. For that observer the left owner's value is at least (L_k+M_k-H_k), whereas its own value is at most (H_k), since the right child is nonpositive. The stated forcing inequality therefore gives comparison at least α. Both mass requirements can be satisfied by one finite positive mass, even for arbitrarily small positive α.

   The geometric preservation claims also hold. Reserving all intervals before insertion leaves nonempty adjacent gaps for every support. The supports for an insertion lie in one current coarse cell and avoid every reserved interval. Relative to every already inserted representative, both supports lie on the same side of its protected interval, so the full cumulative contribution there is zero. New reserved intervals need only retain their restrictions until inserted, while the distinguished row remains unchanged globally. This distinction is enough for the later induction; the proof does not mistakenly assume all new cumulative levels are already fixed. Finite insertions preserve finite piecewise-constant densities and row totals one.

4. **Protection of legal adaptive queries — verified.**

   The stage-(k) row groups are determined from the preceding (k-1) replies and the tape. Processing a different row group cannot change those histories. The next reply of an unprocessed group may change, and its coordinate law is deliberately measured only when that group is reached. This avoids using a stale root distribution. The current addressed row is unchanged by its own insertion, and the selector patch therefore preserves its current reply. Afterward the reply's coordinates are protected for all remaining insertions.

   Coordinate losses are charged in the original tape measure, so the (nh) losses sum to at most the prescribed budget without conditional-probability inflation. A retained trace contains at most (3h) occupied old intervals. Early return, abort, and nontermination after finitely many calls are all preserved by equal past replies. The proof never assumes correctness or a transcript certificate during this construction.

5. **Output coverage and order of choices — verified.**

   The old interval budget is chosen before query protection. Only after the resulting pair is fixed is the finite boundary-count quantile (K) chosen. Finiteness on each return, rather than an expectation bound, suffices for that quantile. The sum of at most (K) boundary pushforwards is a finite measure, so the cover lemma applies. The additional intervals have variation at most \((\alpha-\varepsilon)/(4(K+1))\) under the pre-insertion profile, and their restrictions are unchanged when installed. All old cumulative functions survive, so the same outputs and nonreturns are retained, although their values may change.

   This yields the claimed retained mass (1-3\delta/8). Every final coarse cell has exactly one boundary-free open gap, including the first and last cells. The anchors are fixed in the final enlarged geometry. No anchor or perturbation support is selected after seeing the realized tape. Correctness is evaluated under the resulting base profile (P_2), rather than assumed to persist from the earlier profile (P_1).

6. **Variation-weighted ownership discrepancy — verified.**

   Coarse ownership is determined by the owner on each coarse cell's gap. It agrees with the actual allocation outside protected intervals, and also in each protected interval with no genuine boundary. At most (K) new intervals can contain a genuine boundary. The comparison-indicator difference has absolute value at most (1+\alpha\le2); hence their total contribution is less than half the gap \(\gamma=\alpha-\varepsilon\). The old-interval contribution is bounded by twice the old discrepancy's sum-variation measure. The difference between a coarse comparison at least α and a correct comparison at most \(\varepsilon\) consequently forces \(\nu(D_A)\ge\gamma/4=c>0\).

   This controls mass of disagreement, not number or spacing of old-interval boundaries. Exceptional singleton endpoint labels disappear under the explicitly stated canonicalization. The case (V<c), including no old intervals or horizon zero, is correctly disposed of before division by (V).

7. **Sampling, replay, and constants — verified.**

   Under the fixed base profile, independent samples from \(\nu|_O/V\) hit the discrepancy with probability at least (c/V) for each fixed correct returned output. With \(L=\lceil(V/c)\log(8/\delta)\rceil\), complete coassignment has probability at most \(\delta/8\). The sampling law is not conditioned on the query transcript.

   For each retained tape, the variation mass of all occupied old intervals is at most (3he). The replay-loss bound is therefore (3heL/V). Since (V\ge c), \(L/V\le(a+1)/c\), and the chosen (e=c\delta/[24(h+1)(a+1)]\) gives replay loss at most \(\delta h/[8(h+1)]<\delta/8\). This cancellation resolves the potentially circular dependence on the number and variation of old intervals. No bound on total variation independent of the input is used.

   Each final pulse corridor meets only its own sampled old interval and its immediately adjacent final gap. On the replay event all query coordinates are outside those old intervals and outside the gaps, so every cumulative value needed for Eval, Cut legality, and the old selected-root equation is unchanged. New roots may appear, which is harmless for the permitted patched selector.

8. **Pure physical supports and preservation of incorrect outputs — verified.**

   Both support radii are positive on the sample space and are measurable functions of the sample and fixed geometry. Negative supports stay in boundary-free gaps and are always pure on retained finite returns. For each fixed finite output, the atomless sample law avoids its finitely many genuine boundaries almost surely, and positive supports become pure as their common width parameter decreases. The resulting product-space impurity event is measurable by finite endpoint comparisons. Dominated convergence supplies one deterministic width with product probability below \(\delta/8\); no width is chosen separately for each tape.

   The explicit mass choice has surplus

   \[
   \alpha M_r-(1+\alpha)(T+\textstyle\sum_{s<r}M_s)-\varepsilon
   =(1-\alpha)(T+\textstyle\sum_{s<r}M_s)+\varepsilon+2>0.
   \]

   For the largest split pair, any observer other than its positive owner receives comparison gain at least \(\alpha M_r\); the base and earlier-pair losses are bounded by the displayed \((1+\alpha)\) budgets. All later coassigned pairs cancel separately. Thus a split forces error irrespective of prior correctness. If none splits, every bundle value is unchanged. The assertion applies on the pure-support event; overlapping supports do not invalidate it because the individual signed measures still integrate additively. All profiles remain finite and net-total-one, even though their variation may grow arbitrarily.

9. **One fixed hard input and measurability — verified.**

   The selector is patched once against the fully perturbed profile, independently of the algorithm tape. On the joint replay event the entire finite trace, including nonreturn, is identical. The explicit (Z(\omega,\xi)) uses only random variables from the fixed base execution and finite geometric comparisons. Its base-correctness event is measurable because a fixed atomless profile's interval values are continuous functions of endpoints, after stratifying finite encodings by length.

   Pointwise final success is bounded by (Z): nonretention, replay failure, impurity, or a correct base return with all pairs coassigned. This last event really includes base correctness, preventing repair of previous failures from escaping the bound. The four estimates sum to (3\delta/4<\delta). Tonelli applied to this explicit majorant selects one sample whose section integral is at most \(\delta\). No joint measurability of the algorithm as a function of an abstract input profile, and no jointly measurable family of selector patches, is needed. Fixed-input measurability suffices for the selected pair's success probability.

10. **Transfer to unconditional expected queries — verified.**

    The syntactic guard checks brackets before querying. An extra Eval reveals the actual net bracket value and allows the restricted Cut legality test, yielding a pointwise-legal partial strategy with at most (2q) calls. Those Eval replies are hidden from the original procedure. Fixed tuple-based selectors return the same old roots despite the extra calls; a history-sensitive selector would require a different argument, but it is not the claimed model. The wrapper's correct-return event is exactly original legal success with attempted-call count at most (q). Nonreturn after finitely many queries remains a permitted failure.

    Applying finite-horizon hardness with \(\delta=p/2\) gives a fixed pair with success after (q) calls of probability at least (p/2). Hence \(\mathbb E Q\ge(q+1)p/2\), including unsuccessful executions. Allowing the pair to depend on (q) establishes an infinite supremum of expected costs. This is precisely the announced uniform-bound impossibility. At \(\varepsilon\ge\alpha\), giving the whole net-total-one resource to one owner satisfies the combined inequality without querying, so the strict parameter range is correctly identified.

**Checks and the limited role of Lean.** The independent exact-rational script passed 19,520 signed-pair cases, 9,300 positive-total utility-row cases, 8,635 exhaustive coarse ownership assignments across successive insertions, and 32,805 pure-pulse ownership patterns, including initially incorrect tables. Another 720 floating-point smoke tests checked the sampling/replay budgets. These finite probes are useful error detectors, not proofs of the continuous theorem.

The source-level Lean audit confirms that `MixedApproximation.lean` proves finite weighted coarse forcing, comparison bounds, common-pulse dominance and preservation of failures, the explicit mass inequality, positivity of the discrepancy budget, and the positive-total relative/cake equivalence. `R6MixedMonteCarlo.lean` supplies finite pulse identities, the largest separated pair, and finite event accounting. The weighted ownership-discrepancy theorem is a scalar implication from supplied entry bounds; it does not build the variation measure or the geometric discrepancy set. The continuous selection, coverage, replay, dominated-convergence, and integration arguments remain mathematical proofs in Appendix H. The manuscript's formal-scope limitation is appropriate. Fresh compilation of both reviewed files and their local `SubmissionMonteCarlo` dependency passed, using outputs in the reviewer-owned directory. An independent transitive-axiom audit passed for 48 theorem declarations in the two reviewed namespaces, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Results are recorded in `mixed_independent_checks/finite_lean_check.json` and its logs.

**Resolved wording findings.** Neither finding below was a theorem gap; the full proof already had the required properties. Both were sent to the coordinating reviewer, corrected there, and verified in the final TeX and rebuilt PDF. No unresolved finding remains from this review.

- The overview now qualifies preservation of incorrect outputs by the event that the query history is preserved and every support has one owner. Without that qualifier, the previous sentence was literally broader than Lemma H.8: an impure pulse can be split among several bundles and need not obey its table update. The proof correctly charges impurity to the exceptional event.
- Query protection now explicitly restricts coordinate pushforwards to \(U=(0,1)\setminus\bigcup_sJ_s\), exempting coordinates at 0 or 1. The previous phrase “outside the current protected intervals” omitted that harmless exemption, while the cover lemma itself is stated on (U\subset(0,1)).

No change to the theorem's sign convention, success quantifier, parameter range, hard subclass, root model, or expected-query conclusion is required by this review.
