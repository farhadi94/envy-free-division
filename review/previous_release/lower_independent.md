# Independent audit of the general randomized exact-EF lower bound

**Status: no substantive mathematical gap or counterexample found.** The argument establishes the stated unconditional lower bound on the uniform profile, for each fixed positive success probability, under the stated measurable, input-independent random-tape and ordinary interval-query model. The result covers both cake and chores and arbitrary finite output fragmentation. This is an independent mathematical review, not a full machine verification of the probability theorem.

There are no blocking, major, or unresolved findings. One optional wording clarification was adopted in the final snapshot, as recorded below. I did not edit the manuscript or another reviewer's files, use earlier reviewer conclusions, or use author notes as evidence.

## Sources and scope

I read all 350 lines of `paper/sections/nonnegative_lower_proof.tex`, including the entire replay, measurability, old-failure retention, and limiting arguments. I also read the complete `model.tex`, `general_results.tex`, and `lower_overview.tex`. I checked the corresponding PDF text: the model on page 3, Theorem 2.3 on page 4, the overview on pages 6–7, and all of Appendix G on pages 52–57. The theorem, hypotheses, and displayed inequalities agree between the PDF and TeX. On the final rebuild, I compared the scoped PDF sections against the original extraction and verified that the only Appendix G change is the adopted replay-wording clarification; the model and lower-overview body are unchanged. Reversing that one TeX replacement reproduces the original reviewed source hash exactly. The main theorem's endpoint-freedom sentence was subsequently rephrased equivalently, as described below; its quantitative claim and hypotheses are unchanged.

For the formalization boundary I inspected `R8Lower.lean`, `SubmissionMonteCarlo.lean`, and `formal_scope.tex`. The relevant Lean statements are finite event accounting and scalar algebra with explicit hypotheses. I did not treat them as formalizations of continuous pulse geometry, adaptive execution replay, measurability, dominated convergence, or averaging over fixed inputs. I did not rerun Lean: `lean` and `lake` were absent from this review environment's command path, and neither existed under `~/.elan/bin`.

I checked the model and quadratic theorem in the archived primary PDF of Procaccia (2009). Its model already permits a finite-union allocation to be output for free. The current manuscript's narrow statement that the new result extends the randomized success/accounting scope, rather than raises the asymptotic order, is consistent with that source. I did not conduct an exhaustive novelty search.

Exact source hashes, reviewed scope, findings, and check results are recorded in [the JSON receipt](lower_independent.receipt.json). The final reviewed PDF is `8370c1da9ee87aedfeec7bfd0472bb63420acbb84f38427a2243baaaeb128a90`, matching `review/final_snapshot.json`. The introduction/table wording “even with arbitrarily many output cuts at no query cost” accurately describes the permitted extra freedom, with the precise model retaining the finite-output restriction. The audit applies to the recorded final hashes.

The final academic-exposition follow-up was checked against the preserved preceding checkpoint. The model, Appendix G, lower-overview source, and inspected Lean sources are unchanged. The revised introduction's lower-bound paragraph, the heading “Randomized lower bound: indistinguishable perturbations,” and the lower-bound related-work paragraph accurately describe the audited result and do not expand its formal claim. The theorem now permits “allocations with arbitrarily many intervals, choosing their endpoints without oracle calls”; this is equivalent to the previously audited allowance because allocations remain finite unions by the model. Reversing the two endpoint-freedom wording replacements in `general_results.tex` reproduces that file's prior hash exactly. The complete rendered Appendix G is textually identical to the preceding reviewed PDF. No new finding arose; the unchanged full proof was not redundantly reaudited.

## Mathematical audit

### Quantifiers and admitted inputs

The protocol is fixed before the construction, with an input-independent tape on an arbitrary fixed probability space. The only cross-input assumption is success probability at least `p` on **every** normalized finite-step profile in the density window. No common expected-query bound on the perturbed inputs is used. If the uniform expected cost is infinite, the conclusion is already true; otherwise the uniform execution has finitely many answered queries almost surely.

For fixed `w` and an error allowance, the proof chooses one deterministic dyadic `h` from the uniform execution law. Only afterward are the independent observer, center, displacement, and tape sampled. Dependence of this deterministic width on the fixed protocol is legitimate for a universal lower bound. The proof never chooses an input after seeing the realized tape. Letting the error allowance tend to zero is legitimate because the bound's other quantities, including the uniform expected cost, do not change with `h`.

Every constructed density is normalized: the two circular arcs have the same length `h`. The density takes only values in `{1/2,1,3/2}`, including overlap cancellation. Wrapped arcs produce finitely many ordinary intervals. Thus every realization, including overlapping or coincident pulses, belongs to the promised finite-step class. The proof does not need a positive probability of nonoverlap; the successful decoder event plus endpoint avoidance already supplies the geometry it uses.

### Exact replay and query accounting

An Eval reply is fixed by one interval integral. A successful Cut is fixed by the integral on `[a,z]`, where `z` is its old returned root. Because the perturbed density is at least `1/2`, the cumulative value is strictly increasing. The old `z` remains the unique root and lies in the unchanged bracket, proving legality even if the full bracket value changes. This handles zero targets, degenerate brackets, and arbitrary requested endpoints. No second bracket-total charge is needed for a successful Cut.

For an unavailable-target reply or a terminal illegal target, preserving the actual bracket total preserves the relevant comparison, without pretending that the total was disclosed to the algorithm. Valuation-independent syntax errors need no interval. A legal success cannot contain a prior illegal request, so stopping at the first such request preserves successes and reduces cost. Consequently the determining-interval count is at most `Q+J`, and `E[J] <= 1-s`.

Replay on a fixed tape also handles a run that diverges after finitely many queries: identical replies and the same tape yield identical query-free computation after the last reply. It does not require detecting that last query or deciding divergence. Counting all attempts, as the main model does, only increases cost relative to the more permissive answered-query convention analyzed in Appendix G.

### Detection and arbitrary output fragmentation

For an ordinary interval, the circular symmetric difference under displacement `u` has measure at most `2|u|`; averaging `U ~ Unif[-w,w]` gives detection probability at most `w`. Averaging over the independent observer gives at most `(w/n)(Q+J)` over the entire fixed uniform transcript. This is a union bound on fixed baseline queries, not a conditional independence claim about adaptive queries after previous nondetection.

For any equal-length partition, conditionally on `X=x`, `Y` is uniform on a circular interval of length `2w`. Its chance of remaining in `x`'s entire bundle is at most `(1/n)/(2w)`. This uses bundle measure only and is valid for arbitrarily fragmented finite unions. The uniformly selected changed observer is independent of the centers and the baseline partition, so excluding the single favorable owner contributes exactly the factor `1-1/n`.

The finite endpoint list includes query endpoints, output endpoints when appropriate, and `0,1`. Although its random length can have infinite expectation, `min(1,2hN)` tends pointwise to zero and is bounded by one. Dominated convergence therefore supplies a single width with arbitrarily small endpoint loss. On endpoint avoidance and nondetection, both pulse contributions to every determining interval cancel exactly. On a successful baseline output with different center owners, the affected values are exactly `1/n + h/2`, `1/n - h/2`, and `1/n`. The changed observer has strict cake envy unless it owns the positive pulse, or strict chore envy unless it owns the negative pulse.

### Retaining prior failures

A legal complete but unfair uniform output has positive length gap `Delta = max length - min length`. The pulse perturbation changes an individual set's value by at most `h/2`, and a comparison by at most `h`. Thus the old offending comparison survives when `Delta > h`. There is no assumption of a uniform positive gap: the probability of `0 < Delta <= h` tends to zero by dominated convergence. Invalid allocations, terminal illegal calls, and query-free divergence remain failures by exact replay.

These old failures and the decoded baseline successes are disjoint. Subtracting detection and the two small-width losses yields the stated inequality

`1-p >= 1-s + s*A_w - (w/n)*(E[Q]+j) - eta`,

where `A_w = (1-1/n)*(1-1/(2nw))`. No independence of the subtracted loss events is needed. The estimate remains valid when `A_w` is negative.

The terminal illegal request is absorbed correctly: with

`K = (n/w)*(1-A_w) = 1/w + (n-1)/(2*n*w^2) >= 1`,

the excess term `(1-s)*K-j` is nonnegative because `j <= 1-s`. Dropping it and sending `eta` to zero gives

`E[Q] >= (np-1)/w - (n-1)/(2*n*w^2)`.

This is the essential step that allows every fixed `p>0` and removes the otherwise possible additive one-call loss.

### Measurability and fixed-input averaging

The measurability discussion is sufficient for the stated model, interpreting measurable rules jointly in the tape and prior finite transcript. Translated arc indicators are continuous in `L1`, hence their interval integrals vary continuously with the centers and endpoints. The common density lower bound makes inverse cumulative roots continuous on the legal domain. Finite transcript and finite output strata then give measurable success, endpoint lists, and gaps. Finite-query nonreturn strata can be measured without the final query index being a stopping time.

The product integration only needs measurable sections on the arbitrary tape space; it does not invoke a regular conditional distribution there. For each fixed pulse tuple, the assumed protocol guarantee bounds its tape failure probability by `1-p`. Tonelli therefore gives the required bound for the average perturbed failure probability. Infinite perturbed query costs cause no problem because this step concerns only a bounded failure indicator.

### Optimization and expected-query conclusion

Writing `F(w) = (np-1)/w - (n-1)/(2*n*w^2)`, the unconstrained positive maximum for `np>1` is attained at

`w* = (n-1)/(n*(np-1))`.

The condition `w* <= 1/2` is exactly `np >= 3-2/n`, and substitution gives `n*(np-1)^2/(2*(n-1))`. An independent square completion also confirms global optimality:

`n*(np-1)^2/(2*(n-1)) - F(w)`

`= (n*(np-1)*w-(n-1))^2/(2*n*(n-1)*w^2)`.

The manuscript correctly refrains from substituting an inadmissible optimizer. Its all-window inequality remains valid for all other parameters, with the trivial zero lower bound available. The `p=2/3, n>=4` specialization is correct. For every fixed positive `p`, taking `n >= ceil(3/p)` even gives the explicit asymptotic consequence `E[Q] >= (2/9)*p^2*n^2`.

## Finding and recommended action

**L-01 — resolved optional wording clarification; no mathematical effect.** The original `nonnegative_lower_proof.tex:105-108` said “subsequent outcome” in the replay lemma. This means the returned object and termination behavior, not its fairness classification: the later proof correctly changes a successful uniform allocation into an unfair perturbed allocation. The final snapshot now says “and returned object or nonreturn behavior are unchanged.” I verified this exact replacement in both TeX and the final PDF. The proof already made the intended meaning explicit at lines 116–120, so the clarification repairs no mathematical gap.

No substantive corrective action is required for the audited lower-bound argument.

## Independent finite checks and limits

[The independent script](lower_independent_checks/check_lower.py) uses standard-library exact rational arithmetic. [Its result file](lower_independent_checks/checks_result.json) records successful checks of:

- 4,360 equal-length owner words, including highly fragmented outputs, at 27,840 continuous collision-probability cases. The integration over continuous centers and displacements is exact for the grid-cell words, not sampling.
- 192 ordinary-interval separation probabilities.
- 1,024 normalized two-pulse profiles, 32,640 exact Eval/Cut replay cases, and two successful Cuts whose full bracket totals change.
- 36 wrapped or overlapping pulse profiles and 2,926 direct cake/chore decoder checks.
- 864 retention/terminal-request accounting cases and exact optimization identities on a rational parameter grid.
- A heavy-tailed endpoint count with infinite mean, illustrating that the bounded small-width loss still tends to zero.

These checks are falsifier searches for the finite geometric and arithmetic interfaces. They do not prove the general adaptive probability theorem. The latter conclusion rests on the line-by-line mathematical audit above. I found no missing assumption beyond those already stated: input-independent jointly measurable protocol rules, ordinary Eval/root-only Cut access, finite interval-encoded output on return, success on the whole admitted class, and exact envy-freeness.
