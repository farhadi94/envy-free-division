# Independent audit of `QueryProbability.lean`

**Verdict: pass for the stated supporting probability results. No repair is required.** I read all 248 lines and all 15 theorem statements and proofs, checked the relevant mathlib integral interfaces, and independently compiled the source with an axiom check for every theorem. The hypotheses do not assume the desired expectation or almost-sure finiteness conclusions.

This is an audit of the module and its use as a supporting interface. It is not a formalization or renewed audit of the complete randomized protocol, the mixed hard-input construction, or the full Appendix G probability proof. The probability-specific claims in `formal_scope.tex` accurately preserve that distinction.

## Independent compilation

I submitted the actual module source through `lake env lean --stdin`, followed by `#print axioms` for each of its 15 theorems. The command returned exit code 0 with no warnings or errors. Every theorem reports exactly the permitted axiom set:

`propext`, `Classical.choice`, `Quot.sound`.

The toolchain identifies itself as Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The dependency manifest pins mathlib v4.35.0 at `56a005855ea17e0b0958f73ec801ae140b0a1679`. I found no project axiom, `sorry`, `admit`, or `unsafe` declaration in this module. I did not run the full artifact verifier or claim that other modules passed this compilation.

The audited module SHA-256 is `c050c1da43d681952b4529a783dbb11efcf42ab70e26d27665c20cc37ea47241`.

## Statement and proof audit

### Successful tails and unconditional lower expectation

`success_tail_mass` decomposes `S` into the events `Q<a` and `a<=Q`, applies measure subadditivity, and derives `p-delta <= measure(successful tail)`. Its subtraction is truncated subtraction in the nonnegative extended reals. The lemma itself needs no measurability hypotheses because it only uses measure monotonicity and subadditivity; the subsequent integral lemmas explicitly require measurable `Q` and `S`.

`successful_cost_tail_le_lintegral` constructs the actual measurable indicator of `S intersect {a<=Q}`. It integrates the pointwise bound `a*indicator <= Q`. The integral is over the entire sample space, so it includes costs on incorrect returns and nonreturning runs. No conditional-on-success expectation is substituted.

`expectation_lower_from_success` combines these two established inequalities. It contains no assumed expectation bound. Allowing infinite `Q`, infinite integrals, and truncated subtraction causes no invalid cancellation. The indicator integral correctly uses the extended-real convention `infinity*0=0` on null events.

`enat_lt_successor_iff` separately handles an infinite extended-natural count and a finite natural count. It proves the exact equivalence

`Q < q+1` if and only if `Q <= q`.

The extended-natural expectation theorem consequently obtains the precise `(q+1)*(p-delta)` factor. It does not assume that the count is finite on every outcome, that the protocol terminates, or that its expectation is finite. The natural-count specialization is also sound; finite counts at every outcome can still have an infinite integral on an infinite probability space.

The semantic meaning of `S` as a legal correct finite return is supplied by the caller. The inequalities do not require the extra relation `S subset {Q<infinity}` to be valid, so its absence is not a hidden weakening of the claimed lower bound. For the manuscript's actual execution, that relation holds anyway. Finite-query nonreturn can and should retain its actual finite query count while lying outside `S`.

### Supremum over fixed inputs

`supremum_expectations_eq_top` takes an arbitrary family of measurable counts and success sets on a common tape space. For every cutoff, its `hhard` premise supplies some fixed index with a small successful short-run event. The theorem applies the preceding expectation inequality to that index, bounds it by the family supremum, and uses the positive gap `delta<p` to force the supremum to infinity.

The index is allowed to depend on the cutoff, exactly as in Appendix H. No single index is asserted to have infinite expectation. No common measurability of the entire index family, no probability distribution over input indices, and no measurable selector of hard inputs is assumed. The supplied premises concern success events and finite-horizon events, not the desired expectation conclusion.

### Actual survival indicators and the tail-sum formula

`survival T n` is the event `n<T`, for an extended-natural waiting count. `measurable_survival` derives its measurability from that of `T`. `enat_eq_tsum_tails` proves the pointwise identity by separate finite-count and infinite-count cases. A finite count `k` contributes exactly `k` ones, while an infinite count contributes an infinite sum.

`lintegral_enat_eq_tsum_survival` then applies mathlib's `lintegral_tsum` to the actual measurable survival indicators. It does not assume summability, finite expectation, or almost-sure finiteness. This is a genuine nonnegative-integral tail-sum theorem, not finite event arithmetic with a numerical expectation supplied as a premise.

The zero-attempt case is handled correctly: `T=0` contributes zero to every survival term. For a positive waiting count, the `n=0` survival event supplies the first unit, so there is no off-by-one error.

### Contraction, finite waiting, and per-attempt cost

`survival_mass_le_geometric` proves the geometric tail by induction from the explicit recurrence

`measure(T>n+1) <= r*measure(T>n)`.

Independence of attempts is not assumed. The recurrence is the probability interface supplied by the manuscript's uniform conditional acceptance bound; this module does not itself prove that conditional acceptance bound or its conditional-expectation derivation.

`waiting_time_expectation_le` uses the proved tail sum, the geometric tail, and the extended-real geometric-series identity to obtain

`integral T <= (1-r)^(-1)*measure(T>0)`.

`probability_waiting_time_expectation_le` uses the probability-space normalization to remove the last mass factor. These theorems deliberately allow any nonnegative extended `r`. When `r>=1`, truncated `1-r` is zero and the inverse bound is infinite; no finite expectation is being claimed in that case. For the manuscript's strict contraction factors, the bound is finite.

`waiting_time_finite_ae` explicitly requires `r<1` and a finite measure. It first derives a finite integral from the preceding bound, then uses the measurable-function theorem that finite nonnegative integral forces the infinite-value set to have measure zero. It does not assume almost-sure termination or finite expectation. Its conclusion is precisely `T` finite almost everywhere.

`expected_cost_le_of_attempt_budget` integrates the explicit pointwise budget `C <= b*T`. This is a deterministic accounting hypothesis, not an expectation hypothesis. It covers all outcomes and all rejected attempts. It correctly leaves overhead not covered by that budget to a separate caller bound, as Appendix F does with its additive initial/final costs.

One scope detail is useful for consumers: this cost theorem does not require `Measurable C`. Mathlib's `lintegral` is defined as the lower Lebesgue integral even for a nonmeasurable function, and monotonicity proves the displayed inequality in that greater generality. When it is called an expected query cost, the actual execution's measurable cost must supply the probabilistic interpretation. That measurability is available from the protocol model; adding it as an unused theorem premise is not needed for soundness.

Similarly, finite `T` alone is not an abstract assertion that an arbitrary implementation returned. For the waiting-time application, `T` must denote the index of the accepted return, with infinity if no such return occurs. Appendix F separately establishes that each finite trial terminates. Together those facts make finite `T` imply an actual finite return. The module does not conceal this semantic bridge inside its hypotheses or claim to prove it.

## Comparison with the manuscript

**Appendix H, “Expected queries with a positive success probability.”** The mapping is exact: `Q` is the original attempted-call count, `S` is legal correct finite return, and the guarded finite-horizon construction gives `P(S and Q<=q)<=delta` for a fixed input/selector pair. The hypothesis `P(S)>=p` concerns that same pair. `enat_expectation_lower_from_success` derives the stated `(q+1)*(p-delta)` inequality, and `supremum_expectations_eq_top` derives an infinite supremum over fixed pairs. The hard-pair construction, guard simulation, selector behavior, and event equivalence remain handwritten hypotheses, as the module header and formal-scope section say.

**Appendix F, “Composition and completion.”** The interface bounds give failure factors at most `3/4` for Snapshot and `1/64` for Shrink or Repair, conditional on the preceding history. Their iterated-conditioning consequence is the survival contraction required here. The waiting-time bounds therefore give at most `4` and `64/63` attempts, respectively. The manuscript combines one Snapshot, at most two Shrinks, and one Repair to get `4+3*(64/63)=148/21<8`; then it sums over the separately bounded number of reached iterations and charges the deterministic per-trial budgets. The module proves the waiting/integral components, not that full adaptive composition or the geometric construction supplying acceptance. The manuscript explicitly proves finite computation inside a trial, so the almost-sure finite-waiting interpretation is appropriate.

**Appendix G.** The new module does not formalize its continuous replay, failure-retention, common-width, or Tonelli hard-input argument. The existing finite/scalar lower-bound certificates and the targeted mathematical audit remain distinct. `formal_scope.tex` correctly leaves the lower-bound transcript constructions, dominated convergence, and fixed-input construction outside Lean.

The probability-specific formal-scope claims are accurate: actual event-to-integral lower bounds, tail sums, geometric waiting-time bounds, and the family-supremum conclusion are now checked. No complete main theorem is claimed to be formalized.

## Verdict and limits

No theorem-level defect, circular expectation premise, hidden finiteness premise, count-at-infinity error, or mismatch with the stated F/H uses was found. The application boundaries above are necessary scope descriptions, not repair requests.

**Final snapshot closure:** accepted within this probability-module scope, with **zero unresolved required findings**. `review/final_snapshot.json` has SHA-256 `b446afd3d9512f9e684bfb406fdc46324c4b01fa3b46e470bc74596b2b1c7f6b` and identifies the 71-page PDF `fca21e71706d17b07a0fc272bbeabcd0e7ace0317d228ef48c7527d778f64295`. The module, inspected F/H/G sources, formal-scope text, and dependency metadata are unchanged from the completed independent audit. The final PDF's probability-coverage and exclusion clauses were checked on page 71. The 15-theorem independent compilation remains applicable; it was not repeated. The reported global audit of 31 modules is separate and was not rerun by this reviewer.

The accompanying JSON receipt pins the module, targeted manuscript passages, dependency metadata, compiler result, and per-theorem axiom results. Historical receipts and manuscript sources were not edited.
