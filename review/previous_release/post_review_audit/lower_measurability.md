# Targeted re-audit: lower-bound measurability and fixed-width comparison

**Result: the targeted interfaces are sound after the two measurability repairs recorded below. No counterexample to the lower-bound theorem was found under the now explicit protocol definition.** This conclusion comes from a new derivation of the relevant measurable maps, events, and limits, rather than reliance on the earlier acceptance report.

The audit covers Appendix G.6 and its dependencies in G.1–G.5: legal inverse roots; joint finite histories; finite-query nonreturn; finite-output and endpoint-size strata; a common deterministic pulse width; preservation of baseline failures; and fixed-input averaging. I reread the entire current lower proof for context. This measurability audit does not re-audit the other main theorems. The new `QueryProbability.lean` was subsequently audited and independently compiled in the separate [probability report](probability_independent.md). Historical reports and receipts were not changed.

**Final snapshot closure:** accepted within the stated scope, with **zero unresolved required findings**. The reviewed snapshot is `review/final_snapshot.json`, SHA-256 `b446afd3d9512f9e684bfb406fdc46324c4b01fa3b46e470bc74596b2b1c7f6b`; its copy in `review/post_review_audit/final_snapshot.json` is byte-identical. The final 71-page PDF has SHA-256 `fca21e71706d17b07a0fc272bbeabcd0e7ace0317d228ef48c7527d778f64295`. Current model, Appendix G, main-statement, and probability-module hashes match the already audited versions and the snapshot. The final PDF was checked for the joint-measurability model on page 3, its G.1 invocation on page 56, the fixed null-set extension and almost-sure replay qualification on page 59, and the formalization exclusions on page 71. No already passed proof or compilation was repeated for this reconciliation.

## Findings and adopted repairs

### LM-01: arbitrary modification on a null set is not generally measurable

The original G.4 sentence permitted defining the endpoint list “arbitrarily” on the null set of infinite-query tapes. The tape probability space was not required to be complete, so that universal statement was false.

A concrete counterexample uses `[0,1]` with its Borel sigma-algebra and Borel Lebesgue probability. Let `Z` be the null Cantor set and choose a non-Borel subset `V` of `Z`. A list equal to `(0,1,0)` on `V` and `(0,1)` elsewhere has a nonmeasurable length function, although it differs from a constant list only on the measurable null set `Z`. Such a `Z` can be the infinite-query event of a measurable protocol: make endlessly many legal calls on `Z` and follow any ordinary finite-query protocol off `Z`. Thus this pathology is compatible with finite unconditional expected query cost.

This was a genuine local measurability defect in the permissive wording, not a counterexample to the theorem. The proof needs only one measurable extension. The source now contains the exact repair:

> On the measurable null event of infinite-query tapes, define the list to be $(0,1)$. This fixed extension preserves measurability.

The subsequent replay claim now begins:

> Outside this null event, on $G_h\cap D^c$, ...

Both replacements were checked in the final audited TeX. They avoid relying on completeness and state the intended almost-sure scope of the finite-query replay lemma. **Status: resolved.**

### LM-02: the protocol convention must require joint measurability

“Measurable query, stopping and finite-output rules” naturally means joint measurability in the tape and transcript, but the initial model did not explicitly say so. Separate measurability would not justify G.6's adaptive composition step.

Here is a direct falsifier of that weaker interpretation. Take a Borel uniform tape `omega` in `[0,1]` and a non-Borel set `V`. Define a decision rule

`d(omega,r) = 1` exactly when `omega = r` and `omega` belongs to `V`.

For each fixed reply `r`, this is Borel in the tape, since its accepting section is a singleton or empty. For each fixed tape it is also Borel in `r`. Nevertheless, after the legal query `Eval([0,omega])` on the uniform profile, the reply is `r=omega`, and the resulting decision is `1_V(omega)`, which is not measurable. Hence sectionwise measurability alone cannot establish even measurable finite execution behavior.

The common model now gives standard Borel structures to finite transcript, query-action, and finite-output encoding spaces using countable disjoint unions over lengths and types. It explicitly requires the next-action rule to be jointly measurable in the tape and finite transcript. Its action types include requests, finite returns, and query-free nonreturn. G.1 explicitly invokes this convention and joint measurability of next-action and finite-output rules. **Status: resolved as a model-definition clarification.**

For the common model, the concise wording proposed during this audit was:

> By a measurable randomized protocol we mean one with an input-independent tape $(\Omega,\mathcal F,\mathbb P)$. Finite query/reply histories, query actions, and finite interval-output encodings carry their standard Borel structures, using countable disjoint unions over their lengths and types. The rule for the next action is jointly measurable in the tape and the finite history for the product sigma-algebra. Its action space includes requests, finite returns, and a symbol for query-free nonreturn; this convention does not require nonreturn to be decidable.

The adopted text states the same convention. Joint measurability here is with respect to `F` times the history's Borel sigma-algebra. It does not require the tape space itself to be standard Borel or complete.

## Independent derivation of the remaining interfaces

### 1. Interval values and legal Cut roots are jointly measurable

Fix `h` and one of the finitely many choices of perturbed observer. Write `theta` for the continuous pulse parameters and

`F_theta(x) = integral from 0 to x of f_theta`.

Translated circular interval indicators are continuous in `L1`. This includes wrapping at `0`, overlap, and coincident pulses. Therefore `||F_theta-F_theta'||_infinity` tends to zero with the pulse parameters. The uniform upper density bound `3/2` also controls changes in the query endpoints. In particular, interval integrals are jointly continuous in the pulse parameters and ordinary interval endpoints.

For a Cut, the legal domain is

`0 <= a <= b <= 1` and `0 <= t <= F_theta(b)-F_theta(a)`.

It is Borel (indeed closed on each fixed discrete-type stratum), since the right side is continuous. On that domain the root is uniquely

`z = F_theta^(-1)(F_theta(a)+t)`.

The lower density bound `1/2` yields an explicit continuity estimate. For two legal tuples and `delta = ||F_theta-F_theta'||_infinity`,

`|z-z'| <= 4*delta + 3*|a-a'| + 2*|t-t'|`.

To see this, apply the lower slope bound to `|F_theta(z)-F_theta(z')|`, substitute the two root equations, and bound `|F_theta(a)-F_theta'(a')|` by `delta+(3/2)|a-a'|`. The bracket endpoint `b` is needed for legality, but introduces no additional inverse term. This estimate covers zero targets, degenerate legal brackets, roots at bracket endpoints, and coinciding pulses. Thus the inverse is jointly continuous on its legal domain.

Totalize the oracle by tagging unavailable or illegal requests outside the legal domain. The tags are Borel comparisons and finite syntax/type checks. A root-only Cut reply plus these tags is therefore a jointly measurable oracle map. No root-selection theorem or measurability on an abstract space of all valuation profiles is needed.

### 2. Finite execution histories are jointly measurable

Let `H_k` be the Borel space of histories of `k` answered calls. Let `A` be the countable disjoint union of query actions, finite interval-output codes, and terminal/nonreturn types. The clarified model supplies a measurable next-action map from `Omega x H_k` into `A`.

On the product of the pulse-parameter space and the tape space, start with the empty history. At each stage, compose the next-action map with the current measurable history and the jointly measurable oracle response map. Appending a query/reply pair is Borel. On the complementary, terminated branches use a fixed dummy/cemetery state. Induction gives a jointly measurable finite history and a measurable event that the next answered call occurs. This argument uses product-sigma-algebra composition; no regular conditional distribution is invoked.

Including a query-free nonreturn type is not an assumption that an implementation can decide divergence. If internal computation is represented by countably many measurable steps, the event that a particular next action first appears at time `t` is measurable. A countable union over `t` gives its eventual action, and the complement is nonreturn. The abstract next-action map is a measurable semantic description, not a computable divergence test.

### 3. Finite-query nonreturn causes no hidden stopping-time problem

On the uniform input, let `R_k` be the measurable event that at least `k` calls are answered, with `R_0=Omega`. Then

`{Q=k}=R_k \ R_(k+1)` and `{Q=infinity}=intersection_k R_k`.

For each `k`, the event of a finite return with output-code size `m`, or of a first terminal illegal request, is a measurable type condition on the next action (and, for a target-dependent illegality, the measurable oracle flag). The finite-query nonreturn stratum is what remains of `{Q=k}` after removing the finite-return and terminal-request strata. All these sets are measurable. They do not require the last answered call to be an observable stopping time.

On a stratum with fixed answered count, terminal type, and output size, every determining interval endpoint is a coordinate of the finite history or terminal request. Output endpoints are coordinates of the finite return code. Whether that code is a complete partition is Borel: sorting its finitely many endpoints, or splitting into finitely many endpoint-order cases, reduces coverage and disjointness to finite comparisons. Even redundant interval representations cause no measurability problem; one can refine by all encoded endpoints or use finite inclusion-exclusion for union values.

Consequently the endpoint list `E` is a measurable map into the countable disjoint union of finite endpoint vectors. Its length `N` is measurable. The fixed `(0,1)` extension on `{Q=infinity}` closes precisely the null-set issue in LM-01. Since finite expectation makes that event null, `N` is finite almost surely, without an integrability assumption on `N`.

The output gap `Delta`, the successful-output owner map, and the detection/decoder events are also measurable. For definiteness, the owner at a boundary may be assigned by a fixed first-label convention from the finite output code; no arbitrary nonmeasurable boundary choices are needed. Detection can be expressed as a countable union over the measurable query-coordinate maps. Finite success is a countable union over the measurable return and output-size strata, followed by the finite value and envy comparisons. Its complement includes all nonreturn and illegal behavior.

### 4. One common width can be chosen before sampling either input or tape

The uniform execution law, its finite endpoint list, and its strictly positive wrong-output gap are fixed before selecting any pulse input. For each fixed `h`, the event that a pulse meets an endpoint is measurable by the construction above. Uniform center marginals give the pointwise bound

`P(G_h^c | omega) <= min(1,2*h*N(omega))`.

The right side tends to zero almost surely along dyadic widths and is bounded by one. Dominated convergence applies even if `E[N]=infinity`. There is no exchange of a limit with an unbounded endpoint-count expectation. Joint measurability in the width itself is unnecessary: only the countable dyadic sequence is used, on the same product probability space.

For a complete but unfair uniform return, `Delta>0`; therefore the events `W intersect {Delta<=2^(-m)}` decrease to the empty set. Their probabilities tend to zero. For any prescribed positive loss allowance, choose a single deterministic dyadic width making the sum of these two losses small. That width may depend on the fixed protocol and its uniform law. It depends on neither the realized tape nor the subsequently sampled observer and centers. No measurable-selection theorem is needed to choose this single integer index.

This reasoning would fail if the width were a public protocol parameter whose variation also changed the baseline execution law. The theorem does not give such a promise, and the proof explicitly excludes it.

### 5. Old failures are retained on the stated event

Outside the null infinite-query event, endpoint avoidance and nondetection preserve all determining integrals, hence the finite transcript, returned object, or query-free nonreturn behavior. Geometrically invalid returns remain invalid, terminal illegal requests remain illegal, and query-free nonreturn remains nonreturn.

A complete but unfair baseline allocation has the positive gap `Delta`. Each bundle value changes by at most `h/2`, and each comparison by at most `h`. Thus the old witness still violates envy-freeness when `Delta>h`. This proof does not assume a uniform lower bound on all wrong-output gaps.

The old-failure event and the newly decoded baseline-success event are disjoint. Their failure inclusion is valid outside detection, endpoint loss, small-gap loss, and the measurable null infinite-query event. Removing that null event changes no probability. The union bound requires no independence among these loss events. In particular, finite-query nonreturn is retained rather than silently discarded from the unconditional cost calculation.

### 6. Tonelli averages fixed-input guarantees, not tape-dependent inputs

For fixed `h`, take the product of the original tape probability space with the independent observer/center/displacement law. The previous construction gives a jointly measurable bounded failure indicator on this product. Every fixed pulse tuple is a normalized finite-step profile with density in `[1/2,3/2]`; the success assumption bounds its tape failure probability by `1-p`. Tonelli therefore yields

`integral_theta P_omega(failure on fixed profile theta) <= 1-p`.

The tape space need not admit regular conditional probabilities. No sigma-algebra on the entire class of profiles is required: the finite-dimensional pulse family has a directly measurable oracle parameterization. Also, the expected costs on perturbed inputs need not be finite. The integration uses only a failure indicator.

If a strictly stronger averaged failure lower bound contradicted this inequality, at least one fixed pulse tuple would violate the guarantee. There is no selection of the tuple after observing the tape, and no measurable selector over candidate inputs is needed. Varying the width with an error allowance when taking the final limit is legitimate because the uniform expected query cost and all other bound parameters remain fixed.

## Effect on theorem scope

The fixed null-set representative changes no theorem scope or numerical inequality. The protocol clarification preserves the intended class of ordinary countable-step measurable oracle algorithms, including arbitrary input-independent ideal-real tapes, infinite expected fragmentation, and finite-query nonreturn. It adds no termination, computability, finite-bit, standard-Borel-tape, or full-profile-space assumption.

If “measurable protocol” had instead been intended to include merely separately measurable rules, the new definition excludes some such rules. LM-02 shows why that weaker convention cannot by itself guarantee measurable adaptive execution events. Thus equivalence should be claimed with the standard joint-measurable interpretation, not with every possible weaker interpretation of the old wording.

No unresolved mathematical issue was found in the audited interfaces after the adopted repairs. The new Lean probability module is outside this receipt's scope and is not evidence for this conclusion.

## Audited source hashes

The final audited TeX hashes are:

| Source | SHA-256 |
| --- | --- |
| `paper/sections/nonnegative_lower_proof.tex` | `0e46119b7acce914a668234ebe3a322ff84fd983f874c2b4dd7c3c2498d68d8e` |
| `paper/sections/model.tex` | `534b15490f651f91bad820971e5bd3a4e144cb277336b79808668c0cfee75b11` |
| `paper/sections/general_results.tex` | `1aec573fa9119d53d4fe04bc7d4a7224b588bf82da9df9517726023426b48d9a` |

The accompanying `lower_measurability.json` records initial and final source hashes, findings, exact scope, and final PDF/snapshot closure. The separate probability receipt records the independent compilation and axiom audit of all 15 new probability theorems. This reviewer did not rerun the global artifact verifier during final reconciliation.
