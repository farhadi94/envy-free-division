# Author audit: randomized upper interfaces and completion

This is the author audit of the new edits to `paper/sections/upper_proof.tex`. It is not an independent review of those edits. The previous independent audit concerned an earlier source; the coordinating agent has assigned a separate reviewer to the present changes.

**Author conclusion:** The claimed complete Las Vegas cake/chore allocation and expected bounds remain justified by the audited arguments. I found no missing mathematical premise requiring a weaker theorem. The changes expose the exact primitive contracts and prove their composition explicitly. No global build or publication step was performed by this author.

Input source SHA-256: `bd52ff2087132a2631398e8a04419b8d9cb9833b780dad064aec651a6c56c5d1`.

Author-audited output SHA-256: `66955a399e1eaa71abf7df7f92662b23ba37b57e67998ee59482b75a4634fec9` (1,305 lines).

## Scope and edits

The focused pass read the complete former completion section, lines 967–1146, line by line. It also rechecked the upstream arguments needed for the interfaces: legal ordinary queries and circular sampling; immutable interpolation and endpoint charging; reserve selection; witness-cell assignment isolation; physical credits/taxes and supply; conditional failure sums; Snapshot's zero, small, and large disagreement branches; and one-sided refinement and shrinking. The actual numerical parameters and algorithmic upper-bound orders are unchanged.

The principal source additions are:

- `r6u:repair-contract`: positive recorded buffer, approximate-EF input, whole-endowment permutation, disjoint additions, exact residue, active EF, quarter-buffer spending, conditional acceptance probability, and complete cost cap.
- Expanded `r6u:snapshot`: exact partition output, active EF, completeness or a positive residue for every active observer and a certified pair, history-conditional acceptance, and the full outer-trial cost.
- `r6u:shrink-contract`: permitted factor range, positive recorded input, exact partition, active EF, both residue bounds, rejection behavior, conditional acceptance, and carving plus inner-repair accounting.
- `r6u:completion-contract`: an actual committed-state invariant and an explicit proof of global EF, frozen guards, strict potential progress, almost-sure termination, and the displayed total bounds from those interfaces.
- `r6u:physical-balance` and `r6u:own-transport`: exact all-observer resource balance and the two different own-value/own-cost inequalities.

An accepted primitive output is a recorded candidate partition. The caller can retain it temporarily; it becomes committed only at the stated EF checkpoint. Rejection preserves the input sets and committed allocation while retaining all charged query history. A full trial is a Snapshot attempt, Shrink attempt, or standalone Repair attempt; inner Repair calls are included in their outer attempts.

I removed the optional intermediate zero-residue exits. The specified protocol now makes zero-residue reductions only at committed EF anchors. The lower bounds in all three interfaces already keep every active intermediate residue positive, so no such optional exit is needed. This removes an unnecessary alternative control path without weakening the result.

## Interface verification

| Primitive | Preconditions used by completion | Accepted result | Conditional acceptance and cap |
|---|---|---|---|
| Repair | Original-population parameters fixed; `3 ≤ k ≤ n`; disjoint recorded endowments and buffer; every active buffer value positive; `g_ij(W) ≥ −τ μ_i(B)` | `X_i = W_{π(i)} ∪ Y_i`; disjoint additions including seeds and payments; active EF; literal residue; total additions worth at most one quarter of the buffer to each active observer | Greater than `63/64`; `3m` Cuts, `6nm` queries |
| Snapshot | Same fixed parameters; `3 ≤ k ≤ n`; recorded domain positive for every active observer | Complete active EF allocation, or an exact partition into active EF pieces and a residue positive for every active observer, with `g_ab(X) ≥ θ μ_a(T)` for distinct active agents | Greater than `1/4`; `6m` Cuts, `12nm` queries, including all alternatives and inner Repair |
| Shrink | Same fixed parameters; positive recorded domain; factor fixed before the trial in `[1, (2/θ)(8/τ)^(k−1)]` | Exact active EF partial partition with `3 μ_i(U)/(8G) ≤ μ_i(U') ≤ μ_i(U)/G` | Greater than `63/64`; `4m` Cuts, `8nm` queries, including every rejected carve and inner Repair |

The Repair contract is proved from the physical decomposition `Y_i = Z_{π(i)} ∪ P_i`, the actual payment-margin calculation, and the seed/reserve spending bound. Its conditional rejection sum is established before any completion argument. The chore tax orientation and its minimum-assignment regret/supply bound were rechecked separately from the cake credit orientation.

Snapshot's probability combines an unconditional interpolation failure event with conditional per-candidate witness probabilities; it does not condition the interpolation estimate on the successful sampled table. Its selected valid input then receives a fresh Repair trial after the entire observed candidate history. The zero branch checks actual complete EF. A partial return has positive residue for every active observer, not merely the certificate observer.

For Shrink, one-sided carving yields a buffer between `1/(2G)` and `1/G` of each normalized input value, and its endowment range is within the Repair tolerance. The quarter-buffer bound gives the lower residue estimate. Refinement has logarithmic depth in `G`; the cap covers the whole permitted factor range. No completion or existence oracle is used to establish this contract.

## Completion audit

**State and additive exits.** At every committed checkpoint, `(W_1,…,W_n,U)` is a recorded partition of the entire resource, `W` is globally EF, and the cake or chore frozen guards hold. The proof now checks that any active EF partial allocation of `U`, added under its original owners, preserves global EF and updates the guards to the literal residue. This justifies complete Snapshot returns, zero-cost chore completion, the all-zero case, and the one- and two-agent bases. A zero-value cake observer can freeze because its outgoing guard equals zero. Sink-component freezing has the correct opposite choices for cake and chores, leaves the value state and potential unchanged, and decreases the active population.

**Two-shrink construction.** In the certificate column, all normalized losses are nonnegative and the diagonal is zero. A row excludes at most one candidate factor because the forbidden interval has multiplicative width `16/(3τ) < 8/τ`. Thus a safe factor exists among the `k` candidates. The proof displays both implications: a low scaled entry is at most `τρ_i` by Shrink's lower bound, and a high scaled entry is at least `2ρ_i` by its upper bound. The certificate row is high and the diagonal is low.

A directed path in the saved graph supplies a high-to-low edge. If its low endpoint is the certificate label, identity works. Otherwise the proof specifies the permutation along a simple return path, including the closing assignment of the certificate label to the low row. If a path edge has excessive own loss, the second request uses factor `2/τ`, which lies in the allowed factor range, and identity is retained. Its new residue makes that edge a large witness. A nonidentity transfer is never followed by another shrink. Every retry keeps the same chosen domain and factor.

**Repair applicability.** Snapshot and all Shrink pieces are disjoint. The sum `H` of the Shrink allocations is active EF by additivity. In either preference direction,

`g_ir(D) = g_ir(W) + g_ir(H) + d_i,α(r) − d_i,α(i)`.

This proves both the approximate-EF input bound `−τρ_i` and witness bound `(2−τ)ρ_b`. The endowments `D_i` and positive final buffer satisfy every Repair precondition. Global EF of the uncorrected `D` is neither required nor assumed.

**Physical transport and guards.** After final Repair, `f=β⁻¹` fixes frozen labels and `Z_{f(j)}=W_j∪B_j`. The `B_j` partition the allocated part of the old residue, and they vanish at frozen labels. Hence every original observer, even a frozen one, has exact balance `Σ_j μ_i(B_j)+μ_i(U')=μ_i(U)`.

Before proving global EF, the argument uses only active-active EF to compare an active agent with the active recipient of its own old label. Cake gives `μ_i(Z_i) ≥ μ_i(W_i)+μ_i(B_i)`; chores gives the reverse inequality. Frozen observers have equality. In particular, the chore statement allows an increase in own cost by that label's additions. These inequalities and exact balance prove the cross-population comparisons and updated guards. Thus global EF is derived before it is used in the potential argument.

**Saved-anchor potential.** For every old proper domination target, cake loses at most the target label's additions, while chores loses at most the observer's own label's additions. Exact balance absorbs either loss. Positive new row residue prevents a transported target from becoming the observer; a zero row residue instead saturates all `n−1` proper targets. The proof does not try to count a self-image as a proper target.

For the witness, compare the final bundle to the recipient of `D_b`, then use the final Repair's quarter-buffer bound. This gives `(7/4−τ)ρ_b > ρ_b ≥ μ_b(U')` for either orientation, while `μ_b(U') ≥ 3ρ_b/4 > 0`. The witness label was a nondomination edge of the saved anchor. Its image is therefore proper and distinct from every transported old target. The global integer potential increases by at least one relative to that anchor. Temporary Snapshot/Shrink gains are not used as a second baseline.

**Termination and accounting.** Each nontrivial iteration starts below the finite potential ceiling `n(n−1)`. Every nonterminal iteration strictly increases that same potential; terminal iterations complete from an unsaturated state. Freezing steps strictly decrease the active population. There are therefore at most `n(n−1)` nontrivial iterations.

For a request whose trial acceptance is at least `p` after every full preceding history, iterated conditioning gives `Pr(N>r | history) ≤ (1−p)^r` and `E[N | history] ≤ 1/p`. No independence between attempts or requests is asserted. One iteration uses one Snapshot request, at most two Shrinks, and one final Repair, for at most `4+3(64/63)=148/21<8` expected full trials. Each full trial has the common cap `6m` Cuts and `12nm` queries. Conditioning on reached iteration histories gives the displayed total bounds, including all rejection and all-original-observer recording costs. The optional failure-reporting wrapper retains its fresh-full-trial-boundary interpretation.

## Validation and formalization coordination

Local structural checks found balanced TeX environments, unique labels in the edited source, and all references resolvable in the paper sources. No global TeX build was run.

The existing exact finite check script passed again: 13,140 row/permutation transport states; 8,000 safe-factor/transfer cases covering identity, rotation, and second-shrink branches; and the stated parameter checks at six population sizes. An additional exhaustive finite check tested 4,232 three-label row states with two active labels and one frozen label. It assumed old EF and guards plus only active-active EF after permutation/additions, and verified global EF, new guards, domination transport, and zero-residue saturation. Of these states, 2,624 had positive new residue and 1,608 had zero residue. These checks are finite stress tests, not proofs of the continuous theorem.

I supplied the `mixed_signed` formalization agent with the actual finite transition obligations: whole-label identity and nonnegative additions, exact row mass balance, active-only EF, fixed frozen labels, derived own bounds, derived global EF/guards, proper-target transport with zero-row saturation, quarter-spending witness gain, and strict saved-anchor potential increase. The intended `GlobalCompletion.lean` statements derive these conclusions from concrete value tables; they should not assume global EF, guard preservation, or potential increase as transition fields. That module and its build are owned by the formalization agent, not by this author pass.

## Residual assumptions and review status

The complete theorem still relies on the paper's continuous and probabilistic proofs: nonnegative nonatomic measure properties; ordinary Cut realization on finite unions; circular inclusion and endpoint laws on cutter-null intervals; measurable finite choices; exchangeability and integrated interpolation; conditional endpoint domination under adaptive rejection; the physical realization of all candidate partitions; and fresh-trial probability bounds under every legal measurable nonanticipating Cut policy. Exact real arithmetic and independent uniform-real draws remain the stated model.

Finite value-table formalization does not itself construct the continuous pieces, justify those probability laws, or choose the safe factor and graph path producing `α`. The handwritten two-shrink argument supplies the latter transition hypotheses, and the physical contracts supply the finite tables' exact balance identities. The conditional geometric-tail calculation and conversion from charged trials to oracle calls also remain part of the mathematical protocol proof unless separately formalized.

No mathematical gap remains open in this author audit. Independent acceptance of the new source and the final integrated PDF/Lean build are separate tasks. The source was handed to the independent composition reviewer at the output hash above and is held fixed pending any concrete review finding.
