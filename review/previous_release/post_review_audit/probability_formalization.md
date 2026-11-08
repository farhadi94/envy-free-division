# Probability-to-expectation formalization

The new module is `verification/lean/EnvyFreeResearch/QueryProbability.lean`,
in namespace `EnvyFreeResearch.QueryProbability`. It imports only `Mathlib`.
It contains 15 proved theorems and one event definition. It does not change
the project umbrella, `AxiomAudit.lean`, coverage metadata, or any frozen
round source. No global verifier was run by this lane.

Status: **locally compiled and fully axiom-audited**. The source SHA-256 is
`c050c1da43d681952b4529a783dbb11efcf42ab70e26d27665c20cc37ea47241`.
All 15 theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`;
there are no placeholders, custom axioms, or compiler warnings. Independent
mathematical/integration review is separate from this author receipt.

## What is now checked

The proofs use an arbitrary measurable space, an actual `Measure Ω`,
measurable events/functions, extended nonnegative Lebesgue integrals,
measurable indicators, and countable sums. They are not finite weighted-sum
certificates or scalar inequalities with the desired expectation bound
assumed as a hypothesis.

### Mixed lower bound

For a measurable extended natural query count `Q : Ω → ℕ∞`, a measurable
success event `S`, a natural cutoff `q`, and nonnegative extended parameters
`p, δ`, `enat_expectation_lower_from_success` proves

\[
 p\le\mu(S),\qquad
 \mu(S\cap\{Q\le q\})\le\delta
 \quad\Longrightarrow\quad
 (q+1)(p-\delta)\le\int Q\,d\mu.
\]

The integral is `lintegral`, so both an infinite count and an infinite
expectation are permitted. It is taken over **all outcomes**, including
unsuccessful returns and nontermination. No termination, finite-expectation,
zero-error, independence, or finite-support hypothesis is imposed.
Subtraction is truncated nonnegative subtraction; on a probability space
with `0 ≤ δ < p ≤ 1`, it is the ordinary positive difference.

The proof first covers `S` by its low-cost and high-cost parts, then
integrates the measurable lower indicator
`(q+1) 1_(S ∩ {Q ≥ q+1})`. The discreteness of `ℕ∞`, including its top value,
is checked. A separate generic theorem handles an arbitrary measurable
`Q : Ω → ℝ≥0∞` with the low-cost event `{Q < a}`; a natural-valued
specialization is also included.

`supremum_expectations_eq_top` checks the final quantifier step. With a fixed
gap `δ < p`, if every input has success mass at least `p` and each cutoff
has **some fixed input** with successful short-run mass at most `δ`, then
the supremum of the expectations over inputs equals infinity. The inputs
are indices, with no countability or input-distribution requirement. This
does not assert the existence of a single input with infinite expectation.

This matches `paper/sections/mixed_lower_proof.tex`, subsection
`r6m:expected`, including equation `r6m:eq:expected`. The guarded simulation,
its exact identification with `S ∩ {Q ≤ q}`, and the finite-horizon hard
input/selector construction remain mathematical manuscript proofs.

### Upper-bound waiting time

For measurable `T : Ω → ℕ∞`, `survival T n` is the actual event `{T > n}`.
`measurable_survival` verifies its measurability. The module proves the
pointwise extended-integer tail identity and applies mathlib's nonnegative
Tonelli theorem to obtain

\[
 \int T\,d\mu=\sum_{n=0}^{\infty}\mu\{T>n\}.
\]

Under the explicit measure contraction

\[
 \mu\{T>n+1\}\le r\,\mu\{T>n\}\qquad(n\ge0),
\]

it then proves

\[
 \mu\{T>n\}\le r^n\mu\{T>0\},\qquad
 \int T\,d\mu\le\frac{\mu\{T>0\}}{1-r}.
\]

On a probability space, the bound is at most `1/(1-r)`. On any finite
measure space, `r < 1` additionally implies `T ≠ ∞` almost everywhere.
These are conclusions: neither summability, integrability, nor an
almost-sure finite count is assumed. The model allows `T = 0`.

`expected_cost_le_of_attempt_budget` also integrates a pointwise budget
`C(ω) ≤ b T(ω)` to obtain `∫ C dμ ≤ b/(1-r)` on a probability space.
Its upper bound does not require measurability of `C`; for a measurable
protocol cost it is the usual unconditional expectation statement.

For the manuscript's fixed-history trial analysis one may apply these
lemmas to the corresponding probability law, with `r = 3/4` for the
Snapshot bound and `r = 1/64` for the Repair/Shrink bound. The file does
**not** define conditional-probability kernels or derive the displayed
contraction from the protocol. The actual conditional acceptance estimates,
fresh-trial implementation, law after a history, and summation over the
bounded number of anchored iterations remain outside this module. It
supports the geometric-tail step in `upper_proof.tex`'s global completion
argument; it does not formalize the complete expected-query theorem.

## Precise coverage boundary

The caller must supply measurability of `Q`, `T`, and the success event,
as applicable. The success event must be identified with legal correct
finite return by the separate protocol proof. A nonreturning execution that
makes only finitely many calls may have finite `Q` and simply lie outside
`S`; the lower-bound theorem does not exclude it. For an upper-bound waiting
time, the caller must identify `T` with the number of attempts until return,
using `∞` for failure to finish. Numeric almost-sure finiteness of `T` alone
does not formalize the implementation's return behavior.

Still outside Lean here are the continuous allocation construction,
oracle/root-selector replay, signed-measure perturbations, product dominated
convergence and fixed-input selection used to establish the hard-input
hypothesis, protocol conditional laws, and global allocation correctness.
The use of Tonelli **for the explicit survival-indicator series** is checked;
this does not claim that the manuscript's other Fubini/Tonelli applications
have been formalized.

## Declaration inventory

1. `success_tail_mass`
2. `successful_cost_tail_le_lintegral`
3. `expectation_lower_from_success`
4. `enat_lt_successor_iff`
5. `enat_expectation_lower_from_success`
6. `nat_expectation_lower_from_success`
7. `supremum_expectations_eq_top`
8. `measurable_survival`
9. `enat_eq_tsum_tails`
10. `lintegral_enat_eq_tsum_survival`
11. `survival_mass_le_geometric`
12. `waiting_time_expectation_le`
13. `probability_waiting_time_expectation_le`
14. `expected_cost_le_of_attempt_budget`
15. `waiting_time_finite_ae`

The sole definition is `survival`.

## Local verification

The source compiled with the pinned Lean 4.35.0/mathlib v4.35.0 project and
an empty diagnostic log. Reproduce from
`research/submission_focused/verification/lean` using the repository's
pinned toolchain:

```sh
../../../tooling/lean-4.35.0-darwin_aarch64/bin/lake env lean EnvyFreeResearch/QueryProbability.lean
```

The per-declaration audit source appends `#print axioms` for every authored
theorem to an exact copy of the module. Its source, output, hashes, exit
status, exact inventory, and source guard are recorded beside this report
in `probability_formalization_axioms.lean`,
`probability_formalization_axioms.log`, and
`probability_formalization_receipt.json`. This is a local module audit;
integration and the project's global audit are owned by the root agent.
