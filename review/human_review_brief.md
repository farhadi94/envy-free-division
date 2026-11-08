# External expert review brief

This brief concerns *The Query Complexity of Envy-Free Division: Cake,
Chores, and Mixed Resources*, by Alireza Farhadi and Mohammadtaghi Hajiaghayi.
The repository contains Lean proofs and supporting materials; the manuscript
is maintained separately and should be obtained from the authors for a
paper-to-formalization review. No completed human peer review is claimed.
Internal source reviews and compiler checks are distinct forms of evidence.

## Materials and review scope

Start with [`verification/main_results.json`](../verification/main_results.json)
and [`verification/coverage.json`](../verification/coverage.json). They identify
the four public endpoints, hypothesis summaries and conservative formal variants.
The Lean sources contain the exact statements.
The public source modules are under
[`verification/lean/EnvyFreeResearch/Full/`](../verification/lean/EnvyFreeResearch/Full/):

- `ChoresMain.lean`: `Chores.Main.deterministic_chores`.
- `UpperGlobalOraclePublic.lean`:
  `UpperGlobalPhysical.randomized_exact_envy_free_oracle`, with actual-cost
  measurability and expectation companions in `UpperGlobalOracleCostMeasurable.lean`.
- `NonnegativeRawMain.lean`: `optimized_attempted` and `quadratic`.
- `MixedIntervalMain.lean`: `attempted_expectations_unbounded` and
  `relative_attempted_expectations_unbounded`.

Declaration names above have prefix `EnvyFreeResearch.Full`.
[`verification/lean_status.json`](../verification/lean_status.json) and
[`verification/lean.log`](../verification/lean.log) record build/audit evidence;
[`review/formalization/`](formalization/) contains scoped internal reviews.
Their exact source hashes and limitations matter more than the number of
reports or declarations. The frozen-source cold build and axiom audit passed
for all 1,188 project modules and 12,374 theorem declarations, using only the
three standard Lean axioms. The original evidence is retained in
`review/final_cold_audit/`; this brief is a guide for further expert review.

The four complete main results are now represented by public Lean statements.
An expert review should assess the mathematical statements and their match to
the intended query model, rather than assume that compiling a differently
scoped theorem proves the paper. The original 34 supporting modules remain
byte-identical; [`verification/original34.json`](../verification/original34.json)
records their hashes. Historical partial-coverage reports concern those older
snapshots, not the completed development.

## Deterministic chores

Read the paper's pooled compensation, Core/SubCore and completion arguments,
and trace the actual program behind `deterministic_chores`. Check:

1. Every reached state preserves physical ownership, the exact own-baseline
   identity and reserve inequalities for all relevant rival comparisons,
   including private complements and frozen roots.
2. Masked/affine compensation uses ordinary interval queries and actual
   available material. Zero clipped utilities and affine-zero assignments
   do not invalidate nominal donor accounting or whole-parent guarantees.
3. Component mergers commit disjoint groups together. The original-root
   multiset is conserved; removed material is neither lost nor counted twice.
4. Atomic and exhausted exits control the entire remaining domain, not only
   an active cohort. Recursive calls use strictly smaller populations, with
   their specifications discharged by induction in the public theorem.
5. The pool-floor/rank argument forces termination for every legal response
   history, including plateau roots, rather than assuming future success.
6. Ordinary queries and endpoint recording are charged through the actual
   execution. The formal fixed clearance length and additional recording
   overhead prove both the explicit envelope and leading exponent; they do
   not assert literal equality with every sharper paper ledger.

A useful counterexample identifies a reachable predecessor and failing
transition. Distinguish an abstract invariant counterexample that violates
reachability from a defect in the actual protocol.

## Randomized cake and chores

Read the Repair, Snapshot, Shrink and global-completion chain, then the
ordinary-protocol bridge and cost-measurability companion. Check:

1. The public `next` function is independent of valuations and the oracle
   policy, jointly measurable in tape/transcript, and linked to actual
   ordinary Option-oracle execution, not merely separate finite phase runs.
2. Each call meets the primitive's hypotheses on its actual physical input.
   Acceptance bounds hold on the original independent-sample law, after
   conditioning on the allowed past, including candidate rejection work.
3. The legal oracle observes the answered query transcript and current
   query. No stronger access to private random coordinates or future samples
   is silently assumed or silently granted.
4. At most two successful shrinking requests yield the transfer. Whole
   bundles remain physical, frozen-agent guards hold, zero rows are handled,
   and progress is measured against the saved committed anchor.
5. Almost-sure return is established separately from expected cost. Query-free
   stalling cannot be hidden by a finite query expectation.
6. Costs are the actual supremum over fuel bounds on one tape. They are
   almost-everywhere measurable under the stated answer-policy hypothesis,
   and expectations are unconditional; unsuccessful trials are retained.
7. Charging every normalization step is conservative and preserves the main
   exponents 21 and 20. The endpoint does not certify every sharper additive
   constant, optional tail bound or storage claim in the written argument.

Exact real computation and ideal random sampling are part of the model;
polynomial bit complexity is not claimed.

## Nonnegative lower bound

Check that success is required on the entire normalized finite-step density
class in `[1/2, 3/2]`, while the expected cost is charged on the uniform input.
The pulse width and hard-input law must be fixed before the execution tape
is sampled. Replay must retain old failures as well as create new envy on
previously successful tapes, including finite-query nonreturn and a terminal
illegal request. The quantitative threshold is `np ≥ 3 − 2/n`; the optimized
lower bound is `n(np − 1)^2 / (2(n − 1))`.

The random tape may be an arbitrary probability space; next actions are
jointly measurable. Finite interval outputs may have arbitrarily many
components and unqueried endpoints. Geometric validation must not perform a
fairness-dependent repair or lose cost. The typed disjoint-record encoding is
explicit; no universal parser for redundant unions or program bytes is claimed.
This is an exact-EF quadratic result, not a superquadratic or fixed-positive-
tolerance lower bound.

## Mixed impossibility

Trace the moving frontier, strict cumulative barrier, physical unsplit-tail
obstruction and preservation of roots at the endpoint. Check that later
updates preserve every previously captured failure and that finite-coordinate
quantiles are measurable without a bound on the number of output endpoints.
The hard profile is selected by finitely many batches and is fixed before the
actual tape is drawn; no infinite limiting profile or tape-dependent input
is allowed. Finite-step densities must remain finite-step through reflection
and every update.

The public result uses attempted calls, including failures, and separately
prescribes always-leftmost and always-rightmost roots. The formal rightmost
proof may use direct mirrored capture rather than the paper's extra-Eval
simulation. Both must establish the claimed original ordinary-query model.

Every hard input has net totals one, while total variation is unbounded across
inputs. The signed relative guarantee for `0 < α ≤ 1` is reduced to the usual
α-cake comparisons on these positive-net profiles; additive approximation
uses `0 ≤ ε < 1`. The conclusion is no uniform finite expected-query bound,
not one input with infinite expectation or nonexistence of fair allocations.
No hardness with a fixed common variation ceiling or an oracle supplying both
extrema on demand is asserted.

## Requested report

For each substantive finding, give the source declaration or manuscript
location, the missing implication or counterexample, and whether a local
repair suffices or the theorem statement must change. Separate examined
obligations from unexamined ones and record exact source/manuscript hashes.
Assess the public hypotheses and conclusions as well as their proofs. Neither
finite experiments, a compiler pass nor a count of internal reviews substitutes
for that assessment.
