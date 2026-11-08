# Envy-free division: Lean proofs and supporting materials

This repository accompanies **The Query Complexity of Envy-Free Division:
Cake, Chores, and Mixed Resources**, by Alireza Farhadi (Profound) and
Mohammadtaghi Hajiaghayi (University of Maryland, College Park).

It contains Lean formalizations of the four main results, pinned dependencies,
verification scripts, scoped correspondence reviews, and reproducible finite
checks. The manuscript is maintained separately. All four main results passed
a frozen-source cold build and transitive
axiom audit: 1,188 project modules and 12,374 theorem declarations, using only
`propext`, `Classical.choice`, and `Quot.sound`. Independent scoped source
reviews also passed. The verification status and exact source hashes are
recorded in `verification/lean_status.json`; the original audit evidence is in
`review/final_cold_audit/`. Internal reviews are not human peer review.

## Four main results

| Result | Public module | Guarantee |
| --- | --- | --- |
| Deterministic exact chores | `Full/ChoresMain.lean` | Complete exact envy-free allocation with `2^(3n log₂ n + O(n))` queries and Cuts. |
| Randomized exact cake and chores | `Full/UpperGlobalOraclePublic.lean` | One measurable ordinary-query protocol; almost-sure exact envy-free return; expected queries `O(n^21 log²(2n))` and Cuts `O(n^20 log²(2n))`. |
| Randomized exact lower bound | `Full/NonnegativeRawMain.lean` | Quadratic unconditional expected queries on the uniform profile at every fixed positive success probability. |
| Mixed impossibility | `Full/MixedIntervalMain.lean` | No uniform finite expected-query bound for the stated multiplicative or additive guarantees, separately for always-leftmost and always-rightmost Cut replies. |

Module paths are relative to `verification/lean/EnvyFreeResearch/`.
[`verification/main_results.json`](verification/main_results.json) lists
public declaration names and model/hypothesis summaries; the Lean sources
contain the exact statements. The randomized actual-cost
measurability and expectation companions are in
`Full/UpperGlobalOracleCostMeasurable.lean`.
[`verification/coverage.json`](verification/coverage.json) records the
correspondence to the manuscript and the qualifications below.

### Models and scope

The upper bounds use finite nonnegative nonatomic Borel measures and complete
allocations into finite interval representations. They require neither
densities, positive totals nor common support. The deterministic bound theorem
is stated for `n ≥ 3`, with smaller populations handled by the construction.
It permits every legal adaptive Cut response and proves the explicit envelope
`2^(14n(ceil(log₂ n)+1))` as well as the leading exponent above.

The randomized protocol covers nonempty populations and either preference
direction. Its legal oracle policy sees the answered query transcript and the
current query; the totalized answer function is jointly measurable. The result
uses ideal random sampling and exact real computation, counts rejected work,
and bounds the actual query and Cut costs on the original tape law. It is a
query-complexity theorem, without a polynomial arithmetic-time or
bit-complexity claim.

The nonnegative lower bound assumes success probability at least `p > 0` on
every normalized finite-step density profile in `[1/2, 3/2]`. For
`np ≥ 3 − 2/n`, the explicit attempted-query lower bound is
`n(np − 1)^2 / (2(n − 1))`. The cost is unconditional and charged on the
uniform input. It applies to either cake or chores; finite output fragmentation
has no common bound, and output endpoints may be chosen without queries.

The mixed result holds for at least three agents, already on finite
piecewise-constant signed densities with each net total equal to one. It
allows arbitrary measurable ideal-real tapes and has no common bound on total
variation. For every fixed positive success probability, it rules out a
uniform finite expected-query bound for signed relative multiplicative EF
with `0 < α ≤ 1`, or additive EF with `0 ≤ ε < 1`. The signed relative condition
is `v_i(A_j) − v_i(A_i) ≤ (1 − α) max(|v_i(A_i)|, |v_i(A_j)|)`.
The extremal root rule is prescribed before execution. The conclusion is
unbounded expectations across inputs, not one input of infinite expectation,
and does not assert hardness with a fixed common variation ceiling.

The lower-bound protocol semantics include incorrect or incomplete finite
returns, illegal calls and nonreturn as failures. Raw outputs use finite
disjoint interval records with a fixed endpoint convention; no universal
parser for arbitrary program bytes or redundant overlapping union expressions
is claimed.

The formal upper algorithms make conservative choices: a sufficient fixed
clearance length and explicit endpoint-recording costs for chores, and a charge
for each normalization step in randomized completion. They prove the main
bounds, but not every sharper auxiliary ledger in the manuscript verbatim.

## Contents and history

| Path | Contents |
| --- | --- |
| [`verification/lean/`](verification/lean/) | 1,188 selected Lean source modules and pinned build configuration |
| [`verification/main_results.json`](verification/main_results.json) | Public endpoints, models and hypotheses |
| [`verification/coverage.json`](verification/coverage.json) | Main-result correspondence and conservative-variant qualifications |
| [`verification/lean_status.json`](verification/lean_status.json), [`verification/lean.log`](verification/lean.log) | Recorded build status, source hashes and audit output |
| [`verification/original34.json`](verification/original34.json) | Hashes of the original 34 supporting modules, preserved byte for byte |
| [`review/formalization/`](review/formalization/) | Scoped internal source-correspondence reviews; each states its limits |
| [`review/human_review_brief.md`](review/human_review_brief.md) | Questions for an external expert; no completed human review is implied |
| [`experiments/`](experiments/), [`scripts/`](scripts/) | Finite checks and reproduction commands |
| [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md), [`licenses/`](licenses/) | Dependency notices and license texts |

Historical modules such as `R6Upper`, `R8Chores`, `ChoreComposition`,
`GlobalCompletion`, `QueryProbability`, `RootPreservation`,
`TranscriptAdversary` and `CoordinatedFamily` remain intact. The new `Full/`
development supplies the complete main endpoints and their dependencies.
Earlier coverage and review records describe earlier source snapshots; they
must not be read as certification of this revision. The finite checks remain
useful regression and counterexample searches alongside the general proofs.

## Reproduce the Lean audit

Install [elan](https://github.com/leanprover/elan) and Python 3, with `lake`
available on `PATH`. The project pins Lean **4.35.0**, mathlib **v4.35.0**
(commit `56a005855ea17e0b0958f73ec801ae140b0a1679`), and
fixed-point-theorems commit `93a3eed3364281a9dbf9652bb52356a8db65057c`.
The complete transitive dependency lock is
[`verification/lean/lake-manifest.json`](verification/lean/lake-manifest.json).

```sh
git clone https://github.com/farhadi94/envy-free-division.git
cd envy-free-division
cd verification/lean
lake exe cache get
cd ../..
python3 scripts/verify_lean.py
```

The first run needs network access. `lake exe cache get` retrieves available
mathlib caches; Lake fetches and builds the pinned fixed-point dependency as
needed. The verifier builds every included project module, checks the named
main endpoints and original-module hashes, and audits transitive axiom
dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Proof placeholders, project axioms and unexpected transitive axioms are
rejected. The audit includes dependencies of private/generated declarations.

The verifier writes `verification/lean_status.json` and
`verification/lean.log`. Allow time and disk space for this substantial build.
Do not run `lake update` when reproducing the pinned revision. A routine
incremental build may reuse local project artifacts; the release cold audit
uses an isolated source tree without previously compiled project modules.
The recorded source hashes determine which sources a passed audit covers.

To build without regenerating the verification report:

```sh
cd verification/lean
lake build
lake env lean AxiomAudit.lean
```

The chore construction uses the fixed-point library's proved Kakutani theorem.
Its use is included in the transitive axiom checks. Dependency notices do not
assign a license to the authors' project sources.

## Reproduce the finite checks

These checks use Python's standard library and exact rational/integer
arithmetic. They exercise finite cases and look for counterexamples; they do
not prove the general continuous theorems.

```sh
python3 scripts/run_checks.py
```

Results are written to `verification/finite_checks.json` and the relevant
`experiments/` subdirectories.
[`verification/check_sources.json`](verification/check_sources.json) records
the check-source hashes. The historical finite-check programs are preserved;
no numerical runtime benchmark or practical allocation implementation is
claimed by these checks.

Author and citation metadata are in [`CITATION.cff`](CITATION.cff).
