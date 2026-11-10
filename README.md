# Envy-free division: Lean proofs and supporting materials

This repository accompanies **The Query Complexity of Envy-Free Division:
Cake, Chores, and Mixed Resources**, by Alireza Farhadi (Profound) and
Mohammadtaghi Hajiaghayi (University of Maryland, College Park).
The manuscript is maintained separately; the full submission artifact
contains the paper and its sources.

The artifact formalizes the following four main results in the models stated
in the paper:

| Result | Public Lean module | Guarantee |
|---|---|---|
| Deterministic exact chores | `Full/RefinedChoresMain.lean` | Complete envy-free allocation with at most `n! 2^(25n+18) ≤ 2^(n log₂ n+25n+18)` queries and Cuts. |
| Randomized exact cake and chores | `Full/RefinedUpperGlobalOraclePublic.lean` | One measurable adaptive protocol, almost-sure exact envy-free termination, expected queries `O(n^12 log(2n))` and Cuts `O(n^11 log(2n))`. |
| Randomized lower bound | `Full/MoatMain.lean` | Expected answered queries at least `max{0,n(np−1)/2,n²p/4−1}` on the uniform input, assuming success at least `p` throughout the stated cake/chore class. |
| Mixed impossibility | `Full/MixedIntervalMain.lean` | No uniform finite expected-query bound for the stated multiplicative or additive guarantees, separately for always-leftmost and always-rightmost Cut replies. |

Paths in the table are relative to `verification/lean/EnvyFreeResearch/`.
Public declaration names and model/hypothesis summaries are in
`verification/main_results.json`; the Lean sources contain the exact statements.
The randomized actual-cost measurability companion is
`Full/RefinedUpperGlobalOracleCostMeasurable.lean`.

The upper bounds concern oracle queries, with exact real arithmetic and ideal
random sampling. The mixed lower bound permits signed valuations with no
common total-variation ceiling; it does not assert the same impossibility
under a fixed ceiling. Finite interval allocation representations and the
measurability requirements are specified in the public declarations.

The chore protocol includes all preprocessing, compensation, recursive calls,
and endpoint recording. The randomized protocol includes rejected trials and
every normalization step. `verification/coverage.json` maps the manuscript
proofs to the public formal statements and records their precise scope.

## Files and verification

- `verification/lean/`: the selected theorem dependencies and pinned build configuration.
- `verification/lean_status.json` and `verification/lean.log`: compilation and axiom-audit evidence.
- `review/`: independent, scoped proof-correspondence and presentation reviews, with source hashes.
- `verification/module_selection.json`: the exact import closure of the main endpoints and declared checkpoint audits.
- `verification/historical_proofs.json`: Git identities and hashes of earlier supporting proofs; superseded sources remain recoverable from repository history.

The release audit rebuilds every selected project module from frozen sources
in an isolated directory. It reuses the pinned external dependencies, not
previous project compilation artifacts. The source-selection check rejects
missing dependencies and unused modules outside the declared closure. The
axiom audit checks the transitive
dependencies of every included theorem and permits only `propext`,
`Classical.choice`, and `Quot.sound`. Proof placeholders and project axioms
are rejected. Review receipts describe what each reviewer actually inspected;
they are distinct from compiler verification and from human peer review.

The endpoint manifest's freeze-status field records its state when the frozen
audit began. The completed build and release status are recorded separately in
`verification/lean_status.json` and `review/acceptance.json`.

## Reproduce the Lean check

Install Lean through elan, make `lake` available on `PATH`, and use Python 3.10 or later.
The project pins Lean 4.35.0, mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and fixed-point-theorems commit
`93a3eed3364281a9dbf9652bb52356a8db65057c`.

From the repository root:

```sh
cd verification/lean
lake exe cache get
cd ../..
python3 scripts/verify_lean.py
```

The first command downloads the available mathlib dependency cache. The
verifier builds all project modules and runs the complete axiom audit. This
is a substantial build; allow time and disk space for Lean dependencies.
Do not run `lake update` to reproduce the pinned release.

## Earlier proofs and finite checks

The current Lean tree is the exact dependency closure of the four main
endpoints and the declared primitive audit checkpoints. Superseded modules
remain recoverable from Git history; `verification/historical_proofs.json`
records identities and content hashes for the original supporting proofs.
The earlier complete development is available at commit
`9b02b672db9d87f7987d8a7c594d723be1fdfefc`.

Historical exact-arithmetic finite checks remain in `experiments/`. Run them
with Python's standard library:

```sh
python3 experiments/run_checks.py
```

These checks concern the finite constructions documented by their own
sources and receipts; they are not substitutes for the general Lean proofs.
The release audit evidence determines which main statements and source
bytes were checked for this revision.

The scripts in `scripts/` are preserved byte-for-byte from the audited full
submission artifact. `verify_lean.py` checks this repository. The paper-build,
ZIP-packaging and complete-package integrity scripts require the full
artifact directory, including the separately maintained manuscript; they do
not operate on this Lean-only repository checkout.

Dependency licenses and notices are in `licenses/` and
`THIRD_PARTY_NOTICES.md`. The development repository is
<https://github.com/farhadi94/envy-free-division>.
