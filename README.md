# Envy-free division: Lean proofs and supporting materials

This repository accompanies **The Query Complexity of Envy-Free Division:
Cake, Chores, and Mixed Resources**, by Alireza Farhadi (Profound) and
Mohammadtaghi Hajiaghayi (University of Maryland, College Park).

It contains supporting Lean proofs, a complete dependency manifest, an
axiom-audit script, and reproducible finite checks for the four main results
in the paper. The post-review additions formalize concrete finite allocation
transitions, measure-theoretic expectation arguments, and continuous
first/last-root preservation.

**The four complete continuous/oracle/probability theorems are not fully
formalized in Lean.** Their proofs are in the paper. Every included Lean
theorem has a proof of its stated claim. The formalization does not establish
the full allocation protocols, physical realization of every transition,
or the oracle constructions supplying the probability hypotheses.

## Contents

| Path | Contents |
| --- | --- |
| [`verification/lean/`](verification/lean/) | Lean project: 32 modules, pinned Lean/mathlib dependencies, and axiom audit |
| [`verification/coverage.json`](verification/coverage.json) | Main-result labels, supporting Lean declarations, and components outside formalization |
| [`verification/lean_status.json`](verification/lean_status.json) | Source hashes and results from the recorded Lean build |
| [`verification/lean.log`](verification/lean.log) | Build output and transitive axiom audit |
| [`experiments/`](experiments/) | Exact-arithmetic finite checks for chores, randomized upper/lower bounds, and mixed comparisons |
| [`scripts/`](scripts/) | Reproduction commands |
| [`review/human_review_brief.md`](review/human_review_brief.md) | Focused proof obligations for an external expert; no human review is implied |

The recorded audit covers every included authored theorem and the
private/generated theorem declarations; exact counts and source hashes are
in `verification/lean_status.json`. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed. The verifier
rejects proof placeholders, project axioms, and unexpected transitive axioms.

The coverage record identifies the manuscript proof sections by label and
hash; the manuscript is maintained separately. Historical module names such
as `R6Upper` and `R8Chores` are retained so declaration names and source hashes
agree with the checked artifact.

The additional modules are:

- `ChoreComposition`: concrete compensation records, committed transitions,
  own-cost identities, and conservation of original-root IDs.
- `GlobalCompletion`: finite bundle transport, frozen-agent guards,
  zero-residue cases, and bounded progress under explicit primitive certificates.
- `QueryProbability`: measurable success-event bounds, extended query-count
  integrals, geometric waiting times, and an unbounded-supremum conclusion.
- `RootPreservation`: continuous first/last-root barriers, preservation under
  one-sided cumulative perturbations, and reflection of signed queries.
  These support the two prescribed bracket-sign extremal-root rules in the
  mixed lower bound; they do not prove impossibility for always-leftmost or
  always-rightmost rules.

These modules prove consequences of explicit hypotheses. The manuscript
proves that the continuous protocols supply those hypotheses; that link is
not fully formalized. The coverage record separates finite, measure-theoretic, and continuous
supporting results from the remaining obligations.

## Reproduce the Lean audit

Install [elan](https://github.com/leanprover/elan) and Python 3, with `lake`
available on `PATH`. The project pins Lean **4.35.0**, mathlib **v4.35.0**,
and the exact dependency revisions in `lake-manifest.json`.

```sh
git clone git@github.com:farhadi94/envy-free-division.git
cd envy-free-division
python3 scripts/verify_lean.py
```

The first run needs network access to download dependencies. The verifier
builds all project modules and audits every project declaration. It writes
`verification/lean_status.json` and `verification/lean.log`. Import and
linter warnings may appear; a successful axiom audit is recorded explicitly.

To build the Lean project without regenerating the audit report:

```sh
cd verification/lean
lake build
lake env lean AxiomAudit.lean
```

## Reproduce the finite checks

These checks use Python's standard library and exact rational/integer
arithmetic. They exercise finite cases and look for counterexamples; they
do not prove the general continuous theorems.

```sh
python3 scripts/run_checks.py
```

Results are written to `verification/finite_checks.json` and the relevant
subdirectory of `experiments/`. The check programs are exact copies of those
used during review; [`verification/check_sources.json`](verification/check_sources.json)
records their hashes. No complete allocation implementation or runtime
benchmark is included.

Author and repository citation metadata are in [`CITATION.cff`](CITATION.cff).
