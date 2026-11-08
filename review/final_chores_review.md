# Final deterministic-chores release review

**PASS. No required chore source, model, statement, or presentation correction found.**

Reviewed public endpoint: `EnvyFreeResearch.Full.Chores.Main.deterministic_chores`, corresponding to current paper Theorem 2.1. This is an independent final source/correspondence review; the earlier detailed review was consulted and its central claims checked against current source rather than accepted blindly. No Lean or manuscript source was changed and no expensive build was run.

## Current PDF receipt

- File: `paper/paper.pdf`, 66 pages.
- SHA-256: `5b24cbca4d65952a80ee85608842807a1e0104c26db7c4be99fc0fe25cde60a5`.
- Fresh PDF text inspection confirmed Theorem 2.1, its explicit envelope, and Appendix I's scope qualification. Fresh renders of pages 4 and 66 were inspected: the theorem, exponent, coverage table, and qualification are readable and have no visible clipping or overlap.

## Accepted findings

1. Theorem 2.1 and the public deterministic_chores statement agree for n >= 3: finite nonnegative atomless costs, all legal full-history ordinary Eval/Cut policies, complete exact chore EF, and both claimed query envelopes.

2. The concrete cost-independent program starts from empty history with no supplied cost cache. native_complete closes the population recursion using concrete_step_complete; only strictly smaller child populations are used.

3. Physical shares are pairwise disjoint and cover Icc 0 1 literally. Finite Ioc lists plus one uniquely owned singleton {0} give finite interval outputs; atomlessness preserves costs. Every piece endpoint is within [0,1] and inherited or an actual Cut reply.

4. capacity_bound proves the actual total query capacity, including n initial Evals, is at most both n^(3*n)*2^(27*n) and 2^(14*n*(Nat.clog 2 n+1)); successful trace length and Cut count inherit their minimum.

5. The formal fixed clearance length 14*n*weight n and explicit observer-recording/interpreter costs conservatively differ from the sharper manuscript auxiliary ledger. Appendix I explicitly discloses these choices and does not claim verbatim verification of every auxiliary estimate.

6. All 443 candidate Lean source hashes and all three configuration hashes exactly match the passed chore closure audit. All 34 original supporting Lean modules match their preservation manifest.

7. Current 66-page PDF extracted text agrees with the reviewed statement and scope source. Fresh renders of pages 4 and 66 show readable theorem, explicit bound, coverage table, and qualification without visible clipping or overlap.

## Precise scope and model checks

`Population.Costs` supplies finite measures on real Borel sets with null singletons. This expresses the intended finite atomless nonnegative costs, with no normalization or positive-total assumption; interval measures can be zero-extended to the real line. `AdaptiveOracle.IsLegalPolicy` ranges over all finite histories, with valid replies and complete answers for legal queries. There is no extremal-root restriction, and repeated queries may receive different legal roots. Half-open interval evaluation agrees with the paper's closed interval evaluation because singletons have zero measure.

`Main.program` depends on population and replies, not the measure profile. `Main.native_complete` instantiates the actual local step rather than requiring an external correctness premise. `UnitEntry.program_correct` includes the initial cache-building Evals and produces the same successful execution used by the public bounded `AdaptiveOracle.run`. A successful return cannot conceal an unanswered attempted call: the run would stop at such a call. Per-query legality and valid replies are explicit final conclusions.

`UnitEntry.Output.share` supplies a literal physical allocation, not merely numerical fairness data. Native pieces are finite lists, the singleton zero has exactly one owner, and disjointness, full closed-unit coverage, measurability, interval bounds, and all chore comparisons are proved. The returned known-endpoint and scoped-query facts start with `{0,1}`.

`Main.capacity_bound` uses two independently proved capacity estimates before taking their minimum. The final Cut bound uses Cut count <= answered trace length, which is sufficient for both advertised bounds. The first envelope is exactly `2^(3*n*log2(n)+27*n)` when expressed over reals, yielding the claimed leading coefficient 3. The second uses `Nat.clog 2 n = ceil(log2 n)` for positive n.

The manuscript uses least sufficient clearance length and a sharper cached SubCore/local ledger. Current Lean uses a fixed sufficient clearance length and pays explicit recording/interpreter overhead. Current Appendix I accurately qualifies this formal variant. The release should retain that qualification; this is an accepted scope difference, not an outstanding correction.

## Verification transfer and preservation

The passed frozen chore audit reports 443 modules and 4,888 theorem declarations, with only `propext`, `Classical.choice`, and `Quot.sound` allowed. Every one of its 443 recorded candidate source hashes and all three configuration hashes was independently recomputed and matched. The audit reports no source or configuration changes during execution. All 34 original supporting modules were separately checked against `verification/original34.json` and match byte for byte.

The companion JSON records current reviewed manuscript/Lean hashes, the complete matched closure hash map, audit-report hash, configuration hashes, and PDF hash. This receipt certifies the chore role against that exact PDF/source snapshot. Candidate-wide all-four-results cold verification is a separate root-owned release gate; no claim that it has finished is made here.

## Required findings

None within the chores role.
