# Independent current deterministic-chore manuscript/source review

Verdict: no mathematical blocker found in the scoped current chore argument or in its correspondence with the inspected concrete Lean statements. The explicit bound `Q,C <= n! * 2^(25n+18)` is supported by the manuscript's arithmetic and is exactly the bound of `RefinedChoresMain.deterministic_chores`. Two small precision improvements are recommended below; neither requires changing the construction or the bound.

This is a read-only mathematical/source review of the current deterministic-chore statement, overview, and proof. It is not the still-required fresh final whole-paper review after all edits. I did not read earlier review conclusions or rely on source comments asserting completion. I inspected theorem types, definitions, and the relevant proof steps. I ran no compiler, tests, network action, or commit. The only created files are this report and its hash manifest. Accordingly, this report does not claim a fresh successful Lean build or a freshly printed axiom report.

## Precision findings

1. **Clarify ordinary-label deficit accounting (minor).** At `chore_proof.tex:311`, “At unchanged labels there is no new donor credit or deficit” is liable to be read as saying all labels other than the exceptional label acquire no actual deficit. A donor permutation's return path can replace a piece at another label by an allowed equalizer, creating a genuine negative deviation there. What is zero away from the exceptional label is the **extra deficit beyond the old reserve**, and the new own credit; the ordinary equalizer deficit is covered by that donor's old `h`. The surrounding sentence at lines 299–304 already accounts for these contributions, so the proof can be read correctly. Suggested wording: “At every other label there is no new own credit or extra deficit; any equalizer deficit is covered by that donor's old reserve.” This is exactly `ChoreComposition.proposal_debit_bound` and the `hother` premise discharged by `RefinedChoresPhysicalPayment.output_valid`.

2. **Make global terminal closure explicit (optional clarification).** At `chore_proof.tex:430`, “close all packages” should explicitly include the unused root of the terminal cohort and all live packages outside that cohort, at their unchanged identity allocations, retaining their frozen ancestors. The earlier physical-margin lemma permits this, and the intended operation is already correct. The concrete implementation is explicit: `RefinedChoresTerminalAggregate.terminalPool` consists of the previous closed list, the closed cohort output, and `.close` applied to all remaining active packages; `terminal_pool_ids`/`TerminalGroup.pool_ids` retain every original ID. One sentence would make the paper's subsequent claim about the entire remaining domain easier to verify without supplying this interpretation.

## Mathematical checks

### Preprocessing and the protected label

The Core inequalities follow from one allocated whole parent and each allocated prefix costing the cutter at least her own prefix. Positive residue forces the whole-parent recipient to be a noncutter. Since each original post-snapshot residue contains the final reference residue, its cutter gap exceeds `r_c/H` when `H>n-1`; clearance then makes it large. The pigeonhole count `J=(S-1)(n-1)+1` supplies exactly the common omitted pair required later. No whole gap profile is synchronized.

The tracked universe is fixed to the original snapshots. The bound `J(n^3+n^2)` covers observer values of original atoms and original gaps. A triggering value becomes large after `L` calls by `H^2((n-1)/n)^L<=1` and stays large as residue decreases. This justifies at most one triggering batch per tracked pair, even though other pairs can move from small through the intermediate range before their own trigger. Zero-cost exits occur at an envy-free boundary and preserve all comparisons.

### Deferred payment and root-local cycles

A live root's physical owner is identity and its actual piece remains the original prefix throughout payments and cycle normalization. The allowed edge relation is separate from that owner. The source set for an ordinary group is common, but neither its target nor its other components are required to agree. `RefinedChoresRootState.Tracked`, `payAt`, and `RefinedChoresGroupPaid.Group.liveOutput_good` encode these points directly.

The exceptional donor's own reduction is the affine value `C_j(D)-g_j`, rather than the whole removed-suffix value. Clipped ordinary calls execute it only when positive. Zero or negative affine assignments leave that nominal donor at identity, while still freezing its root and retaining its ancestors. This matches `ordinaryProposal`, `ordinary_nonpositive_is_unchanged`, and `RefinedChoresPhysicalPayment`.

The ledger's exclusivity is valid: for an internal recipient the new reserve does not increase and clipped envy-freeness pays the extra donor deficit; for an external recipient there is no donor extra and the unused-parent threshold pays the new reserve. Protected observers outside the component have nonpositive offered affine values. Thus a single payment is not spent simultaneously on a new extra deficit and an increased reserve. The old allowed reserves cover every other label along a donor return cycle. Actual own reductions and rival deficits then yield the stated positive-surplus margin.

Paid-component cycle contraction is purely combinatorial. `allowed_absorb` proves exact preservation of the complete allowed relation; the root frame/owner and reserves are unchanged. The absorbed cycle has at least two paid components. Its new component has no outgoing proposal; normalization terminates by decreasing component count, and a normalized finite quotient has an unpaid sink. Protected-label normalization retains the required representative. No synchronized partition or physical survivor reset is smuggled into this step.

### Factorial capacity and scheduling

The arithmetic `v(a)v(b)<=u(a+b)` follows from `(a+1)!(b+1)!<=2(a+b)!`; repeated combination gives the partition-wide bound. The single-component exception is essential and is handled: it cannot have an external target, so it is unpaid. Paying an unpaid size-`d` component multiplies its factor by exactly `2(d+1)`. A common dyadic weight bucket bounds the sum of all `d+1` input weights relative to whichever input SubCore leaves unused, so the factor pays the actual group weight without assuming equal package sizes.

The class universe has the stated cardinality `n2^n(4n^2+1)+n4^n+n2^n`. With total live-pool weight `S=n Lambda u(n)+1`, individual weight at most `u(n)`, and no roots discarded outside a selected group, a class with at least `n+1` live roots must exist. An ordinary operation strictly decreases live-root count. Terminal participant sets need at most `n+1` inputs. The formal `class_card`, `cannot_stall`, `capacity_bound`, `capacity_merge`, and `Group.paid_capacity` agree with this proof; the physical group-ID equality is used in the capacity bridge, not assumed away.

### Terminal material and completion

The affine terminal call differs appropriately from the ordinary clipped call: all assignments, including zero-own and empty assignments, execute. Nonnegative own affine utility follows from the primitive; participants' whole offered parents have nonnegative affine utility, and nonparticipants have nonpositive offered utility. The whole-assigned-parent guarantee is present in `RefinedChoresClosed.program_correct` and `RefinedChoresTerminalScans.terminal_executes`, so atomic extraction really contains a full large atom even if its recipient's own credit is zero.

Atomic and exhausted classes do not require common source components. The common terminal participant set lies inside each source component, which supplies the root-specific allowed return paths. For atomic extraction, the first-large-atom scan places every nonparticipant's mark on or below the offered boundary; an ineligible mark above it would have a gap composed solely of passed small atoms, contradicting separation. This protects nonparticipants even if the extracted atom is large to some of them; protection here is geometric, not an incorrect all-small assertion.

`X` is the union of actual assigned terminal suffixes. The leftover domain includes the untouched reference residue and all old/new physical complements outside `X`. At most `Jn^2` original atoms are charged once, yielding the stated remainder bound. The concrete source constructs recorded complement caches, proves extraction disjointness, and bounds each remaining original slot before summation (`TerminalGroup.remaining_slot_small`, `remaining_bounds`, and `finish_atomic_correct`). Thus no released material is dropped and no purely virtual SubCore piece is substituted for physical material.

In the exhausted branch, each outside observer has an actual retained-piece positive deviation of at least `(H-n/H)r_i` against each terminal participant. The aggregate physical-margin theorem preserves this through all frozen ancestors and other packages. Since the entire residue is at most `2r_i` and the margin is at least `2r_i`, it covers every eventual own recursive share. Recursion on the proper complement is valid. In the atomic branch the scale inequalities yield the two actual-domain separations with `alpha=2^(n+2)`, and the two children are positive complementary smaller populations.

### Full recording and constants

The paper's `S,J,H,L`, local allowances, and exponent arithmetic match `RefinedChoresParameters` and `RefinedChoresBudgets`: the snapshot term is at most `n!2^(22n+13)`, paid/terminal calls at most `n!2^(13n+8)`, preparation at most `n!2^(2n+5)`, and their sum fits `E(n)=n!2^(22n+15)`.

The recursive argument charges native child queries plus the ambient population times child cuts, not ambient population times all inherited queries. `Population.wrap_specification` and `wrap_complete_specification` implement precisely `(Q+n*C,C)`. The stronger `CoordinateSpec` quantifies over supplied known-coordinate sets; it does not treat arbitrary gaps in a disconnected child domain as free new endpoints. The capacity recurrence has unary strictly smaller children or two positive children summing to the parent. Its envelope is `(2n-1)(E(n)+n^2 E(n))`, giving `n!2^(25n+17)` before the initial total-cost records. Adding `n` initial Eval queries yields `n!2^(25n+18)`.

## What the public formal statement actually says

`RefinedChoresMain.deterministic_chores` (line 40) takes only `n>=3`, a finite atomless measure profile, and an arbitrary legal adaptive ordinary-query oracle policy. It returns an actual run of the fixed `program n`, with bounded trace length and bounded virtual Cuts, literal pairwise-disjoint shares covering `[0,1]`, exact envy-freeness, measurable shares, interval-coordinate bounds, known output endpoints, scoped queries, and legality of every query/reply. The program is defined independently of the cost profile in `RefinedChoresMainProtocol`. The main theorem calls `native_complete`, which instantiates population induction using `RefinedChoresLocal.concrete_step_complete`; it does not expose an unproved scheduler or local-step premise in the public theorem.

The formal theorem is for the unit interval. Its correspondence with the paper's interval formulation uses the usual affine coordinate transport. Finite unions come from the output's finite interval-piece lists plus the fixed endpoint convention; the main theorem does not literally repeat the phrase “finite union” as a separate conjunct. Finite nonatomic Borel costs on a bounded interval are represented by the finite measures/`NullSingletonClass` used here. No time or bit-complexity conclusion is asserted in either account.

The local import closure of `RefinedChoresMain` contains 474 `EnvyFreeResearch` files. A static scan found no `sorry`, `admit`, or explicit `axiom` declaration (the only word-match was “admit” in an English comment). This is a supplemental source check, not a substitute for the separately running build or an axiom audit. The full closure was hashed, not individually mathematically reviewed in its entirety. The inspected files below cover the requested concrete bridges and accounting; several predecessor primitive proofs are used through their stated proved interfaces.

## File hashes

All hashes are SHA-256, recorded at 2026-11-10T14:30:39.282230+00:00. Paths are relative to `/Users/alireza/temp/ef`. Whole-file hashes for the overview/general-results files include their unrelated sections, although this review covered only their chore passages. The imported-source manifest is `chore_manuscript_independent_review_import_hashes.sha256` (474 files), whose SHA-256 is `bcd3a7069ebfe24fddd5c8fd1fd47c6456db6e33e9977daf9779ff04903b6b5f`.

The following files were directly inspected (the long `ChoreComposition.lean` was inspected at the relevant reserve/proposal/zero-credit definitions and proofs, not read end to end):

```text
baf10a0977c5ad4b6651938f1a45a39e910cfae2000fa772be7b597f92c118f1  research/submission_focused/paper/sections/chore_proof.tex
7bb8325969c0093e0022d0282414be8f13cd4702c5029b77f7403aa7a771871d  research/submission_focused/paper/sections/general_results.tex
1f67dfecc8d95934421e97e5ff84422c8e4f726c5f27d9d8a39e76d94c0a7005  research/submission_focused/paper/sections/proof_overviews.tex
f3281315caf092cca238f1ba6a233dc4fd43e9ac8bf1be35e4998bfba04f75be  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresMain.lean
3a3c81111adb16736212d82022722f2ee7b33c5085b1d48821f96b255a81da9e  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresMainProtocol.lean
3a00acbe11c84f73ae5e055d93b0f96ff968130c6cc0a909e75f3c2dd56a2d5b  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresComplete.lean
94009c864e45bffd722f145f94a9e1d8ed2830e2f49e996908211f01977ee0cf  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresParameters.lean
a1e4f80fa91456a178ab8861b25629a90760229ebacd24a429ae89312a1f7cf7  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresBudgets.lean
522859882bf513eac7043735775b1a0d5b76aa2c6f39030a8eb5ea9d332b0094  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresDeferredPayment.lean
c46c4996bcdd09811f5f33834f8fd28389a5a3a3b734287ba983ac8ca1c6f431  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresPartialGraph.lean
83cec5020e58ef70cf6fda2ca1374639e84833fcc7b36566b33a8df522b73e89  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresNormalize.lean
33b79864aeebaf8475ca4ab410a63ecdaf148460cd5012daec63fa5fa001f37d  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresRootState.lean
5be56dc98fc88fd7c4bbcb7e888e840081df7572da1630f06ce11868be82df47  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresPhysicalPayment.lean
7eb4d9eec164646f0c777e8490224fdf92135af0479d06aa821b87aa9d52c0c2  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresGroupPaid.lean
4fc850f48af5cb7c32b9ea18d445ae6f64e59325ef5fe95424d65578e2191651  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresTerminalCohortFinish.lean
2e7d2804598e4bf8ec23562caec0fce1c7c97aed0af52b627c649f625b7edf07  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresTerminalAggregatePhysical.lean
df74b7d7bd9f01de0d59bcf120c1c7852e08a0864fb25e7fc118ca6bad1997f6  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresTerminalAggregateExhausted.lean
8e6921db812a35b77f604fedb457ef1383ebb4560026e7ad9f1a2e7dde6f3111  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresBucketCapacity.lean
5a0bd6efc4c388430c998b5466706052468c0c4dab5ddf1aac66e9e31aea2481  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresPool.lean
44be336eaa7d4b6b96e528f19bc783fad33172a96bc45b28801b17ee9982c885  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresStateCapacity.lean
af3acd6b92a17ad83a60953824d177fc96af5a96ce728dbe6ab91bfb8499675f  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresLocalLedger.lean
6f6a08a6f5989a1dbbc0b5dc97733eee281b53964386549403b5ba194b660ae6  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresChildLedger.lean
1088a6dac00e50d86b8f3652f9cceeb72ddd5c2e477ed116f596e328309b26ef  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresTerminalCohortRemainder.lean
2ddc19f3c1876826142e65b6200ea8e1a0a805bbdce60113ca8f82ff33522602  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresTerminalScans.lean
f4e064334b5557c37c2cde42fc8601014ecadbbe896c285bf87c91a1f4f5b21d  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresClosed.lean
fd09639a4ec4313aaf553bbbe6dca6b3485080da5eb39a127e4c047ea9ea480a  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/ChoresComponentPopulationCapacity.lean
f196d6d7a8306bffa3fbe43aaec04637365cd3fcfd6512d4de9a9733387f8c55  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresSpecification.lean
260a39e30a15ba05f945de536202ee059368e8940c8a2b457adc4dd638aae93e  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/ChoresComponentPopulationProgram.lean
240ad7c6f8d293e0d73bf22a74ac94a8f987604ab248f9588e1cfdfc77545734  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/ChoresComponentPopulationCoordinates.lean
38f1b6e813cc44c162affa1b9618433ce8c024d64209fe299f95f96f6f71f1cf  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresTerminalAggregatePool.lean
026624cd810135b27c58f30b0c1666b4ad78b78528d02b0ea3fbf67673ad2769  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresTerminalCohortPool.lean
d5f7e640597df42d8fbd4f67067d625930808bba6146267349a81c2a39d112e1  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RefinedChoresPrepare.lean
117e580691cb0b15f0d3c5190cd4602155f4aa3f9a1b092668e25abb637b56f1  research/formalization/all_main_results/verification/lean/EnvyFreeResearch/ChoreComposition.lean
```
