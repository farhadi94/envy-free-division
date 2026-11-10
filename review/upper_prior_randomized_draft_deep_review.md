# Independent deep review of the revised randomized proof draft

Date: 2026-11-10. This is a fresh mathematical/source comparison of the new draft's maximum-determinant selection, deletion stability, supported rounding, inherited boundaries, and first-bad correction probability. It does not adopt the conclusion of the earlier core-source review. No draft or Lean source edits, compiler runs, commits, or publication were performed. The canonical paper was not changed by this reviewer.

## Verdict and required corrections

**No mathematical blocker was found in the intended deep construction. Three statements should be corrected before integrating the drafts.** One is an unrestricted maximum in the main proof; two are overcompressed statements in the overview. The intended statements are supported by the reviewed Lean sources. The exact corrections are below, followed by the proof checks and limits of this review.

### D1 — Main proof's maximum must range over grid cells

At `randomized_paper_revision.tex:263`, the displayed definition is

```tex
A_{ij}=\max_{E\subseteq R}|(w_i-w_j)(E)|.
```

Read literally, this maximizes over all subsets of the reserve, not over the retained refined cells. That is a materially different quantity, closer to a total-variation discrepancy; the maximum-determinant witness and per-cell `A_{ij} <= eta` arguments do not establish the claims with that interpretation. For example, many positive cell discrepancies can add over a union even when every individual discrepancy is tiny.

Introduce the finite family `\mathcal P_R` of retained refined grid cells and write

```tex
A_{ij}=\max_{E\in\mathcal P_R}|(w_i-w_j)(E)|.
```

Retained positive mass ensures this family has a nonempty relevant domain; alternatively specify the empty maximum as zero for a total definition. Also explicitly bind `E\in\mathcal P_R` when defining the envelope `H_j(E)` around line 548. The deletion lemma already explains that its `A_{ij}` is a maximum **full-cell** disagreement, so this is a definition repair rather than a new proof. The directly reviewed `RefinedUpperPayments.allocation_spec`, `RefinedUpperCorrectionConditional`, and `RefinedUpperActualCorrectionBound` all use the finite-table `cellGap`.

The targeted search found no second unrestricted maximum over `E\subseteq R`. Other maxima in the inspected portion are explicitly over row pairs or labels. The envelope's cell range is implicit and should be made explicit with the same notation.

### D2 — Overview must retain the rank-one tie criterion

At `randomized_overview_revision.tex:13–16`, the overview says to choose two cells maximizing the absolute determinant, and immediately claims that those cells control every linear combination. Determinant maximization **alone** does not imply this in degenerate cases. With vectors `(0,0)` and `(1,0)`, every pair has determinant zero; selecting the zero vector twice fails to control the first-coordinate functional.

Replace the instruction with, for example: “choose a pair by the lexicographic determinant-and-total-mass rule of Lemma [Maximum-determinant witnesses], allowing repeated cells.” The main appendix already states the correct secondary criterion. `RefinedUpperWitnessSelector.score`, `select_spec`, and `rank_one_mass_witness` confirm why it is necessary.

### D3 — Overview's preservation claim must specify real recipient coordinates

At `randomized_overview_revision.tex:29–31`, “Sorted-slot rounding preserves zero and one coordinates” is too broad. Underpaying/trimming can change the unused-color coordinate; the robust discrepancy argument needs preservation only of fixed **real-color** coordinates. The formal statement is deliberately `FrozenReal`, not unrestricted `Frozen`, for the final rounding.

Use: “Supported sorted-slot rounding and trimming preserve all fixed zero/one coordinates for real recipients.” The appendix around lines 509–512 already makes the needed distinction. `RefinedUpperSparseFloating.support_error` expressly permits the unused color to change, and `RefinedUpperWholeLinear.exists_whole_payments` proves `FrozenReal` for the rounded allocation.

## Clarifications recommended for exact source correspondence

1. At main-draft lines 225–227, replace “two unnormalized row values” with an explicit vector, preferably `(nu_i(E),nu_j(E))`, where `nu_i=mu_i/mu_i(B)` is normalized by the **original** buffer. The formal `physicalCumulative` divides by original-buffer mass, and `recorded_table_pointValues` identifies it with the actual cached table. The guarantee works for arbitrary later normalization coefficients; this does not say that the selected pair itself is invariant under row rescaling. Rescaling can change the secondary total-mass tie criterion. The current wording could instead mean “before retained-reserve normalization,” but that should be explicit.

2. The appendix presents floating and supported rounding as a finite construction, while the executed formal selector is `RefinedUpperLinearSelector.firstValid`: it enumerates finite ownership tables and chooses the first satisfying the proved whole-payment inequalities. The floating/rounding argument proves that such a table exists. This is not a query-bound problem or a mathematical counterexample: both use only the already queried finite table, and either can be implemented with Borel finite choices. For literal correspondence, say that the protocol may select the first valid finite ownership table after the existence proof. This also gives a short direct measurability argument without leaving a choice of kernel direction implicit.

3. The overview's deletion sentence at lines 17–18 should identify the two grids: a protected endpoint is tested in the **augmented** grid, while the coarse parent must survive in the **deleted/original** run. The main proof handles this correctly. Suggested wording: “If an inserted point is unprotected in the augmented run and its coarse parent survives in the original run, deleting it leaves all peeling choices unchanged.”

These are precision/source-correspondence recommendations; D1–D3 are the concrete statement fixes I recommend treating as required before integration.

## Mathematical checks

### Maximum determinant and deletion stability

The nondegenerate Cramer-rule argument is sound: replacing either member of a maximum-determinant pair bounds both coordinates of every competitor in that basis by one in absolute value. The determinant-zero case uses nonnegativity, a common ray, the maximum total mass, and repeated pairs. No positivity of the determinant or strict positivity of all cell values is silently required.

Deletion of unchosen alternatives is valid because the score is fixed and the surviving geometric order is unchanged. The stronger insertion/deletion step needs more than that simple fact, and the draft supplies the right additional argument: at a first discrepancy between runs, an old-grid winner must involve the merged cell; that would remove its parent, contradicting survival of the parent in the old grid. `RefinedUpperPeelingLocalEdit.local_edit_agrees` formalizes exactly this asymmetric assumption: the edited/original parent survives, and all augmented selected cells avoid the inserted endpoint. It does not assume both executions already agree or assume stability as an oracle property.

`point_unprotected_control` derives unchanged peeling choices and uses a final retained maximum-determinant pair to bound both split-cell discrepancies by `2*A`. Its coefficients `u,v` are arbitrary reals. Consequently, retained-reserve normalizers may depend on the sample: the proof never conditions a fixed-measure interpolation theorem on those normalizers. The draft's final `k^2` row-pair witnesses are essential and are present; protecting peeling witnesses alone would not establish the partial-cell bounds.

The run-completion/availability obligation is also available: at most `2r` coarse parents are removed, each original row loses at most `2r*sigma`, and `4r <= q+1` leaves at least half its mass. Inserting one sample changes no coarse parent or coarse-row bound. Thus the augmented procedure can complete as well. The formal actual-control adapter discharges this via the augmented-supply theorem rather than assuming successful peeling.

### Exceptional set and actual sampling law

The bad set is not “a finite set of endpoints” of the original grid. It is the set of test points that become protected when individually inserted into the grid. The draft defines it this way, as does `protectedBad`. This distinction is necessary because that set can have positive measure.

For a fixed augmented sample of size `m+1`, at most `4r+4k^2` distinct sample coordinates can be charged. The selection procedure depends on the sorted geometry and fixed original row cumulatives, not sample identities. Exchangeability therefore gives the division by `m+1`. `RefinedUpperStabilityProtectedEvent.integrated_coincidence_le` proves the measurable event estimate; the underlying exchangeability module even handles coincident coordinates through fiber charges. Atomlessness justifies the simpler distinct-coordinate prose.

The coarse grid and original buffer must be fixed before the iid draw; they are. `RefinedUpperActualBadGrid.actual_bad_grid_probability` transports the estimate using the actual `UpperGridMerge.iid_sample_law`, under admissibility and answer measurability. Thus the source does not replace history-dependent queried samples with unjustified independent roots.

The actual pointwise-control theorem excludes an augmented bad set that also contains outside-reserve points and finite grid endpoints. Adding those points costs zero restricted cutter mass. The paper instead treats grid endpoints by their exact zero interpolation error and cells outside the reserve by zero rows. These are compatible ways of handling the boundary cases; no positive measure is silently discarded.

### Supported rounding and the linear discrepancy bound

The counting argument includes the unused color in the fractional-coordinate count. Each split cell has at least two fractional coordinates because its nonnegative coordinates sum to one. At a fractional basic state,

`v <= c+k+d`, `2*c <= v`, and `v > 4*k`

imply `d > v/4`. Each coordinate has nonzero coefficient in at most `k` discrepancy equations. Hence some kept discrepancy equation has support at most `4k`. The formal `rank_bound`, `column_degree`, `sum_support`, and `sparse_row` establish these statements without assuming a sparse plan in advance.

At the time a row is dropped, its value is still its original value zero. Only its then-fractional support can subsequently change; each coordinate changes by at most one and each coefficient is bounded by `A_ij`. This controls the **entire eventual** error by `4k*A_ij`, rather than adding a fresh error at every later floating step. `exists_robust_float` makes that endpoint guarantee explicit for every later box-valued table preserving fixed real coordinates.

The slot-matching construction has capacity at most one per physical cell across recipients. Matching only positive incidences gives support preservation. Trimming removes cells from the newly matched split-cell part, while previously integral allocations remain fixed. The owner's already integral load cannot exceed its target because the floating owner equation is exact and remaining loads are nonnegative. The sorted-slot lower bound and final trimming therefore leave an owner deficit in `[0,min(t_j,eta)]` without violating the frozen-coordinate premise. The formal `exists_supported_rounding`, `owner_deficit`, `owned_positive`, and `exists_whole_payments` implement these connections.

The paper is right to emphasize support preservation: using only an arbitrary disjoint rounding with an owner-load approximation would leave a genuine gap, because a formerly zero real-color coordinate could enter a dropped equation. That gap is absent here.

### Inherited boundaries and envelope probability

The candidate correction's virtual boundary contains grid boundaries, the two new endpoints, and endpoints of every previous **accepted** correction. Rejected attempts alter history but leave no hole. Before correcting recipient `j`, there are fewer than `k` accepted corrections; `RefinedUpperRetainedGeometry.point_count` gives `2*(accepted.length+1) <= 2k` endpoint slots. Charging `2*A_ij` per slot yields `4k*A_ij`. The draft explicitly includes these inherited boundaries and correctly avoids counting only the latest two endpoints.

The supply invariant follows from the whole-payment bounds and the checked accepted-payment caps, independently of interpolation being good. With `sum t_j < 1/16`, `k*lambda*eta < 1/16`, and `lambda >= 16k`, all removed pending/completed payments consume less than `1/8` of any reserve-normalized row. This supports the endpoint domination and the target-fit argument even after earlier rejected attempts.

The maximum envelope controls all observers simultaneously. Its total mass is at most the finite retained-cell count `N`, not `k*N`. The circular law and `w_j(S)>7/8` give the deliberately loose `2*eta*N` mean bound. Markov at `lambda/4` yields `8*eta*N/lambda`. The discrepancy budget `4k+4k+lambda/4 <= lambda` follows from the stated `lambda >= 16k`. No hidden observer union bound restores an extra population factor.

### First bad endpoint, finite retries, and unconditional Repair

The stopped process must continue only after a **good and rejected** attempt. The draft says this, and `RefinedUpperFirstBad.hit`/`hit_le_fixed_point` use precisely that continuation event. They do not assume all histories are good or condition on eventual success.

The probability of a fresh bad endpoint is at most

`a=(32*k/7)*delta0=1/(7168*k)`.

A good rejection is contained in the envelope event and has probability at most `b=1/4`. Thus `B*=4a/3` satisfies `a+B*b=B`, bounds the first-bad probability for every finite retry horizon, and good exhaustion contributes at most `b^ell`. The numerical total is

`k*(B*+4^(-ell)) <= 1/5376+k/(4*s^2)`.

`RefinedUpperCorrectionBatchProbability` carries a concrete `Good` invariant combining physical supply, history consistency, and the exact accepted endpoint count. It proves preservation through good rejection and good acceptance before invoking the stopped-loop bound. `RefinedUpperActualCorrectionBound` then discharges its analytic good-endpoint and bad-mass premises from actual preparation. `RefinedUpperRepairProbability.probability_le` integrates the fixed preparation fibers and adds bad-grid and cycle-isolation exceptions on the original law. `RefinedUpperRepairFailure` substitutes the revised counts and closes the numerical `<1/64` bound. No success, reserve-mass event, or stopped-retry estimate is left as an unexplained hypothesis of that final local failure theorem.

The arithmetic `8*eta*(2m)/lambda=1/4` and the endpoint constants agree exactly with the draft. One stale **source comment**, in `RefinedUpperFirstBad`, still says the application uses `b=1/7, B=7a/6`; the theorem is parameterized and the actual instantiation uses the correct `1/4,4a/3`. This comment should eventually be updated, but it is not a proof mismatch.

## Scope limits

This review targets the listed new deep steps. It does not supply a fresh compilation/axiom receipt, a complete audit of every imported geometry or probability theorem, or final whole-paper proofreading. In particular, I did not independently rederive the full assignment-isolation proof, all Snapshot cases, or the global domination potential in this pass. The actual-probability assembly was checked for which assumptions it discharges, not treated as evidence that every imported lemma is semantically correct by virtue of compiling. No change to the canonical theorem claim should be inferred from this report while end-to-end integration is pending.

## Reviewed source identities

Hashes below are SHA-256 at report creation. The paper and overview were left unchanged by this reviewer. The source workspace is shared; later edits require checking these identities. Lean filenames are relative to `research/formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/`.

| File | SHA-256 |
|---|---|
| `randomized_paper_revision.tex` | `d184e5abe8609642b031bcf3b278dc3bce2884cc582aa0dea1d36262bef780c5` |
| `randomized_overview_revision.tex` | `7490e454bf985779f7afdb3ea190c8c41c427d6b575f92cd6cb031ad59bf95f0` |
| `RefinedUpperWitnessSelector.lean` | `47cfbbeaf9f41072251f74fd8ac89984f02a2aa4560c64be0892204154428f09` |
| `RefinedUpperStabilityProcedure.lean` | `b3d0686dee3536d8b9a2ca40da6ecd8b63d326d31efcccd90557654fe2b70f17` |
| `RefinedUpperStabilityActualControl.lean` | `560134231acb533f58e7c09a5ab6831dcb2626d446f21ef2e8a6d079e2440a1d` |
| `RefinedUpperStabilityExchangeability.lean` | `3266cf13cd6fbc23ee4d281d91e3fc08782ed25fc92e12cba0af3e4b7ad7ff1d` |
| `RefinedUpperStability.lean` | `b78d527fc8e87fa628ee113f890034f13b7fc7853cb8a6e214e61caf1a3afd0d` |
| `RefinedUpperPeelingStability.lean` | `b25f76fac67bcc737c68c7b5b0ca8390a86e132f1652b497948f3398d31c4cbe` |
| `RefinedUpperActualBadGrid.lean` | `a7edd63b3f61ae189e4e4166017e647586012f86fa23ab64123c8d6f095b4b7c` |
| `RefinedUpperActualCorrectionBound.lean` | `2214a69b8642b387229ab9d6ad14669fee7432b6a0ec781b9b29f98d14b698ae` |
| `RefinedUpperCorrectionBatchProbability.lean` | `e7038bd8c4327dcd748a52ce6303f417d34099a900906d884f62c3c3aa636b50` |
| `RefinedUpperCorrectionProbability.lean` | `2e4f001dbe847b7197188e5f0af5d185ea0e009618905fc1a86c4f9b66156641` |
| `RefinedUpperFirstBadFinite.lean` | `066d9e21f6a3af17fc5b7dd5e3bfe68126ab5b7d47fac84293dda34daf11b647` |
| `RefinedUpperFirstBad.lean` | `d4e2e93f259be1de65ca399bdedbaad9ed8684bce569076a2c4a770606ddbebf` |
| `RefinedUpperWholePayments.lean` | `0f0b3ac7ff7baf5bfeb5951d20cf252cb26c9fe8b722faffb72186e11f5f1814` |
| `RefinedUpperPayments.lean` | `bc2a0899cefec318e80b24827eb570f7635b7b3a0bc4f488222037fcbb4f8506` |
| `RefinedUpperRawPayments.lean` | `e57142f91e166af062063be1fe350f643816ae56ab7fcfdcf99014ce056587cb` |
| `RefinedUpperWholeLinear.lean` | `d15f95c7c0757a74602ec8b42cd967b115e61794a60fc7cd30c145c9fe0b42b2` |
| `RefinedUpperSupportedRounding.lean` | `bcf7276597394249ee8d588a4ce677de2acdd9260fc36bed5d9dbdf18d75f3e8` |
| `RefinedUpperIteratedDropping.lean` | `46a1ce16b87ae696693f477b81c15c8625cf00511f4af05089df8cbce179529b` |
| `RefinedUpperSparseFloating.lean` | `3a9af48a0c7221d9c087c5507da2e19ec3a0a92b235655eec1bf34fd423d2947` |
| `RefinedUpperPeelingLocalEdit.lean` | `d758af2a3aeb5f4f109c26182e70e8c6d7551247fc060d34c788d4db7d80f4e9` |
| `RefinedUpperStabilityPointwise.lean` | `1757fbeab4c49288621e7d55b698c9576ed3b2499147db96095252f0f671848a` |
| `RefinedUpperCorrectionConditional.lean` | `1b090a9fef8b003a505605077db75c2c98fa6e06666f47a2b63a30bf00020707` |
| `RefinedUpperStabilityRecordedProcedure.lean` | `aa90d12af5147c35da5469a0100384267c5e1043b1e4db23efa23f42dd5587b8` |
| `RefinedUpperRetainedGeometry.lean` | `c7ea59388f66695348955a4f8b8c2690e85e460f73e8cf5050cb54777e50a746` |
| `RefinedUpperFailureAllowances.lean` | `e51f341415a52a8032ab433eb91cd341b419ce6acb256388c724c1a56de65268` |
| `RefinedUpperRepairEventProbability.lean` | `b14d82b1a9bca5d3681277fe573583e529aa1047a40d006e22e4eed04c5349e5` |
| `RefinedUpperRepairFailure.lean` | `4dbfe5e7a7cdac86a9e26c5024555eaf7f735d35a99999314bd86ed49982577f` |
| `RefinedUpperLinearSelector.lean` | `5435c665909bfde32308251108da2c842d6c89d5c0720782986f864ccdd29a70` |
| `RefinedUpperRepairProbability.lean` | `6241d4eab104c9a1bd74b736ca2b236c1c10f21ae6e12c6f31493fd25bca0d19` |
| `RefinedUpperStabilityProtectedEvent.lean` | `735c1f8add2154f7b85d55a546454d0ec075aa2866de5662ea6e2f1949617802` |
