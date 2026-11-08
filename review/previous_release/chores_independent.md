# Independent review of the deterministic chore theorem

**Final status: accepted within audited scope.** I found no counterexample, missing mathematical assumption, or blocking gap in the deterministic ordinary Eval/Cut theorem as stated. This conclusion follows from a direct audit of the continuous construction and its accounting, supported by independent finite checks. It does not follow from compilation of the Lean artifact.

The audited claim is Theorem 2.1 (`thm:deterministic-chores`), proved as Theorem A.1 (`r8c:theorem`): for arbitrary finite nonnegative nonatomic Borel chore costs, the protocol returns a complete exactly envy-free finite-union allocation, permits every legal Cut response, and satisfies both the asymptotic bound `2^{3n log_2 n + O(n)}` and the stated explicit envelope `2^{14n(ceil(log_2 n)+1)}` for `n >= 3`.

## Evidence and scope

I read the model and theorem in the actual TeX, and all of the following proof dependencies, without relying on previous review reports or author notes as evidence of correctness:

- `sections/chore_proof.tex`, all 772 lines: preprocessing, packages, masked compensation, atomic and exhausted batches, the common-component schedule, integer pool floors, completion, and the entire query ledger.
- `sections/core_proof.tex`, all 494 lines: hungry existence, the canonical prefix dynamic program, persistent records, simultaneous realization, Core accounting, and the whole-cell rounding and splitter.
- `sections/baseline_subcore.tex`, all 177 lines: the many-parent algorithm, inherited allocation interface, equal-value chain, formal ties, and recurrence.
- `sections/offset_subcore_proof.tex`, all 264 lines: clipped and affine contracts, the virtual bottom, nonnegative targets, physical ordinary-query realization, and zero stripping.
- `sections/baseline_completion.tex`, all 108 lines: reserved-piece augmentation, the physical complements, and two-group completion.

I checked the PDF's stated theorem and Appendix A–E content against this source. The PDF was rebuilt during the review: its initial SHA-256 was `6fcdffcb341c059ed699c81c940af89b150c7efcc89bcc814401fceb2eb382b2`, an intermediate snapshot was `12fa56b38e4d99aeb86b19532543d051203793369fcfc2c90006997bfa14ebff`, and the accepted pre-editorial snapshot was `2cb128afb74e0bd288a08db4db36fcb5a1a4bb4b8165e506254a5544544aa7c8`. The exposition pass produced accepted snapshot `11f7134516c4919b389fadfaaf692ca484267a80f9540eadb2f15b271219c21f`, and three output-cut wording substitutions produced `8370c1da9ee87aedfeec7bfd0472bb63420acbb84f38427a2243baaaeb128a90`. Four light comparison-table separators produced accepted snapshot `151b40a104bead8c90f3d128368fc89767388c64e6ee1ed2c5d4f40ea218d123`. Following removal of the mixed-resource figure and unused TikZ imports, the accepted final PDF is `8274e3fe05605dde286cfb57eb8b8250d8eb11c4287fdc4544af57d1b077029c`. The extracted Appendix A–E text is identical in all seven snapshots, with SHA-256 `33cb32d08d1007f07705348593b832ba11e251f255d30259f483c7a5b8e40458`. The deterministic theorem text, model, and proof dependencies remained unchanged; the final edits to `general_results.tex` concern only other theorem descriptions. The receipt is closed against the updated `review/final_snapshot.json` and lists the individual hashes.

For inherited results, I consulted the primary mathematical text of Ye–Bai, Appendix F, including Algorithm 6 and the corrected chain and tie arguments; Aziz–Mackenzie, Algorithm 2 in the specified v12; Kakutani's fixed-point statement; and the full-version multicolor rounding theorem and floating-variable proof of Glaßer–Reitwießner–Witek. In particular, the manuscript uses Ye–Bai's omitted-final-recursion variant, not the larger original Aziz–Mackenzie recurrence. I independently checked the versions of these arguments reproduced in the manuscript. Archive metadata and commentary were not used as correctness evidence.

I also read the formal-scope statement and inspected the relevant finite masked-cost, task-injectivity, selected-root, and physical-credit lemmas in `R8Chores.lean`. They have the limited finite scope claimed in the paper. I did not compile Lean, and did not infer continuous correctness, pool survival, or oracle realizability from those lemmas.

## 1. Core and arbitrary legal roots

**The hungry existence and finite search argument check out.** In the local matching lemma, the Kakutani correspondence has nonempty compact convex values and a closed graph on the compact product of two simplices. If `Z` is the zero-coordinate set and `P` its complement, the originally matched agents in `Z` put at least `|Z|` demand in `Z`. Positive coordinates maximize demand, yielding `k >= |P| M + |Z|` and therefore `M <= 1`. Since the average demand is one, every column sum is one, giving the matching through Hall's condition.

The maximal-endpoint existence proof increases a strictly separated unanchored group without harming its old tie comparisons or outside observers. Strict comparisons remain strict after a sufficiently small increase. It consequently supplies the required anchored order. The sign-class identities are valid on balanced agent/parent sets; they imply anchored maximality and uniqueness of the prefix vector. Removing the last pair from an anchored witness therefore supplies exactly the smaller vector retained by the dynamic program, even if its matching differs. This justifies retaining one state per balanced subset pair.

**The extension to plateaus is not an unimplemented perturbation oracle.** `core_proof.tex:255–334` specifies permanent records shared by all states and failed candidates. Their primary values are actual physical costs; their secondary labels can be arbitrary rationals. A target whose real part equals a neighboring record reuses the physical endpoint. Otherwise strict primary bracketing makes an ordinary Cut legal and places every returned root between the physical bracket endpoints. Recording the other observers preserves the common order. The retrospective single-epsilon realization preserves the complete finite table, including earlier decisions and cross-parent target equalities. This is enough for the first-failure contradiction; no fixed point or perturbed-measure query is performed by the protocol.

The Core ledger includes every candidate, using `sum_{k=2}^n k^2 binom(n,k)^2 = n^2(binom(2n-2,n-1)-1)`, and charges recording evaluations. The whole-parent property supplies both contraction and the cutter-gap inequality. If positive residue remains, the whole-parent recipient cannot be the cutter: otherwise the cutter's envy-free comparisons force all prefixes to have full cutter value and leave zero cutter-cost residue.

## 2. SubCore, offsets, masks, and zero utility

**The recursive SubCore interface is coherent.** The inherited allocation, not an arbitrary unsupported benchmark vector, underlies the necessity argument for agents whose benchmarks exceed all uncontested values. The inherited owner's tie preference is needed there and is included. The equal-value chain uses strict order only within a single parent, plus envy-freeness and unused-parent comparisons. The backwards containments and forwards equalities identify the same formal suffix records. The selected set grows strictly, so its recursive sizes are distinct and the omitted final call gives precisely `S_k = 2^{k+1}-2k-2`.

**Parent-dependent offsets do not require cross-parent additivity.** All SubCore comparisons concern one suffix at a time. For clipped utilities, a genuinely queried target has positive primary utility and converts to the original cost target `g_{si}+t`; primary-zero targets can reuse a known clipped-zero endpoint. For affine utilities, the virtual bottom is a valid common inherited benchmark, but it is not incorrectly treated as physical empty. At the top level, nonnegative whole-parent utilities force nonnegative targets. In recursive calls, nonnegative inherited own utilities provide that guarantee. A primary-zero affine target may require a positive original cost `g_{si}`, and the proof explicitly implements that case.

**The pooled-mask simulation stays within the ordinary oracle.** Each actual observer appears in at most one task because source components are disjoint. When a pooled trim genuinely changes primary utility, it lies in that task's own block; cached component totals locate one physical interval. Other blocks are masked plateaus and are never queried as if the original observer were zero there. At most one Cut and `n-1` observer evaluations suffice. Retaining only the task's own-block intersection preserves its utility and the same-label comparisons, which are exactly the comparisons used by the package proof.

**The two zero cases are handled differently for a necessary reason.** A zero clipped proposal can have negative affine utility, so a continuing merge freezes that nominal donor at its old matching instead of claiming a credit. All nominal roots are still reserved and consumed. Atomic and exhausted batches instead satisfy the affine routine's nonnegative-whole hypothesis and retain affine-zero assignments. Their whole-parent certificate is therefore physical. The manuscript does not use a clipped whole-parent certificate after stripping.

## 3. Package reserves and actual material

The invariant `L_{i,p} >= D_{i,j,p} + H_s(i,j,p)` is strong enough for resets and closure. For an allowed live edge, the live reserve is its actual negative baseline deviation. Resetting along an old matching preserves every recipient's own baseline and uses only that root's original piece and private complement. Closure replaces the live reserve by the actual frozen deficit. Since each donor changes one label beyond an equalizer matching, the exact own-cost identity is valid.

Subtracting that identity from a rival's positive-minus-negative baseline decomposition proves the retained-positive-surplus inequality. This is important: the witness from one newly frozen root survives unrelated ancestors and different eligible sets. The proof does not merely establish that individual newly created witnesses are large before aggregation.

For a cycle advance, the payment split is valid separately for every advancing label and observer. An observer inside the source component needs to pay either an internal rival's one modified donor deficit, or an external rival's new survivor reserve. These are exclusive cases for a fixed rival, so the same credit is not spent twice. Old allowed internal reserves stay unchanged, and newly forbidden internal recipients have zero future reserve. An outside observer's eligible mark is no farther right than the first outside mark; an omitted mark on the wrong side would express a large gap as at most `n` small atoms, contradicting `H^2 > n`. Thus no omitted observer needs an unprovided new credit.

The physical donor complement has exact own reduction `C_i(E)-g_{s,i,p}`; charging `C_i(E)` alone would be wrong, but the text subtracts the original offset. The live root has never supplied a donor modification, so its private complement is available for the advertised resets. Frozen roots do not become live again. After closure, every ordinary released set is contained in passed small original atoms, and each original atom is charged at most once to the final unallocated union. `R_0` is never spent during the package stage, proving both sides of the residue bound.

## 4. Atomic and exhausted exits

In an atomic batch, the scan stops at a locally eligible mark. That mark lies at or before the first large atom's left endpoint and excludes an agent from both `A` and the large-observer mask `B`. The owner lies in `A`, and largeness makes `B` nonempty, so both sets are nonempty proper subsets. Every participant's offered whole suffix has nonnegative affine utility. Observers outside `A` retain their equalizers; the omitted-mark contradiction uses only small atoms to the right of the large atom.

The extracted domain `X` is the union of actual assigned suffixes, including formerly private portions. Because a whole affine output remains physical, `X` contains one complete large atom from a selected root. All selected roots have the same large mask, which proves the lower bound for every member of `B`. For an observer outside `B`, at most `n` assigned parents with at most `n` small atoms each give the upper bound. An unassigned root keeps its large atom allocated; an assigned root keeps the unremoved portion in its complementary prefix. Consequently large material is not silently left in the residue outside `X`.

In an exhausted batch, each recipient in `A` has a distinct selected-root witness against each outside observer, of size at least `(H-n/H)r_i`. Positive-surplus retention makes this an aggregate margin. With `H >= Jn^2` and `H-n/H >= 2`, it pays the entire physical residue. Recursing only on `N\A` therefore preserves comparisons against all inactive recipients, as well as within the active group. Formerly forbidden recipients may be used here because it is a newly paid closed operation, not a live reset.

## 5. Common components, pending proposals, and pool survival

The construction needs common SCC partitions, not common graphs, equalizer orders, or next recipients. For each root, an old simple path inside each source component connects the actual incoming recipient to the departing representative. Those paths lie in disjoint components and, with the new cycle edges, give a single permutation cycle. The same collection of old components merges in every root.

An unchanged source retains its frontier and first outside agent while the pool is filtered. If its target merges elsewhere, all recorded next agents still lie in one external target component. Its pending proposal therefore remains valid. If its source merges, the proposal is discarded and the new component is revealed once. This proves `G <= n-1`, `F <= n+G`, and `F+G <= 3n-2`, including the final closed revelation.

The scarce-class loss is bounded by `B_0 = n(4^n+2^n)`, and the surviving outside proposals have at most `n` target-component classes. The floor estimate follows exactly from `M_t=(n+1)M_{t-1}` and `M_{t-1} >= B_0`. Grouping costs at most another factor `n+1`. Thus the integer reserve `S=(B_0+n^2+1)(n+1)^{3n-2}` works for every allowed interleaving, without assuming divisibility. At one full component the protected representative `p_*` still omits the initial cutter in every root, so the exhausted class is proper. The base pool is too large for all roots to disappear into scarce classes.

## 6. Recursive completion and null material

The whole-cell rounding argument works with exact real coefficients: if no kernel direction exists, column independence yields an equation with at most `2r` positive fractional variables. Dropping it incurs final error at most `2r/K`; zero variables never return. Quantile refinement with `K=4rm` therefore gives the required positive lower shares, including for arbitrary plateau roots. A disconnected cell/color representation does not introduce a union query. Zero-total observer rows impose no constraint.

The reserved-piece augmentation is sound. Before recipient `i` acts, at least `2^i+1` untouched original public pieces remain, so her order statistic fits into every piece she reserved. Later augmenters only add cost. The earlier agents' touched bundles and chosen bundles are both contained in their designated sets, so their total obstruction is bounded by `sum_{j<i} |D_j| < |D_i|`, rather than being counted twice. An untouched member of `D_i` retains cost exactly `v_i`, proving the claimed envy-free selection. All unused reserves, tails, and public bundles remain in the complement.

The separation scale supplies the cross-group comparison `C_i(X)/(2m_D) >= C_i(R)` and its symmetric counterpart. Each child's domain is the exact complement of its group's retained partial allocation. Within groups, envy-free allocations add; between groups, the retained whole pieces protect the entire possible child allocation. Future endpoints only require current active observers because ancestor protection depends on whole-domain bounds. Disjoint child populations and strict population reduction give at most `2n-1` recursion nodes, including domination steps.

Zero-cost exits occur at completed envy-free boundaries. Giving the remaining domain to a zero-cost agent can only improve other agents' comparisons against that recipient. Empty and null components are retained in a physical allocation or complement throughout. The one- and two-agent base cases are valid with cached component values.

## 7. Complete query accounting

The tracked universe has at most `V=J(n^3+n^2)` observer/value pairs. Once a pair triggers `L` clearance calls, contraction makes it large permanently; no later residue reduction can trigger it again. Thus `J+VL` Core calls include all original and clearance work. Original equalizers, gaps, and atoms are recorded within the stated conservative allowance; subsequent masks, offsets, graph operations, and class tests are cached arithmetic.

A pooled call can have `d=n` tasks, and the ledger correctly uses `B_SC=n(2^{n+1}-2n-2)`. The bound of `J` compensation calls is charged to distinct nominal roots that freeze, including roots whose proposals are stripped. The splitter and augmentation counts include the complementary material and all endpoint recording. Input component values are inherited from the enclosing call; top-level totals are covered by Core's initial allowance.

I checked all factors in

`F_n = (J+VL)Q_Core + (n+1)Jn(n-1) + J B_SC + 19n2^n`.

The displayed integer inequalities give the stated explicit envelope after accounting for recursion and base cases. Asymptotically, `J` is a polynomial factor times `4^n(n+1)^{3n-2}`, clearance adds only polynomial/logarithmic factors, and Core adds `4^n` times a polynomial factor. Recursion is linear in `n`. The resulting leading exponent is indeed `3n log_2 n + O(n)` for queries, and the same bound covers cuts since each physical cut is a counted query.

## Independent checks

The review directory contains an independently written rational simulator, `chores_independent_checks/check_primitives.py`. It uses no manuscript or Lean implementation. With fixed seed `2718281828`, it passed:

- 180 prefix dynamic-program profiles for 2–4 agents;
- 600 clipped and 600 affine SubCore profiles for 1–5 participants, with several parent counts;
- zero densities, exact ties, zero-valued parents, masked plateaus, original-cost affine zero targets, and leftmost/rightmost/interior choices among plateau roots;
- all formal envy-free/benchmark/unused-parent/whole-parent assertions, all source trim-request bounds, and one exercised equal-value chain repair.

The run made 1,533 recursive SubCore calls, inserted 4,468 records, and counted 3,456 fresh physical cuts. The simulator uses rational piecewise-constant parents; it does not simulate the enormous complete pooled protocol, singular continuous measures, or real external Eval calls. Generality in those directions rests on the audited arguments above.

`chores_independent_checks/check_ledger.py` checked the pool floors, geometric scale conditions, Core/SubCore bounds, two-group preparation, and explicit recursive envelope using exact integers for `n=3,...,100`, and the SubCore recurrence through 30 participants. These are finite consistency checks, not substitutes for the all-`n` inequalities in the proof.

## Findings and remaining questions

There are **no blocking findings and no unresolved correctness questions within the audited scope**. No theorem-level repair is requested.

Two optional clarifications would make the proof easier to audit:

1. At `chore_proof.tex:131–145` or `:362–379`, explicitly note that every edge in a union of perfect matchings belongs to a directed permutation cycle, so the graph has no edges between distinct SCCs. This makes the assertion that exactly the prescribed cycle components merge immediate. The construction already guarantees this fact; it is not an additional assumption.
2. At the first physical-domain convention, state a fixed endpoint-membership convention for adjacent intervals. Nonatomicity makes endpoints costless, so assigning them consistently gives literal disjointness and completeness without changing any query or inequality. This is a representational clarification, not a null-interval disposal step.

This acceptance covers the deterministic theorem and the dependencies listed above. It does not certify the other main theorems, polynomial bit complexity, a production implementation, or a complete Lean formalization. Source hashes, test results, and the exact review scope are recorded in `chores_independent_receipt.json`.

## Final editorial reconciliation

I read the revised introduction, proof overview, upper overview, and related-work prose for their chore-facing claims. The deterministic bound, nonnegative nonatomic domain, absence of density/common-support/strict-positivity assumptions, pooled compensation explanation, and cited SubCore provenance remain consistent with the accepted theorem and proof. The overview navigation does not change the logical dependencies. This brief reconciliation does not extend the review to the randomized theorem.

At the exposition checkpoint, I independently verified that the actual file changes matched `editorial_delta.json`; every source from the original theorem/proof audit still had its accepted hash; all Lean source hashes matched the pre-editorial checkpoint; and the PDF's extracted Appendices A–E were byte-identical. No new correctness issue arose. Acceptance at that checkpoint was bound to PDF SHA-256 `11f7134516c4919b389fadfaaf692ca484267a80f9540eadb2f15b271219c21f`. The earlier independent tests were not rerun because their mathematical inputs were unchanged.

For the subsequent wording synchronization, I read the changed abstract and statement clauses. Reversing exactly those three prose substitutions reconstructs the previously accepted `paper.tex` and `general_results.tex` hashes. The deterministic chore subsection is byte-identical, as are the model and all proof dependencies. That PDF's Appendix A–E text remains byte-identical, and actual Lean files still match the checkpoint hashes. This introduced no new chore-theorem issue and accepted PDF SHA-256 `8370c1da9ee87aedfeec7bfd0472bb63420acbb84f38427a2243baaaeb128a90`.

The table layout change adds exactly four `\midrule[.25pt]` lines; deleting those lines reproduces the prior table source hash. I checked that delta against the actual source, verified its snapshot, and again compared the PDF's Appendix A–E text. No substantive statement changed, and acceptance extended to PDF SHA-256 `151b40a104bead8c90f3d128368fc89767388c64e6ee1ed2c5d4f40ea218d123`.

The last presentation change removes the mixed-resource figure, its overview references, and unused TikZ imports. I read those changes, verified every actual paper/Lean source against the synchronized manifest, and confirmed that the deterministic theorem and the entire extracted Appendix A–E text remain unchanged. The removed illustration is not a dependency of this theorem. No new finding or unresolved question arises. The final status is **accepted within audited scope**, bound to PDF SHA-256 `8274e3fe05605dde286cfb57eb8b8250d8eb11c4287fdc4544af57d1b077029c`.
