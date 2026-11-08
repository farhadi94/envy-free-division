# Final paper/formalization correspondence review

**Verdict: main-statement correspondence supported, with precise release/model edits below; not build certification or release acceptance.** This independent read-only review found no change needed to any of the four advertised main orders. The proposed formal-scope appendix is appropriately limited to the four main results and explicitly distinguishes conservative formal algorithms from sharper auxiliary ledgers. Its promotion must wait for the final frozen-source closure/axiom audits and the separate new single-next-action bridge review.

Reviewer: `/root/final_paper_correspondence`. Only this report was written. No canonical manuscript, Lean proof, configuration, release artifact, or prior review was changed. No Lean/PDF build was run. Timestamp: 2026-11-08T03:00:16.485312+00:00.

## Exact result correspondence

| Manuscript claim | Inspected public endpoint and comparison |
| --- | --- |
| `thm:deterministic-chores` | `EnvyFreeResearch.Full.Chores.Main.deterministic_chores`, in `Full.ChoresMain`: n ≥ 3, finite nonnegative atomless costs, any legal full-history ordinary oracle; actual bounded execution of a cost-independent program from empty history; literal complete pairwise-disjoint finite-interval allocation and exact chore EF. `bound` is `min (n^(3*n)*2^(27*n)) (2^(14*weight n))`, so both the leading exponent and explicit manuscript envelope follow. One/two-agent bases are in the underlying construction, rather than this n ≥ 3 endpoint. |
| `thm:general-upper` | **`EnvyFreeResearch.Full.UpperGlobalPhysical.randomized_exact_envy_free_oracle`, in `Full.UpperGlobalOraclePublic`**: a single jointly measurable tape/transcript `next`, almost-sure actual ordinary execution returning `.done a`, physical partition of `[0,1]`, both EF orientations, and expected actual query/Cut supremum bounds `100*A*n^21*log₂(2n)^2` / `49*A*n^20*log₂(2n)^2`. `fallback : Fin n` encodes n ≥ 1. No density, positive-total, normalization, common-support, assumed-success or assumed-runtime premise is present. The older polynomial endpoint alone was a phase-run statement and is insufficient as the final named ordinary-protocol endpoint. |
| `thm:nonnegative-lower` | `NonnegativeRawMain.optimized_attempted` gives exactly `n*(n*p-1)^2/(2*(n-1))` at `n*p ≥ 3-2/n`, under success on every normalized finite-step density profile in `[1/2,3/2]`, for either orientation. `quadratic` gives positive constant `p^2/8` for `n*p ≥ 3` on answered costs; pointwise domination by attempted cost transfers it to the model's Q. The charge is unconditional on the uniform profile, not conditional on success. |
| `thm:mixed-mc` | `MixedIntervalMain.attempted_expectations_unbounded` and `relative_attempted_expectations_unbounded`, plus `finite_step_attempted_expectations_unbounded`, use actual normalized integrable density rows, a root-rule parameter fixed as `.leftmost` or `.rightmost`, arbitrary measurable tape/next action, and raw finite interval returns. The conclusion is supremum of unconditional attempted expectations equal to infinity. Additive ε < 1 is obtained by α = 1; signed relative multiplicative EF uses its exact normalized-profile equivalence to the α-cake comparisons. Finite-step hard profiles already suffice. This implies the general signed-measure impossibility without needing to represent every singular signed measure. It does not assert one fixed input with infinite expectation. |

The abstract, introduction, table, main statements and proof overviews agree on the four orders and on exactness versus approximation. The lower bounds do not gain an unsupported superquadratic order or fixed-variation hardness. The table correctly separates Q, C and output fragmentation. Nonnegative Cut uniqueness on the hard density class removes a hidden root-choice issue in that lower bound.

## Model interpretation and qualifications

The positive endpoints use finite Borel measures on ℝ with null singletons; manuscript measures on `[0,1]` are covered by the usual zero extension. All finite Borel nonatomic measures on the line meet this interpretation. Measures outside the resource do not change the result. This standard identification is a mathematical correspondence, not an inspected formal zero-extension compiler.

`AdaptiveOracle.Policy` takes the complete answered query history and current query. Its legality quantifies every history. This covers varying legal roots on repeated requests; it is not a leftmost-only positive algorithm. Its public randomized measurability hypothesis is joint measurability of `answer oracle`. The informal words “the past” should be made explicit as the answered transcript, rather than suggesting access to private random coordinates not exposed by queries. A stronger oracle-observation model would require a separate statement/adapter.

Upper costs in the public endpoint are answered-count suprema over all fuel bounds for **one** next function. `single_protocol_output_almost_sure` and returned-cost stabilization link them to successful actual executions almost surely. Thus unsuccessful internal trials are included, and the fact that a hypothetical illegal terminal request is not an answer does not discard positive-measure cost: almost every tape actually returns under the legality assumptions. I source-inspected the new public assembly and operational output bridge, but defer the internal stability/least-prefix proof audit to the independent randomized reviewer.

The lower raw grammar has a finite unsorted list of bounded pairwise-disjoint `(left,right]` records, owner labels and one owner of 0. Validity is geometric, not fairness dependent. Arbitrary finite fragmentation and free endpoints are admitted; invalid returns are failures. The measurable decoder preserves physical shares and all costs. This is a standard finite partition encoding, not a universal parser/canonicalizer for arbitrary redundant overlapping union expressions or malformed machine bytes. The manuscript's fixed endpoint convention and standard finite-output model are consistent with this interpretation. The draft appendix appropriately does not claim universal parser coverage.

The randomized formal tape combines independent continuous and finite discrete primitive coordinates. The manuscript's ideal uniform-real wording uses the routine mathematical sampling of finite labels/permutations from uniforms. A universal formal pushforward adapter from a single uniform-real stream is not claimed by this review. No bit-complexity implementation is claimed in either source.

## Conservative formal variants and auxiliary claims

The draft paragraph on conservative choices is necessary and accurate. For chores, a fixed sufficient clearance length `14*n*weight n` replaces the paper's least sufficient L, and generic physical/observer endpoint recording adds polynomial overhead. The actual formal query bound proves both stated main envelopes; it does not assert literal equality with `F_n` in `(r8c:node-query)` or the cached `B_SC` ledger. The chore independent source review documents the full local/recursive integration and that these costs are discharged, not assumed.

For randomized completion, the reviewed formal ledger includes `(n+1)*(N+1)+2*n` normalization/initial queries and `(N+1)` additional Cuts, whereas `(r6u:global-cost)` in the paper has sharper `O(n)` / `O(1)` additive terms. These differences preserve the main polynomial exponents. The formal endpoint also does not itself state the conditional fewer-than-eight-trials guarantee, high-probability wrapper, or endpoint-storage bound. Those remain paper auxiliary arguments. The manuscript explains the sharper ledger through initial totals plus a single terminal two-agent division, so the mere fact that the conservative formal accounting is weaker is not a contradiction requiring the paper's main or auxiliary mathematics to be weakened.

The mixed formal proof directly mirrors capture for rightmost roots, while the manuscript gives an extra-Eval reflection simulation. Both prove the same main model/result. The scope appendix must not imply proof-by-proof identity.

## Precise required edits before promotion

1. **Final endpoint selection:** in `formalization/release_staging/main_results.json.draft`, change the `randomized_upper.module` to `EnvyFreeResearch.Full.UpperGlobalOraclePublic` and its public declaration to `EnvyFreeResearch.Full.UpperGlobalPhysical.randomized_exact_envy_free_oracle`. Update the PLAN table, example audit roots, selected closure/inventory, final umbrella/coverage and any package description consistently. The inspected manifest still named `UpperGlobalProtocolPublicPolynomial`; preserving that name as the sole final endpoint would leave the new one-next-action result outside the advertised release root.
2. **Manifest claim in `formal_scope.tex.draft`:** the current JSON lists names and pins, not precise assumptions. Either enrich it with the hypothesis/encoding fields summarized above, or replace “Its endpoint manifest records the precise hypotheses and the correspondence between the public Lean statements and the four theorems.” with: **“Its endpoint manifest identifies the public Lean statements corresponding to the four theorems; those statements record the precise hypotheses.”** The latter is a concise accurate repair.
3. **Oracle wording precision in canonical `general_results.tex`:** replace “Here nonanticipating means that a reply may depend on the past and the current query, but not on future random choices.” with: **“Here a policy is a measurable function of the answered query transcript and the current query; it has no access to future random choices.”** This resolves ambiguity while retaining the intended ordinary oracle model. If a broader observable-randomness model is intended, do not use this editorial patch to conceal that stronger claim: it requires a corresponding formal adapter.
4. **Coverage promotion only after gates:** replace canonical `formal_scope.tex` and `ai_methodology.tex` with the corrected proposed drafts together, once the frozen builds and fresh reviews pass. Current canonical text explicitly denies complete main coverage. Publishing the new Lean sources with that old text would be inconsistent; publishing the new claims before audit completion would be premature. The new verifier's promised placeholder/project-axiom rejection and transitive dependency whitelist are present in the staged script, but its successful application to the final package remains a release gate.

No new figures, theorem-order changes, weakened main bounds, or expanded introduction are needed. Adding a long list of Lean filenames to the paper would reduce readability; keep detailed hypotheses/encoding notes in the artifact manifest and reviews.

## Presentation checks

`paper.tex` places references before `\appendix`. `\E` is defined once using square brackets; searched source contains no alternative unbracketed expectation macro use. The author line, PDF metadata source, bibliography entries, introduction and related-work text consistently use **Hajiaghayi**. No figure/includegraphics/TikZ source was found. The source includes the results table immediately before the model/main results. This is a source-level order check, not certification of the revised PDF's page count, table placement, overflow, hyperlinks, or arXiv compilation.

The AI-methodology replacement removes the stale denial of main formalization while retaining a clear description of material Codex/Astra assistance. This review cannot independently establish historical model identity or every past assistance activity; it checks consistency with the supplied authorship/history description and the new formal scope.

## Evidence and limits

I read the complete abstract/front matter, introduction, table, model, general results, related work, all proof overviews, both scope drafts and the canonical scope/AI text. I inspected the positive appendices' theorem/primitive interfaces and accounting/completion passages, and the lower appendices' model, quantitative/approximation statements, and final probability/expected-cost arguments. I did **not** independently reprove every line of all 4,496 manuscript section lines or every imported Lean theorem. Existing independent chore and lower-adapter reviews support the deeper chains; their reported builds are not re-certified here. The randomized review visible at the inspected snapshot still identified the old phase-run bridge gap, which is why its later hashed addendum remains a separate gate.

No browser/literature lookup was performed: prior benchmark statements are checked for internal consistency only, not newly verified against external papers. No PDF, old acceptance receipt, or ZIP checksum is treated as evidence for the new source. No expensive builds, axiom commands, visual PDF review, release assembly, archive extraction or arXiv submission was performed. Hashes below identify a source snapshot; they do not certify that future edits are covered.

## SHA-256 source snapshot

Paths are relative to `/Users/alireza/temp/ef/research`. The manuscript hashes cover all its section sources even where the review sampled interfaces rather than the entire proof. Hashes of supporting reviews record their inspected checkpoint, not an endorsement of outdated findings after later edits.

| Source | SHA-256 |
| --- | --- |
| `submission_focused/paper/paper.tex` | `5fea7cd8956f9d6d01e3b18722214057de1f90364ab784bff88b5202b9cec590` |
| `submission_focused/paper/sections/ai_methodology.tex` | `d43b15cd749f4d77060d09c7832b3e725cc5010e12d5fef16ccdfd2030eeb4ff` |
| `submission_focused/paper/sections/baseline_completion.tex` | `6b0ba931c2c3d8204666f40b576d4a0509eb9eab5ed7ada3bfce13684e025d52` |
| `submission_focused/paper/sections/baseline_subcore.tex` | `15baaa46e3c96f9e94e8d83500dbc0d66f35ac6ce36642b7d74dc453ec385c01` |
| `submission_focused/paper/sections/chore_proof.tex` | `4e53573239e1f577e007b6feca9d7f566bbd1805b16974cec740e63c00f40712` |
| `submission_focused/paper/sections/core_proof.tex` | `7f7b9233216c488d2de28e659639d0c6d1325a6d0fb1e613b819ffd4356208bf` |
| `submission_focused/paper/sections/formal_scope.tex` | `4e28ad65559c00e53331804377d4d044f711d46d208cb54c86f6dbcd08ea1050` |
| `submission_focused/paper/sections/general_results.tex` | `cf6772ce8e8b944300a46ca41f754177bd4c284499aad3d708564701aa58cbfc` |
| `submission_focused/paper/sections/introduction.tex` | `9819b6cef6459c045e32a7bbec61965e67815c06baedf28a7785d87cd1a403fa` |
| `submission_focused/paper/sections/lower_overview.tex` | `91738d525c21c3c04b79ccfe529bdc36bf47a818498a18c47890b13561fd3b7f` |
| `submission_focused/paper/sections/mixed_lower_proof.tex` | `7c1138114db4d71cb4ad56010a8f05834bf6adef393035225390496888ab7f43` |
| `submission_focused/paper/sections/mixed_overview.tex` | `3c354a9219e6b922d06b6ce59bf2ef34c00d95ba2a827bfb18a84668b639bde3` |
| `submission_focused/paper/sections/model.tex` | `534b15490f651f91bad820971e5bd3a4e144cb277336b79808668c0cfee75b11` |
| `submission_focused/paper/sections/nonnegative_lower_proof.tex` | `0e46119b7acce914a668234ebe3a322ff84fd983f874c2b4dd7c3c2498d68d8e` |
| `submission_focused/paper/sections/offset_subcore_proof.tex` | `8c9ddf586a21189ae2068843683e93dd33d20a598dc845598ef29a3e56492ea2` |
| `submission_focused/paper/sections/proof_overviews.tex` | `20179bf87f044f8fa5733afe43b58e51aacdf92725ec43b93937b44fd272c5de` |
| `submission_focused/paper/sections/related_work.tex` | `f005fb958c3decb84ab1b4d93bde619ce4f9eed285805070af270f7bbf8c34e2` |
| `submission_focused/paper/sections/results_table.tex` | `81584644dab5388e8284571744ca2ae8abb2ee9e5385ac40af0a8ca362b6adae` |
| `submission_focused/paper/sections/upper_overview.tex` | `d5eaf935e36e642be2a9fb00d102f9165905752d7fde50b653d414683e46c781` |
| `submission_focused/paper/sections/upper_proof.tex` | `66955a399e1eaa71abf7df7f92662b23ba37b57e67998ee59482b75a4634fec9` |
| `submission_focused/paper/references.bib` | `555f856da871a17b246aedea6b8d363379a46ba6316d9e5825d5eca3d454e2e4` |
| `formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/ChoresMain.lean` | `77308913ad573637030e33e473d8a6ffee115563bfb70999aefc2ba6274b1767` |
| `formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/UpperGlobalOraclePublic.lean` | `b35f14c1e0aa9ec72b55010bb6ea406f316885165ea76c378f87173866b8cb99` |
| `formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/UpperGlobalOracleExecutionUnit.lean` | `1e6c24617bbb1019981394115726294396932278fe62427a515a82d1d1aaa588` |
| `formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/UpperGlobalOracleNextMeasurable.lean` | `e660e7ef4f1800cab5e0889b9be6512dc7a4d324112a2fc25bae9f0a2b689d5b` |
| `formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/AdaptiveOracle.lean` | `98ae4573285668d74df0e013a505e2f08c33e0428d40b1d5194a800841013331` |
| `formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeRawMain.lean` | `f7502eef7163684e13f51bf221d1a5038147bdfeee8a4321ef39701b22845a84` |
| `formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/NonnegativeInputClass.lean` | `ead3ef0d53ec3ca5e8002e25a58ec2d444e94c13a2d5e800cc6b03660282ba49` |
| `formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedIntervalMain.lean` | `51750ebc1ee0f3e83d72aab6c57887901f3c1711026945de01be943daa314bfc` |
| `formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/MixedPhysicalMain.lean` | `b739574dc13087fb78ffee57d12ef017267c1fcbcd7e367306a0f735b777522b` |
| `formalization/all_main_results/verification/lean/EnvyFreeResearch/Full/RawIntervalPartition.lean` | `dd4d9bb3aac7d463dacb50ca00bc6e5c85c0719dc3c2c3b090e59f799c5b923a` |
| `formalization/all_main_results/verification/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `formalization/all_main_results/verification/lean/lakefile.lean` | `1dc697593bd118bbaa6df9e2a0065a191e20bc3010758f5c32259941ea5044d6` |
| `formalization/all_main_results/verification/lean/lake-manifest.json` | `959a848076f126dfde4f8ef5b1c8718a62e078d6a96e8b5e3369bab9ccc04965` |
| `formalization/all_main_results/formalization/release_staging/formal_scope.tex.draft` | `9bbb767af07618b809fcf0d09064a81ca6c3d7802cf3d9d99385364e47f39136` |
| `formalization/all_main_results/formalization/release_staging/ai_methodology.tex.draft` | `0991f71b9b0ff36a01c8ef74b0e6bc47351ab7ab2f6e06845c6e494a7bef530c` |
| `formalization/all_main_results/formalization/release_staging/main_results.json.draft` | `69e04a7a2ccfd5175bfeab083c84a4a0c9d8ff7fb77da9109f59b3cfcff65e12` |
| `formalization/all_main_results/formalization/release_staging/PLAN.md` | `8ddbf8c4825eac3e8efc1882e644b5834d0f9f8186b7a386c1ff17405c11c1ae` |
| `formalization/all_main_results/formalization/release_staging/verify_lean.py.draft` | `b1ec359f4d5574f6b5a63cff2109772613da8cbdcffd67adeaacee8c2167230e` |
| `formalization/all_main_results/formalization/reviews/chore_main_fresh_review.md` | `4d7fed995bd36488c3f6d711cd91e354712e8830c7795cc3a79cccf2535b1ccb` |
| `formalization/all_main_results/formalization/reviews/randomized_main_fresh_review.md` | `cb177992e35a918c0d9a7b045bc11a642b836e67018682bc8d2cbf070d55bfc1` |
| `formalization/all_main_results/formalization/reviews/lower_adapters_independent_review.md` | `23300769783502e3b023e94df80d1c81839cba4e7fad5626b259ff7de0e9fcf4` |
