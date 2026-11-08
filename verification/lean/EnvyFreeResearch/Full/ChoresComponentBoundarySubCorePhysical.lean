import EnvyFreeResearch.Full.ChoresComponentBoundarySubCoreEntry
import EnvyFreeResearch.Full.ChoresComponentBoundaryMasked

/-! Physical affine/clipped SubCore provenance. The concrete source theorem
supplies stored references; the concrete tagged interpreter transfers every
source boundary to an inherited endpoint or an original-oracle Cut reply. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram Persistent Suffix
open SubCorePhysical SubCoreLeaves SubCoreEntry OrderedUnion
open scoped Classical

variable {n : ℕ} {Agent Root : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Root] [Nonempty Root]

theorem clipped_physical_known (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (domains : Root → Fin n → Set ℝ) (cache : Masked.Cache Root n)
    (hc : Masked.CacheCorrect (measureProfile cost) domains cache)
    (agent : Agent → Fin n) (offset : Root → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
    (hpositive : 0 < Fintype.card Agent) (hmany : Fintype.card Agent < Fintype.card Root)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (points : Set ℝ) (hcache : MaskedCacheKnown points cache) (hzero : 0 ∈ points) (hone : 1 ∈ points)
    (prior : History (Query (Fin n)) ℝ) (store : SubCorePhysical.Store Root (ClippedRecord n))
    (out : SubCore.Allocation Agent Root (OrderedRecord n)) (fresh : Masked.Cache Root n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (clippedPhysicalProgram agent offset cache hmany.le) prior ((store,some out),fresh) trace) :
    SuffixStoreKnown ClippedRecord.record (Known points trace) store ∧
      MaskedCacheKnown (Known points trace) fresh ∧ Scoped points trace ∧
      (∀ p, 1-(out.point p).record.point ∈ Known points trace) := by
  let initial : Masked.SemanticState (measureProfile cost) domains := ⟨cache,prior,hc⟩
  let policy := Masked.virtualPolicy cost oracle hpolicy domains initial
  let P := fun p => Masked.rowProfile cost (domains p)
  letI := clippedValidity P offset (cachedTotals cache)
  have hlegal : Masked.IsLegalPolicy P policy :=
    Masked.virtual_policy_legal cost oracle hpolicy domains initial
  obtain ⟨sourceStore, sourceOut, virtualTrace, hsource, _, _, hrefs, _, _, _, _⟩ :=
    clipped_program_correct P (masked_profile_monotone cost domains) agent offset (cachedTotals cache)
      hoffset (cached_totals_profile cost domains cache hc) hpositive hmany policy hlegal []
  obtain ⟨hsourceStore, hsourceScope⟩ := clipped_source_known policy points hzero hone agent offset
    (cachedTotals cache) hmany.le [] (sourceStore,some sourceOut) virtualTrace hsource
  obtain ⟨physicalTrace, hphysical, hfinalCache, hphysicalScope, hsubset⟩ :=
    masked_translate_known cost oracle hpolicy domains initial hsource points
      (by simpa only [Masked.historyState, List.foldl_nil, initial] using hcache) hsourceScope
  have hphysical' : Executes oracle (clippedPhysicalProgram agent offset cache hmany.le) prior
      ((sourceStore,some sourceOut), (Masked.historyState cost oracle hpolicy domains initial virtualTrace).cache)
      physicalTrace := by
    simpa only [clippedPhysicalProgram, Masked.historyState, List.foldl_nil, List.nil_append, initial] using hphysical
  obtain ⟨hpair, htrace⟩ := hphysical'.deterministic h
  have hstore : sourceStore = store := congrArg (fun x => x.1.1) hpair
  have hout : sourceOut = out := Option.some.inj (congrArg (fun x => x.1.2) hpair)
  have hfresh : (Masked.historyState cost oracle hpolicy domains initial virtualTrace).cache = fresh :=
    congrArg Prod.snd hpair
  subst store
  subst out
  subst fresh
  subst trace
  have hstored := hsourceStore.mono hsubset
  refine ⟨hstored, ?_, hphysicalScope, ?_⟩
  · simpa only [List.nil_append] using hfinalCache
  · exact records_suffix_known ClippedRecord.record (Known points physicalTrace) sourceStore hstored sourceOut.point hrefs

theorem affine_physical_known (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (domains : Root → Fin n → Set ℝ) (cache : Masked.Cache Root n)
    (hc : Masked.CacheCorrect (measureProfile cost) domains cache)
    (agent : Agent → Fin n) (offset : Root → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
    (hpositive : 0 < Fintype.card Agent) (hmany : Fintype.card Agent < Fintype.card Root)
    (hwhole : ∀ p i, 0 ≤ cachedTotals cache p (agent i)-offset p (agent i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (points : Set ℝ) (hcache : MaskedCacheKnown points cache) (hzero : 0 ∈ points) (hone : 1 ∈ points)
    (prior : History (Query (Fin n)) ℝ) (store : SubCorePhysical.Store Root (Record n))
    (out : SubCore.Allocation Agent Root (OrderedRecord n)) (fresh : Masked.Cache Root n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (affinePhysicalProgram agent offset cache hmany.le) prior ((store,some out),fresh) trace) :
    SuffixStoreKnown id (Known points trace) store ∧
      MaskedCacheKnown (Known points trace) fresh ∧ Scoped points trace ∧
      (∀ p, 1-(out.point p).record.point ∈ Known points trace) := by
  let initial : Masked.SemanticState (measureProfile cost) domains := ⟨cache,prior,hc⟩
  let policy := Masked.virtualPolicy cost oracle hpolicy domains initial
  let P := fun p => Masked.rowProfile cost (domains p)
  letI := affineValidity P offset (cachedTotals cache)
  have hlegal : Masked.IsLegalPolicy P policy :=
    Masked.virtual_policy_legal cost oracle hpolicy domains initial
  obtain ⟨sourceStore, sourceOut, virtualTrace, hsource, _, _, hrefs, _, _, _, _⟩ :=
    affine_program_correct P (masked_profile_monotone cost domains) agent offset (cachedTotals cache)
      hoffset (cached_totals_profile cost domains cache hc) hwhole hpositive hmany policy hlegal []
  obtain ⟨hsourceStore, hsourceScope⟩ := affine_source_known policy points hzero hone agent offset
    (cachedTotals cache) hmany.le [] (sourceStore,some sourceOut) virtualTrace hsource
  obtain ⟨physicalTrace, hphysical, hfinalCache, hphysicalScope, hsubset⟩ :=
    masked_translate_known cost oracle hpolicy domains initial hsource points
      (by simpa only [Masked.historyState, List.foldl_nil, initial] using hcache) hsourceScope
  have hphysical' : Executes oracle (affinePhysicalProgram agent offset cache hmany.le) prior
      ((sourceStore,some sourceOut), (Masked.historyState cost oracle hpolicy domains initial virtualTrace).cache)
      physicalTrace := by
    simpa only [affinePhysicalProgram, Masked.historyState, List.foldl_nil, List.nil_append, initial] using hphysical
  obtain ⟨hpair, htrace⟩ := hphysical'.deterministic h
  have hstore : sourceStore = store := congrArg (fun x => x.1.1) hpair
  have hout : sourceOut = out := Option.some.inj (congrArg (fun x => x.1.2) hpair)
  have hfresh : (Masked.historyState cost oracle hpolicy domains initial virtualTrace).cache = fresh :=
    congrArg Prod.snd hpair
  subst store
  subst out
  subst fresh
  subst trace
  have hstored := hsourceStore.mono hsubset
  refine ⟨hstored, ?_, hphysicalScope, ?_⟩
  · simpa only [List.nil_append] using hfinalCache
  · exact records_suffix_known id (Known points physicalTrace) sourceStore hstored sourceOut.point hrefs

end EnvyFreeResearch.Full.Chores.Boundary
