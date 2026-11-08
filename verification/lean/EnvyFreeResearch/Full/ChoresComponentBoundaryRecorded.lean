import EnvyFreeResearch.Full.ChoresComponentBoundaryRecording

/-! Public parametric provenance contracts for the actual complete affine
and clipped compensation primitives. These inspect successful original-query
executions of the same programs used by the outer scheduler. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram Persistent Suffix
open SubCorePhysical SubCoreEntry OrderedUnion ComponentRecording
open scoped Classical

variable {n : ℕ} {Task Root : Type*} [Fintype Task] [DecidableEq Task]
    [Fintype Root] [Nonempty Root]

theorem clipped_recorded_known (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (domains : Root → Fin n → Set ℝ) (cache : Masked.Cache Root n)
    (hc : Masked.CacheCorrect (measureProfile cost) domains cache)
    (agent : Task → Fin n) (offset : Root → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
    (hpositive : 0 < Fintype.card Task) (hmany : Fintype.card Task < Fintype.card Root)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (points : Set ℝ) (hcache : MaskedCacheKnown points cache) (hzero : 0 ∈ points) (hone : 1 ∈ points)
    (prior : History (Query (Fin n)) ℝ) (out : Recorded (ClippedRecord n) Task Root n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ComponentRecording.clippedProgram agent offset cache hmany.le) prior (some out) trace) :
    RecordedKnown ClippedRecord.record (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨source, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  rcases source with ⟨⟨store, maybe⟩, next⟩
  cases maybe with
  | none => cases hs
  | some allocation =>
    obtain ⟨recorded, tail, empty, hfinish, hreturn, ht₂⟩ := Executes.split_bind _ _ hs
    cases hreturn
    simp only [List.append_nil] at ht₂
    subst second
    subst trace
    obtain ⟨hstore, hnext, hscope, hpoints⟩ := clipped_physical_known cost domains cache hc agent offset
      hoffset hpositive hmany oracle hpolicy points hcache hzero hone prior store allocation next first hf
    obtain ⟨hout, htail⟩ := retained_finish_known oracle ClippedRecord.record (Known points first) agent
      store hstore allocation hpoints next hnext (prior++first) out tail hfinish
    exact ⟨hout.mono (known_mono points first tail),
      (scoped_append points first tail).mpr ⟨hscope, htail⟩⟩

theorem affine_recorded_known (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (domains : Root → Fin n → Set ℝ) (cache : Masked.Cache Root n)
    (hc : Masked.CacheCorrect (measureProfile cost) domains cache)
    (agent : Task → Fin n) (offset : Root → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
    (hpositive : 0 < Fintype.card Task) (hmany : Fintype.card Task < Fintype.card Root)
    (hwhole : ∀ p i, 0 ≤ cachedTotals cache p (agent i)-offset p (agent i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (points : Set ℝ) (hcache : MaskedCacheKnown points cache) (hzero : 0 ∈ points) (hone : 1 ∈ points)
    (prior : History (Query (Fin n)) ℝ) (out : Recorded (Record n) Task Root n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (ComponentRecording.affineProgram agent offset cache hmany.le) prior (some out) trace) :
    RecordedKnown id (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨source, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  rcases source with ⟨⟨store, maybe⟩, next⟩
  cases maybe with
  | none => cases hs
  | some allocation =>
    obtain ⟨recorded, tail, empty, hfinish, hreturn, ht₂⟩ := Executes.split_bind _ _ hs
    cases hreturn
    simp only [List.append_nil] at ht₂
    subst second
    subst trace
    obtain ⟨hstore, hnext, hscope, hpoints⟩ := affine_physical_known cost domains cache hc agent offset
      hoffset hpositive hmany hwhole oracle hpolicy points hcache hzero hone prior store allocation next first hf
    obtain ⟨hout, htail⟩ := retained_finish_known oracle id (Known points first) agent
      store hstore allocation hpoints next hnext (prior++first) out tail hfinish
    exact ⟨hout.mono (known_mono points first tail),
      (scoped_append points first tail).mpr ⟨hscope, htail⟩⟩

end EnvyFreeResearch.Full.Chores.Boundary
