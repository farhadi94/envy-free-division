import EnvyFreeResearch.Full.ChoresOuterBoundaryEqualizers
import EnvyFreeResearch.Full.ChoresComponentBoundaryPhysicalCore
import EnvyFreeResearch.Full.ChoresSnapshotLoop

/-! Coordinate provenance for an actual complete snapshot: physical Core,
all recorded original equalizers, and literal allocation/residue caches. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Equalizers Snapshot
open scoped Classical

variable {n : ℕ}

theorem allocation_cache_known (points : Set ℝ) (cache : List (Parent n))
    (hcache : CacheKnown points cache) (out : IntervalCore.Outcome n) (p : Fin n) :
    CacheKnown points (allocationCache cache out p) := by
  cases out with
  | zero z =>
    by_cases hp : p=z
    · simpa only [allocationCache,ite_eq_left hp] using hcache
    · simp only [allocationCache,ite_eq_right hp,CacheKnown,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | prefixes parent state => exact hcache.filter _

theorem residue_cache_known (points : Set ℝ) (cache : List (Parent n))
    (hcache : CacheKnown points cache) (out : IntervalCore.Outcome n) :
    CacheKnown points (residueCache cache out) := by
  cases out with
  | zero z => simp [residueCache,CacheKnown]
  | prefixes parent state => exact hcache.filter _

structure SnapshotKnown (points : Set ℝ) (out : Snapshot.Output n) : Prop where
  cache : CacheKnown points out.cache
  table : TableKnown points out.equalizers
  endpoints : ∀ x ∈ coreEndpoints out.outcome, x ∈ points

theorem SnapshotKnown.mono {old more : Set ℝ} {out : Snapshot.Output n}
    (h : SnapshotKnown old out) (hm : old ⊆ more) : SnapshotKnown more out :=
  ⟨h.cache.mono hm,h.table.mono hm,fun x hx => hm (h.endpoints x hx)⟩

theorem SnapshotKnown.parents {points : Set ℝ} {out : Snapshot.Output n}
    (h : SnapshotKnown points out) (p : Fin n) : CacheKnown points (out.parents p) :=
  allocation_cache_known points out.cache h.cache out.outcome p

theorem SnapshotKnown.residue {points : Set ℝ} {out : Snapshot.Output n}
    (h : SnapshotKnown points out) : CacheKnown points out.residue :=
  residue_cache_known points out.cache h.cache out.outcome

theorem snapshot_known (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (points : Set ℝ) (hcache : CacheKnown points cache) (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (c : Fin n) (prior : History (Query (Fin n)) ℝ)
    (out : Snapshot.Output n) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (Snapshot.program c cache) prior out trace) :
    SnapshotKnown (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨core,first,tail,hcore,htail,htrace⟩ := Executes.split_bind _ _ h
  rcases core with ⟨result,middle⟩
  obtain ⟨table,second,empty,htable,hreturn,htailtrace⟩ := Executes.split_bind _ _ htail
  cases hreturn
  simp only [List.append_nil] at htailtrace
  subst tail
  subst trace
  obtain ⟨hmiddle,hscope,hpoints⟩ := cached_domain_core_known cost oracle hpolicy U cache hc
    points hcache hzero hone c prior result middle first hcore
  obtain ⟨htableKnown,htableScope⟩ := equalizer_table_known oracle (Known points first) (Or.inl hzero)
    (allocationCache middle result) (allocation_cache_known _ _ hmiddle _) (prior++first) table second htable
  refine ⟨⟨hmiddle.mono (known_mono points first second),?_,
    fun x hx => known_mono points first second (hpoints x hx)⟩,?_⟩
  · simpa only [known_append] using htableKnown
  · exact (scoped_append points first second).mpr ⟨hscope,htableScope⟩

end EnvyFreeResearch.Full.Chores.Boundary
