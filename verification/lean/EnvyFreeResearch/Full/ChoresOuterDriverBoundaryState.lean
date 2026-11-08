import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryGroup
import EnvyFreeResearch.Full.ChoresOuterInitial

/-! The scheduler's boundary invariant is carried separately from physical
cache validity. Filtering and revelation only reorganize recorded data. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Scheduler Components ChoreComposition Boundary
open scoped Classical
variable {n : ℕ} {RootId : Type*}

structure DataKnown (points : Set ℝ) (original : RootId → Snapshot.Output n)
    (data : Data n RootId) : Prop where
  snapshots : ∀ root, SnapshotKnown points (original root)
  cache : ∀ root p, CacheKnown points (data.cache root p)

theorem DataKnown.mono {points more : Set ℝ} {original : RootId → Snapshot.Output n}
    {data : Data n RootId} (h : DataKnown points original data) (hm : points ⊆ more) :
    DataKnown more original data :=
  ⟨fun root => (h.snapshots root).mono hm,fun root p => (h.cache root p).mono hm⟩

theorem DataKnown.filter {points : Set ℝ} {original : RootId → Snapshot.Output n}
    {data : Data n RootId} (h : DataKnown points original data) (kept : List (Fin data.size)) :
    DataKnown points original (data.filter kept) := ⟨h.snapshots,h.cache⟩

theorem DataKnown.reveal {points : Set ℝ} {original : RootId → Snapshot.Output n}
    {data : Data n RootId} (h : DataKnown points original data)
    (p : Fin n) (hp : p ∈ data.pending.partition.labels)
    (proposed : Scheduler.Proposal (Fin data.size) (Fin n))
    (hvalid : proposed.Valid data.pending.partition p) :
    DataKnown points original (data.reveal p hp proposed hvalid) := ⟨h.snapshots,h.cache⟩

theorem initial_data_known {J : ℕ} (points : Set ℝ) (original : Fin J → Snapshot.Output n)
    (h : ∀ root, SnapshotKnown points (original root)) :
    DataKnown points original (initialData original) :=
  ⟨h,fun root p => (h root).parents p⟩

end EnvyFreeResearch.Full.Chores.Outer
