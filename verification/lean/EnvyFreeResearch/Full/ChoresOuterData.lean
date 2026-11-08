import EnvyFreeResearch.Full.ChoresOuterOriginal
import EnvyFreeResearch.Full.ChoresOuterFiltering
import EnvyFreeResearch.Full.ChoresRevealPendingGeometry
import EnvyFreeResearch.Full.ChoresOuterSchedule

/-! Concrete committed state of the package scheduler. Computation reads
only original snapshot tables, finite graph data and physical caches.
Measure semantics are carried separately by Good and are not protocol
inputs. Every inactive package remains explicitly in the closed pool. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open scoped Classical

variable {n : ℕ} {RootId : Type*}

structure Data (n : ℕ) (RootId : Type*) where
  size : ℕ
  source : Fin size → RootId
  pending : PendingState (Fin size) (Fin n)
  visited : Visited pending
  packages : Fin size → ChoreComposition.Package (Fin n) RootId
  frames : Fin size → ChoreComposition.Frame (Fin n) RootId
  frontier : Fin size → Fin n → Fin n
  cache : RootId → Fin n → List (Parent n)
  closed : List (ChoreComposition.Package (Fin n) RootId)

def Data.allPackages (data : Data n RootId) : List (ChoreComposition.Package (Fin n) RootId) :=
  data.closed++List.ofFn data.packages

def Data.filter (data : Data n RootId) (kept : List (Fin data.size)) : Data n RootId where
  size := kept.length
  source := data.source ∘ kept.get
  pending := data.pending.restrict kept.get
  visited := data.visited.restrict kept.get
  packages := data.packages ∘ kept.get
  frames := data.frames ∘ kept.get
  frontier := data.frontier ∘ kept.get
  cache := data.cache
  closed := data.closed++(rejected (List.finRange data.size) kept).map (fun s => (data.packages s).close)

def Data.reveal (data : Data n RootId) (p : Fin n) (hp : p ∈ data.pending.partition.labels)
    (proposed : Scheduler.Proposal (Fin data.size) (Fin n))
    (hvalid : proposed.Valid data.pending.partition p) : Data n RootId where
  size := data.size
  source := data.source
  pending := data.pending.reveal p hp proposed hvalid
  visited := data.visited.reveal p hp proposed hvalid
  packages := data.packages
  frames := data.frames
  frontier := data.frontier
  cache := data.cache
  closed := data.closed

/-- The component containing an arbitrary original label, including a
label that is no longer the representative after a merger. -/
def Data.component (data : Data n RootId) (p : Fin n) : Finset (Fin n) :=
  data.pending.partition.component (data.pending.partition.representative p)

structure Data.Good [Fintype RootId] (data : Data n RootId)
    (original : RootId → Snapshot.Output n)
    (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (r : Fin n → ℝ) (H : ℝ) : Prop where
  package_valid : ChoreComposition.PoolValid data.allPackages
  all_ids : (data.allPackages.flatMap ChoreComposition.Package.ids).Perm Finset.univ.toList
  closed : ∀ package ∈ data.closed, package.live=none
  live : ∀ s, (data.packages s).live=some (data.frames s)
  source : ∀ s, (data.frames s).root=data.source s
  original_frame : ∀ s, OriginalFrame (data.frames s) (original (data.source s))
  cache : ∀ root p, Valid (measureProfile cost) (data.cache root p) ∧ Ordered (data.cache root p)
  cache_subset : ∀ root p, material (data.cache root p) ⊆ (original root).piece p
  realized : ∀ a ∈ data.allPackages.flatMap ChoreComposition.Package.allocations, ∀ i p,
    a.cost i p=(cost i).real (material (data.cache a.root p))
  live_cache : ∀ s p, data.cache (data.source s) p=
    ((original (data.source s)).equalizers (p,(data.frames s).owner p)).parts.prefixParts
  allowed : ∀ s p i, i ∈ (data.frames s).allowed p ↔ Components.Edge (data.visited.graph s) p i
  frontier : ∀ s p, Frontier.Invariant
    (Frontier.weight (original (data.source s)).equalizers p)
    (Frontier.rankOf (original (data.source s)).equalizers p) r H
    (Frontier.eligible (Frontier.weight (original (data.source s)).equalizers p)
      (Frontier.rankOf (original (data.source s)).equalizers p) r H)
    (data.component p) ((data.frames s).allowed p) ((data.frames s).forbidden p) (data.frontier s p)
  frontier_value : ∀ s i p, (data.frames s).frontierGap i p=(data.frames s).gap i (data.frontier s p) p
  pending_scan : ∀ p proposed, data.pending.proposals p=some proposed → ∀ s,
    Frontier.scan (original (data.source s)).equalizers p r H (data.pending.partition.component p)=
      Frontier.Outcome.outside (proposed.nextAgent s)
  complement_small : ∀ root p i,
    (cost i).real ((original root).piece p \ material (data.cache root p)) ≤ (n : ℝ)*r i/H

theorem filter_package_list (data : Data n RootId) (kept : List (Fin data.size)) :
    (data.filter kept).allPackages=filteredPool (List.finRange data.size) kept data.packages data.closed := by
  unfold Data.allPackages Data.filter filteredPool
  congr 1
  change List.ofFn (fun i : Fin kept.length => data.packages (kept.get i))=kept.map data.packages
  exact List.ofFn_getElem_eq_map kept data.packages

theorem filter_allocations_perm (data : Data n RootId) (kept : List (Fin data.size)) (hk : kept.Nodup) :
    ((data.filter kept).allPackages.flatMap ChoreComposition.Package.allocations).Perm
      (data.allPackages.flatMap ChoreComposition.Package.allocations) := by
  rw [filter_package_list]
  have h := filtered_allocations_perm (List.finRange data.size) kept (List.nodup_finRange _) hk
    (fun i _ => List.mem_finRange i) data.packages data.closed
  simpa only [Data.allPackages,List.ofFn_eq_map] using h

theorem filter_ids_perm (data : Data n RootId) (kept : List (Fin data.size)) (hk : kept.Nodup) :
    ((data.filter kept).allPackages.flatMap ChoreComposition.Package.ids).Perm
      (data.allPackages.flatMap ChoreComposition.Package.ids) := by
  have h := (filter_allocations_perm data kept hk).map ChoreComposition.Allocation.root
  simpa only [PackageGeometry.pool_allocation_roots] using h

end EnvyFreeResearch.Full.Chores.Outer
