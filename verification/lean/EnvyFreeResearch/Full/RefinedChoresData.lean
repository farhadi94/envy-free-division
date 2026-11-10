import EnvyFreeResearch.Full.RefinedChoresRootFrontier
import EnvyFreeResearch.Full.ChoresOuterData

/-! Physical pool state for the root-local deferred-payment scheduler.
Every live root retains its original identity allocation. Paid permission
states and their component partitions are local to that root. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.Equalizers Chores.Snapshot Chores.Frontier Chores.Scheduler ChoreComposition
open RefinedChoresRootState RefinedChoresPartialGraph RefinedChoresCapacityRun RefinedChoresStateCapacity
open scoped Classical

structure Data (n : ℕ) (RootId : Type*) where
  size : ℕ
  source : Fin size → RootId
  packages : Fin size → Package (Fin n) RootId
  frames : Fin size → Frame (Fin n) RootId
  tracked : ∀ s, Tracked (frames s)
  protectedLabel : Fin n
  protected_fixed : ∀ s, (tracked s).state.partition.representative protectedLabel = protectedLabel
  frontier : Fin size → Fin n → Fin n
  cache : RootId → Fin n → List (Parent n)
  closed : List (Package (Fin n) RootId)

variable {n : ℕ} {RootId : Type*}

def Data.pending (data : Data n RootId) (s : Fin data.size) := (data.tracked s).state
def Data.visited (data : Data n RootId) (s : Fin data.size) := (data.tracked s).graph

def Data.allPackages (data : Data n RootId) : List (Package (Fin n) RootId) :=
  data.closed ++ List.ofFn data.packages

def Data.component (data : Data n RootId) (s : Fin data.size) (p : Fin n) : Finset (Fin n) :=
  componentSet (data.pending s) ((data.pending s).component p)

def Data.Normal (data : Data n RootId) : Prop := ∀ s, ¬ Nonempty (Cycle (data.pending s))

structure Data.Good [Fintype RootId] (data : Data n RootId)
    (original : RootId → Snapshot.Output n)
    (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (r : Fin n → ℝ) (H : ℝ) : Prop where
  package_valid : PoolValid data.allPackages
  all_ids : (data.allPackages.flatMap Package.ids).Perm Finset.univ.toList
  closed : ∀ package ∈ data.closed, package.live = none
  live : ∀ s, (data.packages s).live = some (data.frames s)
  source : ∀ s, (data.frames s).root = data.source s
  original_frame : ∀ s, Outer.OriginalFrame (data.frames s) (original (data.source s))
  cache : ∀ root p, Valid (measureProfile cost) (data.cache root p) ∧ Ordered (data.cache root p)
  cache_subset : ∀ root p, material (data.cache root p) ⊆ (original root).piece p
  realized : ∀ a ∈ data.allPackages.flatMap Package.allocations, ∀ i p,
    a.cost i p = (cost i).real (material (data.cache a.root p))
  live_cache : ∀ s p, data.cache (data.source s) p =
    ((original (data.source s)).equalizers (p,p)).parts.prefixParts
  frontier : ∀ s p, RefinedChoresPendingFrontier.Pending
    (Frontier.weight (original (data.source s)).equalizers p)
    (Frontier.rankOf (original (data.source s)).equalizers p) r H
    (Frontier.eligible (Frontier.weight (original (data.source s)).equalizers p)
      (Frontier.rankOf (original (data.source s)).equalizers p) r H)
    (data.component s p) ((data.frames s).allowed p) ((data.frames s).forbidden p) (data.frontier s p)
  frontier_value : ∀ s i p, (data.frames s).frontierGap i p =
    (data.frames s).gap i (data.frontier s p) p
  weight_bounded : ∀ s, (data.packages s).ids.length ≤ capacity (data.pending s)
  complement_small : ∀ root p i,
    (cost i).real ((original root).piece p \ material (data.cache root p)) ≤ (n : ℝ)*r i/H

structure Normalized (frame : Frame (Fin n) RootId) (tracked : Tracked frame)
    (protectedLabel : Fin n) where
  result : Tracked frame
  normal : ¬ Nonempty (Cycle result.state)
  cap : capacity tracked.state ≤ capacity result.state
  protected_fixed : result.state.partition.representative protectedLabel = protectedLabel
  coarsens : ∀ a b, tracked.state.partition.representative a = tracked.state.partition.representative b →
    result.state.partition.representative a = result.state.partition.representative b

def normalizeRoot (frame : Frame (Fin n) RootId) (tracked : Tracked frame) (p : Fin n)
    (hp : tracked.state.partition.representative p = p) : Normalized frame tracked p :=
  Classical.choice (show Nonempty (Normalized frame tracked p) from by
    obtain ⟨state,graph,hn,hcap,hp,hcoarse,hexact⟩ :=
      normalization_with_capacity tracked.state tracked.graph p hp
    exact ⟨⟨⟨state,graph,fun a b => (tracked.exact a b).trans (hexact a b).symm,
      tracked.owner_identity⟩,hn,hcap,hp,hcoarse⟩⟩)

def Data.normalize (data : Data n RootId) : Data n RootId :=
  { data with
    tracked := fun s => (normalizeRoot (data.frames s) (data.tracked s) data.protectedLabel
      (data.protected_fixed s)).result
    protected_fixed := fun s => (normalizeRoot (data.frames s) (data.tracked s) data.protectedLabel
      (data.protected_fixed s)).protected_fixed }

theorem normalized_normal (data : Data n RootId) : data.normalize.Normal :=
  fun s => (normalizeRoot (data.frames s) (data.tracked s) data.protectedLabel
    (data.protected_fixed s)).normal

theorem normalized_good [Fintype RootId] (data : Data n RootId)
    (original : RootId → Snapshot.Output n)
    (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H) :
    data.normalize.Good original cost r H := by
  refine { good with frontier := ?_, weight_bounded := ?_ }
  · intro s p
    apply RefinedChoresPendingFrontier.grow _ _ _ _ _ _ _ _ _ _ (good.frontier s p)
    intro a ha
    simp only [Data.component,mem_componentSet] at ha ⊢
    exact (normalizeRoot (data.frames s) (data.tracked s) data.protectedLabel
      (data.protected_fixed s)).coarsens a p ha
  · intro s
    exact (good.weight_bounded s).trans
      (normalizeRoot (data.frames s) (data.tracked s) data.protectedLabel
        (data.protected_fixed s)).cap

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.normalized_good
