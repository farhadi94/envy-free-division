import EnvyFreeResearch.Full.RefinedChoresData
import EnvyFreeResearch.Full.ChoresOuterInitial

/-! The new physical pool starts from the actual recorded snapshots. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.Equalizers Chores.Snapshot Chores.Frontier Chores.Scheduler ChoreComposition
open RefinedChoresRootState RefinedChoresPartialGraph RefinedChoresCapacityRun RefinedChoresStateCapacity
open scoped Classical
variable {n J : ℕ}

def initialData (original : Fin J → Snapshot.Output n) (protectedLabel : Fin n) : Data n (Fin J) where
  size := J
  source := id
  packages s := Package.seed (PackageGeometry.initialFrame s (original s).parents (original s).equalizers)
  frames s := PackageGeometry.initialFrame s (original s).parents (original s).equalizers
  tracked s := RefinedChoresRootState.initial _ rfl (fun _ => rfl)
  protectedLabel := protectedLabel
  protected_fixed _ := rfl
  frontier _ p := p
  cache s := (original s).parents
  closed := []

theorem initial_normal (original : Fin J → Snapshot.Output n) (protectedLabel : Fin n) :
    (initialData original protectedLabel).Normal := by
  intro s ⟨cycle⟩
  have hsub := selected_pending ((initialData original protectedLabel).pending s) cycle
  have htwo := selected_two ((initialData original protectedLabel).pending s) cycle
  have hle := Finset.card_le_card hsub
  change (selected _ cycle).card ≤ (PendingState.initial : State (Fin n)).pending.card at hle
  rw [PendingState.initial_pending,Finset.card_empty] at hle
  omega

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (original : Fin J → Snapshot.Output n) (protectedLabel c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (r : Fin n → ℝ) (H : ℝ) (hr : ∀ i, 0 ≤ r i) (hH : 0 < H)
include hsound hr hH

theorem initial_good : (initialData original protectedLabel).Good original cost r H := by
  have old := Outer.initial_good cost original c hsound r H hr hH
  refine {
    package_valid := old.package_valid
    all_ids := old.all_ids
    closed := old.closed
    live := old.live
    source := old.source
    original_frame := old.original_frame
    cache := old.cache
    cache_subset := old.cache_subset
    realized := old.realized
    live_cache := ?_
    frontier := ?_
    frontier_value := old.frontier_value
    weight_bounded := ?_
    complement_small := old.complement_small }
  · intro s p
    exact old.live_cache s p
  · intro s p
    have hinv := Frontier.initial_invariant (weight (original s).equalizers p)
      (rankOf (original s).equalizers p) r H p (rank_owner _ _) (rank_le _ _) (hr p) hH
    have hc : (initialData original protectedLabel).component s p = {p} := by
      apply Finset.ext
      intro i
      simp only [Data.component,mem_componentSet,Finset.mem_singleton]
      rfl
    change RefinedChoresPendingFrontier.Pending _ _ _ _ _
      ((initialData original protectedLabel).component s p) {p} ∅ p
    rw [hc]
    exact RefinedChoresPendingFrontier.of_invariant _ _ _ _ _ _ _ _ _ hinv
      (Finset.mem_singleton_self _)
  · intro s
    change (Package.seed (PackageGeometry.initialFrame s (original s).parents
      (original s).equalizers)).ids.length ≤ capacity (PendingState.initial : State (Fin n))
    rw [initial_capacity]
    rfl

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.initial_good
