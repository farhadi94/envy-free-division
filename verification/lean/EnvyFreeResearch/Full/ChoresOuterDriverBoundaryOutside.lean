import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryState
import EnvyFreeResearch.Full.ChoresOuterOutside

/-! A continuing revelation leaves all physical caches unchanged, whether
or not the guard's success has already been established semantically. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set IntervalOracle InitialPartition OrderedUnion Boundary Scheduler
open scoped Classical
variable {n : ℕ} {RootId : Type*}

theorem outside_commit_known (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (points : Set ℝ) (hold : DataKnown points original data)
    (p : Fin n) (hp : p ∈ data.pending.partition.labels) (r : Fin n → ℝ) (H : ℝ)
    (roots : List (Fin data.size)) (target : Fin n) (updated : Data n RootId)
    (h : outsideCommit data original p hp r H roots target=some updated) :
    DataKnown points original updated := by
  unfold outsideCommit at h
  dsimp only at h
  split at h
  · cases h
    exact (hold.filter roots).reveal p hp _ _
  · cases h
end EnvyFreeResearch.Full.Chores.Outer
