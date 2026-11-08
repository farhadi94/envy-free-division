import EnvyFreeResearch.Full.ChoresOuterBatchCache

/-! Commit all cohort results at once, merging once and closing all leftovers. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Scheduler Components ChoreComposition
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))
  (original : RootId → Snapshot.Output n) (outputs : List (GroupResult data hall cycle))
  (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)

def batchSurvivor (s : Fin outputs.length) : Fin data.size :=
  (outputs.get s).survivor data hall cycle

def commitBatch : Data n RootId where
  size := outputs.length
  source := data.source ∘ batchSurvivor data hall cycle outputs
  pending := (data.pending.merge (data.pending.selected hall cycle) keep
    (data.pending.selected_subset hall cycle) hk).restrict (batchSurvivor data hall cycle outputs)
  visited := (data.pending.commitGraphs hall cycle data.visited keep hk).restrict
    (batchSurvivor data hall cycle outputs)
  packages s := (outputs.get s).package data hall cycle original
  frames s := ComponentFrames.advance data.pending hall cycle data.visited data.frames
    (batchSurvivor data hall cycle outputs s)
  frontier s := advancedFrontier data hall cycle (batchSurvivor data hall cycle outputs s)
  cache := batchCache data hall cycle original outputs
  closed := data.closed ++ (Scheduler.leftovers (List.finRange data.size)
    (Fintype.card (ComponentBatch.Task data.pending hall cycle)+1)).map (fun s => (data.packages s).close)

theorem commit_batch_partition :
    (commitBatch data hall cycle original outputs keep hk).pending.partition=
      data.pending.partition.merge (data.pending.selected hall cycle) keep
        (data.pending.selected_subset hall cycle) hk := rfl

theorem commit_batch_source (s : Fin outputs.length) :
    (commitBatch data hall cycle original outputs keep hk).source s=
      data.source ((outputs.get s).survivor data hall cycle) := rfl

theorem commit_batch_live (s : Fin outputs.length) :
    ((commitBatch data hall cycle original outputs keep hk).packages s).live=
      some ((commitBatch data hall cycle original outputs keep hk).frames s) :=
  (outputs.get s).live_frame data hall cycle original

theorem commit_batch_closed
    (hold : ∀ package ∈ data.closed, package.live=none) :
    ∀ package ∈ (commitBatch data hall cycle original outputs keep hk).closed,
      package.live=none := by
  intro package hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hold package hp
  · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
    exact package_close_live _

theorem commit_batch_size
    (hgroups : outputs.map GroupResult.group=cohorts data hall cycle) :
    (commitBatch data hall cycle original outputs keep hk).size=
      data.size/(Fintype.card (ComponentBatch.Task data.pending hall cycle)+1) := by
  change outputs.length=_
  have h := congrArg List.length hgroups
  simpa only [List.length_map,cohorts_length] using h

end EnvyFreeResearch.Full.Chores.Outer
