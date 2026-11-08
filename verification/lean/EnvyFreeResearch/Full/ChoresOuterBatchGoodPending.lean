import EnvyFreeResearch.Full.ChoresOuterBatchGoodFrames

/-! Stored frontier values and pending scans remain exact after commit. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Scheduler Components ChoreComposition
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) (original : RootId → Snapshot.Output n)
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))
  (outputs : List (GroupResult data hall cycle))
  (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)
include good

theorem commit_batch_frontier_value (s : Fin outputs.length) (i p : Fin n) :
    ((commitBatch data hall cycle original outputs keep hk).frames s).frontierGap i p=
      ((commitBatch data hall cycle original outputs keep hk).frames s).gap i
        ((commitBatch data hall cycle original outputs keep hk).frontier s p) p := by
  by_cases hp : p ∈ data.pending.selected hall cycle
  · simp only [commitBatch,ComponentFrames.advance,advancedFrontier,ite_eq_left hp,Frame.gap]
  · simpa only [commitBatch,ComponentFrames.advance,advancedFrontier,ite_eq_right hp,Frame.gap] using
      good.frontier_value (batchSurvivor data hall cycle outputs s) i p

theorem commit_batch_pending_scan (p : Fin n)
    (proposed : Scheduler.Proposal (Fin outputs.length) (Fin n))
    (hp : (commitBatch data hall cycle original outputs keep hk).pending.proposals p=some proposed)
    (s : Fin outputs.length) :
    Frontier.scan (original ((commitBatch data hall cycle original outputs keep hk).source s)).equalizers
      p r H ((commitBatch data hall cycle original outputs keep hk).pending.partition.component p)=
        .outside (proposed.nextAgent s) := by
  change Option.map (fun q => q.restrict (batchSurvivor data hall cycle outputs))
    ((data.pending.merge (data.pending.selected hall cycle) keep
      (data.pending.selected_subset hall cycle) hk).proposals p)=some proposed at hp
  obtain ⟨q,hq,rfl⟩ := Option.map_eq_some_iff.mp hp
  exact advanced_pending_scan data original cost r H good hall cycle keep hk p q hq
    (batchSurvivor data hall cycle outputs s)

end EnvyFreeResearch.Full.Chores.Outer
