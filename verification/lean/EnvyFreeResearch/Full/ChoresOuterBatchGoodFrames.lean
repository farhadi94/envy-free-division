import EnvyFreeResearch.Full.ChoresOuterBatchCommit

/-! Frame and frontier invariants for the actual simultaneous commit. -/
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

theorem commit_batch_frame_source (s : Fin outputs.length) :
    ((commitBatch data hall cycle original outputs keep hk).frames s).root=
      (commitBatch data hall cycle original outputs keep hk).source s :=
  good.source _

theorem commit_batch_original (s : Fin outputs.length) :
    OriginalFrame ((commitBatch data hall cycle original outputs keep hk).frames s)
      (original ((commitBatch data hall cycle original outputs keep hk).source s)) :=
  advance_original data.pending hall cycle data.visited data.frames (original ∘ data.source)
    good.original_frame _

theorem commit_batch_allowed (s : Fin outputs.length) (p i : Fin n) :
    i ∈ ((commitBatch data hall cycle original outputs keep hk).frames s).allowed p ↔
      Edge ((commitBatch data hall cycle original outputs keep hk).visited.graph s) p i :=
  ComponentFrames.advanced_allowed data.pending hall cycle data.visited data.frames
    (batchSurvivor data hall cycle outputs s) (good.allowed _) p i

theorem commit_batch_frontier (hr : ∀ i, 0 ≤ r i) (hH : 0 < H)
    (s : Fin outputs.length) (p : Fin n) :
    Frontier.Invariant
      (Frontier.weight (original ((commitBatch data hall cycle original outputs keep hk).source s)).equalizers p)
      (Frontier.rankOf (original ((commitBatch data hall cycle original outputs keep hk).source s)).equalizers p) r H
      (Frontier.eligible
        (Frontier.weight (original ((commitBatch data hall cycle original outputs keep hk).source s)).equalizers p)
        (Frontier.rankOf (original ((commitBatch data hall cycle original outputs keep hk).source s)).equalizers p) r H)
      ((commitBatch data hall cycle original outputs keep hk).component p)
      (((commitBatch data hall cycle original outputs keep hk).frames s).allowed p)
      (((commitBatch data hall cycle original outputs keep hk).frames s).forbidden p)
      ((commitBatch data hall cycle original outputs keep hk).frontier s p) :=
  advanced_frontier data original cost r H good hall cycle keep hk hr hH
    (batchSurvivor data hall cycle outputs s) p

end EnvyFreeResearch.Full.Chores.Outer
