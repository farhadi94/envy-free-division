import EnvyFreeResearch.Full.ChoresOuterBatchGoodRealization
import EnvyFreeResearch.Full.ChoresOuterBatchGoodLive
import EnvyFreeResearch.Full.ChoresOuterBatchGoodPending
import EnvyFreeResearch.Full.ChoresOuterBatchCacheBounds

/-! All physical and scheduler invariants of the actual full batch commit. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Scheduler Components ChoreComposition
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Data n RootId) (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (outputs : List (GroupResult data hall cycle))
  (hout : ∀ out ∈ outputs, out.Correct data hall cycle cost (fun root => xs.get (index root)))
  (hgroups : outputs.map GroupResult.group=cohorts data hall cycle)
  (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)
include hsound hsep hr hH hscale good hout hgroups

theorem commit_batch_good :
    (commitBatch data hall cycle (fun root => xs.get (index root)) outputs keep hk).Good
      (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H := by
  let original := fun root => xs.get (index root)
  let r := fun i => (cost i).real R
  constructor
  · exact commit_batch_package_valid data hall cycle cost xs index R H good outputs hout keep hk
  · exact commit_batch_all_ids data hall cycle cost xs index c hsound R H hsep hr hH hscale
      good outputs hout keep hk hgroups
  · exact commit_batch_closed data hall cycle original outputs keep hk good.closed
  · exact commit_batch_live data hall cycle original outputs keep hk
  · exact commit_batch_frame_source data original cost r H good hall cycle outputs keep hk
  · exact commit_batch_original data original cost r H good hall cycle outputs keep hk
  · exact batch_cache_actual_valid data hall cycle cost xs index c hsound outputs hout good.cache
  · exact batch_cache_subset data hall cycle cost xs index c hsound outputs hout good.cache_subset
  · exact commit_batch_realized data hall cycle cost xs index c hsound H R hsep hr hH hscale
      good outputs hout hgroups keep hk
  · exact commit_batch_live_cache data hall cycle original outputs
      (actual_slots_distinct data hall cycle outputs hgroups)
      (source_injective data original cost r H good) keep hk
  · exact commit_batch_allowed data original cost r H good hall cycle outputs keep hk
  · exact commit_batch_frontier data original cost r H good hall cycle outputs keep hk
      (fun i => (hr i).le) (by linarith)
  · exact commit_batch_frontier_value data original cost r H good hall cycle outputs keep hk
  · exact commit_batch_pending_scan data original cost r H good hall cycle outputs keep hk
  · exact batch_cache_complement data hall cycle cost xs index c hsound R H hsep hr hH hscale
      good keep hk outputs hout

end EnvyFreeResearch.Full.Chores.Outer
