import EnvyFreeResearch.Full.ChoresOuterBatchCommit
import EnvyFreeResearch.Full.ChoresOuterNextCache

/-! Truthful physical caches of actual cohort results. -/
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
include hsound

theorem group_cache_valid (out : GroupResult data hall cycle)
    (hout : out.Correct data hall cycle cost (fun root => xs.get (index root)))
    (s : Fin out.group.roots.length) (p : Fin n) :
    Valid (measureProfile cost) (out.nextCache data hall cycle (fun root => xs.get (index root)) s p) ∧
      Ordered (out.nextCache data hall cycle (fun root => xs.get (index root)) s p) := by
  let state := out.group.state data hall cycle
  let original := fun root => xs.get (index root)
  apply ComponentBatch.next_cache_valid state.pending (out.group.all_pending data hall cycle)
    (out.group.recordedCycle data hall cycle) state.visited state.frames
    (originalGaps state original) out.result (equalizerCache state original) (offeredFrontier state original)
    cost (fun t q => (original (state.source t)).piece q) (offeredBlocks state original)
  · intro t q
    obtain ⟨U,hs⟩ := hsound (state.source t)
    exact valid_material_unit cost _ (hs.parent_cache q).1
  · exact offered_frontier_valid cost xs index c hsound state
  · exact offered_equalizer_valid cost xs index c hsound state
  · intro t q
    exact offered_equalizer_subset cost xs index c hsound state t q _
  · exact offered_blocks_complement cost xs index c hsound state
  · exact hout.2.2.1

theorem batch_cache_actual_valid (outputs : List (GroupResult data hall cycle))
    (hout : ∀ out ∈ outputs, out.Correct data hall cycle cost (fun root => xs.get (index root)))
    (hold : ∀ root p, Valid (measureProfile cost) (data.cache root p) ∧ Ordered (data.cache root p))
    (root : RootId) (p : Fin n) :
    Valid (measureProfile cost) (batchCache data hall cycle (fun root => xs.get (index root)) outputs root p) ∧
      Ordered (batchCache data hall cycle (fun root => xs.get (index root)) outputs root p) := by
  apply batch_cache_valid data hall cycle _ outputs _ hold
  intro slot p
  exact group_cache_valid data hall cycle cost xs index c hsound (outputs.get slot.1)
    (hout _ (List.get_mem _ _)) slot.2 p

end EnvyFreeResearch.Full.Chores.Outer
