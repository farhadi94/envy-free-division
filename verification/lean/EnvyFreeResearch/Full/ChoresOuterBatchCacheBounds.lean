import EnvyFreeResearch.Full.ChoresOuterBatchCacheFacts

/-! Actual cohort cache containment and whole-private-complement bounds. -/
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

theorem group_cache_subset (out : GroupResult data hall cycle)
    (hout : out.Correct data hall cycle cost (fun root => xs.get (index root)))
    (s : Fin out.group.roots.length) (p : Fin n) :
    material (out.nextCache data hall cycle (fun root => xs.get (index root)) s p) ⊆
      (xs.get (index (data.source (out.group.roots.get s)))).piece p := by
  let state := out.group.state data hall cycle
  let original := fun root => xs.get (index root)
  apply ComponentBatch.next_cache_subset state.pending (out.group.all_pending data hall cycle)
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
  · exact offered_equalizer_subset cost xs index c hsound state

theorem batch_cache_subset (outputs : List (GroupResult data hall cycle))
    (hout : ∀ out ∈ outputs, out.Correct data hall cycle cost (fun root => xs.get (index root)))
    (hold : ∀ root p, material (data.cache root p) ⊆ (xs.get (index root)).piece p)
    (root : RootId) (p : Fin n) :
    material (batchCache data hall cycle (fun root => xs.get (index root)) outputs root p) ⊆
      (xs.get (index root)).piece p := by
  unfold batchCache
  split
  next h =>
    have hs := group_cache_subset data hall cycle cost xs index c hsound (outputs.get h.choose.1)
      (hout _ (List.get_mem _ _)) h.choose.2 p
    change _ ⊆ (xs.get (index (data.source (slotOld data hall cycle outputs h.choose)))).piece p at hs
    simpa only [h.choose_spec] using hs
  next _ => exact hold root p

variable (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)
include hsep hr hH hscale good hk

theorem group_cache_complement (out : GroupResult data hall cycle)
    (hout : out.Correct data hall cycle cost (fun root => xs.get (index root)))
    (s : Fin out.group.roots.length) (p i : Fin n) :
    (cost i).real ((xs.get (index (data.source (out.group.roots.get s)))).piece p \
      material (out.nextCache data hall cycle (fun root => xs.get (index root)) s p)) ≤
      (n : ℝ)*(cost i).real R/H := by
  let state := out.group.state data hall cycle
  have hg := filter_good data (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H
    good out.group.roots out.group.nodup
  exact next_cache_complement_small cost state xs index c hsound R H hsep hr hH hscale hg
    (out.group.all_pending data hall cycle) (out.group.recordedCycle data hall cycle) keep hk
    out.result hout.2.2.1 s p i

theorem batch_cache_complement (outputs : List (GroupResult data hall cycle))
    (hout : ∀ out ∈ outputs, out.Correct data hall cycle cost (fun root => xs.get (index root)))
    (root : RootId) (p i : Fin n) :
    (cost i).real ((xs.get (index root)).piece p \
      material (batchCache data hall cycle (fun root => xs.get (index root)) outputs root p)) ≤
      (n : ℝ)*(cost i).real R/H := by
  unfold batchCache
  split
  next h =>
    have hs := group_cache_complement data hall cycle cost xs index c hsound R H hsep hr hH hscale
      good keep hk (outputs.get h.choose.1) (hout _ (List.get_mem _ _)) h.choose.2 p i
    change (cost i).real ((xs.get (index (data.source (slotOld data hall cycle outputs h.choose)))).piece p \
      material _) ≤ _ at hs
    simpa only [h.choose_spec] using hs
  next _ => exact good.complement_small root p i

end EnvyFreeResearch.Full.Chores.Outer
