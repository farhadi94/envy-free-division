import EnvyFreeResearch.Full.ChoresOuterComplement

/-! A paid open group preserves the bound on every original private
complement, including all already frozen ancestors. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open ChoreComposition ComponentDonors ComponentRecording ComponentPayments
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

omit [Fintype RootId] in
theorem valid_material_unit (cache : List (Parent n)) (hc : Valid (measureProfile cost) cache) :
    material cache ⊆ Ioc (0 : ℝ) 1 := by
  induction cache with
  | nil => exact empty_subset _
  | cons p ps ih =>
    intro x hx
    rcases hx with hx | hx
    · exact ⟨lt_of_le_of_lt hc.1.1.1 hx.1,hx.2.trans hc.1.1.2.2⟩
    · exact ih hc.2 hx

variable (data : Data n RootId) [Nonempty (Fin data.size)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (cutter : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U cutter (xs.get (index root)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hpos : ∀ i, 0 < (cost i).real R) (hHlarge : 1 < H) (hscale : (n : ℝ) < H*H)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : Components.ProposalCycle (data.pending.outgoing hall))
  (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)
  (result : ComponentBatch.Result data.pending hall cycle)
  (hparts : PartsCorrect cost
    (domains (offeredBlocks data (fun root => xs.get (index root))) data.pending.partition.representative)
    Subtype.val result)

include hsound hsep hpos hHlarge hscale good hparts hk

theorem next_cache_complement_small (s : Fin data.size) (p i : Fin n) :
    (cost i).real ((xs.get (index (data.source s))).piece p \
      material (ComponentBatch.nextCache data.pending hall cycle data.visited data.frames
        (originalGaps data (fun root => xs.get (index root))) result
        (equalizerCache data (fun root => xs.get (index root)))
        (offeredFrontier data (fun root => xs.get (index root))) s p)) ≤
      (n : ℝ)*(cost i).real R/H := by
  apply ComponentAssignment.dispatch_property result.allocation
    (fun s p => equalizerCache data (fun root => xs.get (index root)) s p
      ((ComponentFrames.advance data.pending hall cycle data.visited data.frames s).owner p))
    (fun j => ordinaryCache data.pending data.visited data.frames Subtype.val
      (originalGaps data (fun root => xs.get (index root))) result
      (equalizerCache data (fun root => xs.get (index root)))
      (offeredFrontier data (fun root => xs.get (index root))) j)
    (fun s cache => (cost i).real ((xs.get (index (data.source s))).piece p \ material (cache p)) ≤
      (n : ℝ)*(cost i).real R/H)
  · intro t
    obtain ⟨U,hs⟩ := hsound (data.source t)
    have hnew := ComponentFrames.advance_good data.pending hall cycle data.visited data.frames t
      (good.allowed t) (fun p i => original_equalized cost hs (data.frames t) (good.original_frame t) p i)
    exact old_complement_small cost hs p _ H _ _ _ _
      (advanced_frontier data _ cost _ H good hall cycle keep hk (fun i => (hpos i).le)
        (by linarith) t p) (fun i => (hpos i).le) (by linarith) _ (hnew.1 p) i
  · intro j
    have hp : ∀ t q, (xs.get (index (data.source t))).piece q ⊆ Ioc (0 : ℝ) 1 := by
      intro t q
      obtain ⟨U,hs⟩ := hsound (data.source t)
      exact valid_material_unit cost _ (hs.parent_cache q).1
    have hc := ComponentDonors.ordinary_cache_correct data.pending data.visited data.frames Subtype.val
      (originalGaps data (fun root => xs.get (index root))) result
      (equalizerCache data (fun root => xs.get (index root)))
      (offeredFrontier data (fun root => xs.get (index root))) cost
      (fun t q => (xs.get (index (data.source t))).piece q)
      (offeredBlocks data (fun root => xs.get (index root))) hp
      (offered_frontier_valid cost xs index cutter hsound data)
      (offered_equalizer_valid cost xs index cutter hsound data)
      (fun t q => offered_equalizer_subset cost xs index cutter hsound data t q _)
      (offered_blocks_complement cost xs index cutter hsound data) hparts j p
    rw [hc.2.2]
    exact ordinary_complement_small cost data xs index cutter hsound R H hsep hpos hHlarge hscale
      good hall cycle result hparts j p i

theorem patched_complement_small (root : RootId) (p i : Fin n) :
    (cost i).real ((xs.get (index root)).piece p \
      material (ComponentBatch.patchedCache data.pending hall cycle data.visited data.frames
        (originalGaps data (fun root => xs.get (index root))) result data.cache
        (equalizerCache data (fun root => xs.get (index root)))
        (offeredFrontier data (fun root => xs.get (index root))) root p)) ≤
      (n : ℝ)*(cost i).real R/H := by
  unfold ComponentBatch.patchedCache ComponentPhysical.patchCache
  split
  next h =>
    have hb := next_cache_complement_small cost data xs index cutter hsound R H hsep hpos hHlarge hscale
      good hall cycle keep hk result hparts h.choose p i
    have heq : data.source h.choose=root := (good.source h.choose).symm.trans h.choose_spec
    simpa only [heq] using hb
  next _ => exact good.complement_small root p i

end EnvyFreeResearch.Full.Chores.Outer
