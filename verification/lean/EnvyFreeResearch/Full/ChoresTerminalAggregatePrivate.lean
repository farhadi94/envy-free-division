import EnvyFreeResearch.Full.ChoresTerminalExtractionPatched

/-! Exhausted terminal batches leave a small entire private complement at
each original root, including roots already frozen before the batch. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Snapshot Frontier
open ChoreComposition ComponentRecording ComponentPayments ComponentDonors ComponentExtraction
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
  (A : Finset (Fin n)) (out : ComponentClosed.Result (Root := Fin data.size) A)
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
  (good : data.Good original cost r H) (hr : ∀ i, 0 ≤ r i) (hH : 0 < H)
  (hparts : PartsCorrect cost (domains (blocks data original r H)
    data.pending.partition.representative) Subtype.val out)


variable (hsmall : ∀ j : A, ∀ s i,
  (cost i).real (blocks data original r H s (data.pending.partition.representative j)) ≤ (n : ℝ)*r i/H)

include hsound good hr hH hparts hsmall

theorem exhausted_next_complement_small (s : Fin data.size) (p i : Fin n) :
    (cost i).real ((original (data.source s)).piece p \
      material (ComponentClosed.nextCache data.pending data.visited A data.frames
        (Outer.originalGaps data original) out (Outer.equalizerCache data original)
        (fronts data original r H) s p)) ≤ (n : ℝ)*r i/H := by
  apply ComponentAssignment.dispatch_property out.allocation
    (fun s p => Outer.equalizerCache data original s p ((data.frames s).owner p))
    (fun j => affineCache data.pending data.visited data.frames Subtype.val
      (Outer.originalGaps data original) out (Outer.equalizerCache data original)
      (fronts data original r H) j)
    (fun s cache => (cost i).real ((original (data.source s)).piece p \ material (cache p)) ≤ (n : ℝ)*r i/H)
  · intro t
    change (cost i).real ((original (data.source t)).piece p \
      material ((original (data.source t)).equalizers (p,(data.frames t).owner p)).parts.prefixParts) ≤ _
    rw [← good.live_cache t p]
    exact good.complement_small _ p i
  · intro j
    have hc := affine_cache_correct data.pending data.visited data.frames Subtype.val
      (Outer.originalGaps data original) out (Outer.equalizerCache data original)
      (fronts data original r H) cost (fun s p => (original (data.source s)).piece p)
      (blocks data original r H) (parent_unit data original cost c hsound)
      (fronts_valid data original r H cost c hsound) (equalizers_valid data original cost c hsound)
      (fronts_subset data original r H cost c hsound) (blocks_complement data original r H cost c hsound)
      hparts j p
    rw [hc.2.2]
    obtain ⟨U,hs⟩ := hsound (data.source (out.allocation.assigned j))
    apply Outer.proposal_complement_small cost hs (data.frames (out.allocation.assigned j))
      ((Outer.active_package_valid data original cost r H good _).live_good _ (good.live _))
      r H hr hH data.component (data.frontier (out.allocation.assigned j)) (good.frontier _)
      _ rfl _ _ _ p i
    · intro q hq
      exact owner_other data.pending data.visited data.frames Subtype.val out j good.allowed q hq
    · intro k
      exact (measureReal_mono (μ := cost k)
        (suffix_subset cost _ Subtype.val data.pending.partition.representative out hparts j)).trans
          (hsmall j (out.allocation.assigned j) k)

theorem exhausted_patched_complement_small (root : RootId) (p i : Fin n) :
    (cost i).real ((original root).piece p \
      material (updatedCache data original r H A out root p)) ≤ (n : ℝ)*r i/H := by
  unfold updatedCache ComponentClosed.patchedCache ComponentPhysical.patchCache
  split
  next h =>
    have hb := exhausted_next_complement_small data original r H A out cost c
      hsound good hr hH hparts hsmall h.choose p i
    have heq : data.source h.choose=root := (good.source h.choose).symm.trans h.choose_spec
    simpa only [heq] using hb
  next _ => exact good.complement_small root p i

end EnvyFreeResearch.Full.Chores.Terminal
