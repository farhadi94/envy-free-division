import EnvyFreeResearch.Full.ChoresTerminalOffers
import EnvyFreeResearch.Full.ChoresOuterNextCache
import EnvyFreeResearch.Full.ChoresComponentClosedPhysicalJoin

/-! Physical cache realization for the actual affine terminal output.
Both the donor fragments and all inherited frozen fragments are retained. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open ComponentRecording ComponentPayments
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) [Nonempty (Fin data.size)]
  (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
  (A : Finset (Fin n)) (out : ComponentClosed.Result (Root := Fin data.size) A)

def updatedCache : RootId → Fin n → List (Parent n) :=
  ComponentClosed.patchedCache data.pending data.visited A data.frames
    (Outer.originalGaps data original) out data.cache (Outer.equalizerCache data original)
    (fronts data original r H)

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
  (good : data.Good original cost r H)
  (hparts : PartsCorrect cost (domains (blocks data original r H)
    data.pending.partition.representative) Subtype.val out)

include hsound

theorem parent_unit (s : Fin data.size) (p : Fin n) :
    (original (data.source s)).piece p ⊆ Ioc (0 : ℝ) 1 := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  exact Outer.valid_material_unit cost _ (hs.parent_cache p).1

theorem equalizers_valid (s : Fin data.size) (p j : Fin n) :
    CacheValid (measureProfile cost) (material (Outer.equalizerCache data original s p j))
      (Outer.equalizerCache data original s p j) := by
  obtain ⟨U,hs⟩ := hsound (data.source s)
  exact ⟨(snapshot_equalizers hs p j).2.1.1,(snapshot_equalizers hs p j).2.1.2.1,rfl⟩

include good hparts

theorem updated_cache_valid (root : RootId) (p : Fin n) :
    Valid (measureProfile cost) (updatedCache data original r H A out root p) ∧
      Ordered (updatedCache data original r H A out root p) :=
  ComponentClosed.patched_cache_valid data.pending data.visited A data.frames
    (Outer.originalGaps data original) out data.cache (Outer.equalizerCache data original)
    (fronts data original r H) cost (fun s p => (original (data.source s)).piece p)
    (blocks data original r H) (parent_unit data original cost c hsound)
    (fronts_valid data original r H cost c hsound) (equalizers_valid data original cost c hsound)
    (fronts_subset data original r H cost c hsound) (blocks_complement data original r H cost c hsound)
    hparts good.cache root p

theorem updated_cache_subset (G : PackageGeometry.Pieces RootId (Fin n))
    (hG : ∀ root p, G.piece root p=(original root).piece p) (root : RootId) (p : Fin n) :
    material (updatedCache data original r H A out root p) ⊆ G.piece root p := by
  apply ComponentClosed.patched_cache_subset data.pending data.visited A data.frames
    (Outer.originalGaps data original) out data.cache (Outer.equalizerCache data original)
    (fronts data original r H) cost (fun s p => (original (data.source s)).piece p)
    (blocks data original r H) (parent_unit data original cost c hsound)
    (fronts_valid data original r H cost c hsound) (equalizers_valid data original cost c hsound)
    (fronts_subset data original r H cost c hsound) (blocks_complement data original r H cost c hsound)
    hparts G
  · intro s p
    rw [hG,good.source]
  · intro s p j
    obtain ⟨U,hs⟩ := hsound (data.source s)
    exact Outer.original_equalizer_subset cost hs p j
  · intro root p
    rw [hG]
    exact good.cache_subset root p

theorem updated_cache_realizes (p : Fin n)
    (hmany : Fintype.card A < Fintype.card (Fin data.size))
    (hlabel : ∀ j ∈ A, data.pending.partition.representative j=p) :
    ∀ a ∈ (ComponentClosed.outputPackage data.pending data.visited A p data.packages data.frames
      (Outer.originalGaps data original) out hmany).allocations, ∀ i q,
      a.cost i q=(cost i).real (material (updatedCache data original r H A out a.root q)) := by
  apply ComponentClosed.output_cost_realized data.pending data.visited A p data.packages data.frames
    (Outer.originalGaps data original) out data.cache (Outer.equalizerCache data original)
    (fronts data original r H) cost (fun s p => (original (data.source s)).piece p)
    (blocks data original r H) (parent_unit data original cost c hsound)
    (fronts_valid data original r H cost c hsound) (equalizers_valid data original cost c hsound)
    (fronts_subset data original r H cost c hsound) (blocks_complement data original r H cost c hsound)
    hparts
  · intro s i p j
    obtain ⟨U,hs⟩ := hsound (data.source s)
    exact Outer.original_equalizer_value cost hs (data.frames s) (good.original_frame s) i p j
  · intro s p i
    obtain ⟨U,hs⟩ := hsound (data.source s)
    exact Outer.original_gap cost hs (data.frames s) (good.original_frame s) p i
  · exact hlabel
  · exact good.live
  · exact Outer.active_ids_distinct data original cost r H good
  · exact Outer.active_frozen_cost data original cost r H good

end EnvyFreeResearch.Full.Chores.Terminal
