import EnvyFreeResearch.Full.ChoresComponentNextCache
import EnvyFreeResearch.Full.ChoresComponentRealization

/-! The concrete open-group caches realize every output cost table while
preserving all frozen ancestor pieces. This joins actual physical oracle
outputs to the package ledger. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentBatch
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open Persistent Suffix SubCoreEntry SubCorePhysical ChoreComposition IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (hall : state.partition.labels ⊆ state.pending)
  (cycle : ProposalCycle (state.outgoing hall)) (visited : Visited state)
  (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
  (gap : Root → Fin n → Fin n → ℝ) (out : Result state hall cycle)
  (old : RootId → Fin n → List (Parent n))
  (equalizer : Root → Fin n → Fin n → List (Parent n))
  (frontier : Root → Fin n → List (Parent n))

def patchedCache : RootId → Fin n → List (Parent n) :=
  ComponentPhysical.patchCache frames old
    (nextCache state hall cycle visited frames gap out equalizer frontier)

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (parent blocks : Root → Fin n → Set ℝ)
  (hp : ∀ s p, parent s p ⊆ Ioc (0 : ℝ) 1)
  (hf : ∀ s p, CacheValid (measureProfile cost) (material (frontier s p)) (frontier s p))
  (he : ∀ s p j, CacheValid (measureProfile cost) (material (equalizer s p j)) (equalizer s p j))
  (hfrontier : ∀ s p, material (frontier s p) ⊆ parent s p)
  (hblocks : ∀ s p, blocks s p = parent s p \ material (frontier s p))
  (hparts : PartsCorrect cost (domains blocks state.partition.representative) Subtype.val out)
include hp hf he hfrontier hblocks hparts

theorem patched_cache_valid
    (hold : ∀ r p, Valid (measureProfile cost) (old r p) ∧ Ordered (old r p)) (r : RootId) (p : Fin n) :
    Valid (measureProfile cost)
        (patchedCache state hall cycle visited frames gap out old equalizer frontier r p) ∧
      Ordered (patchedCache state hall cycle visited frames gap out old equalizer frontier r p) :=
  ComponentPhysical.patch_valid frames (measureProfile cost) old _ hold
    (next_cache_valid state hall cycle visited frames gap out equalizer frontier cost parent blocks
      hp hf he hfrontier hblocks hparts) r p

theorem patched_cache_subset (G : PackageGeometry.Pieces RootId (Fin n))
    (hparent : ∀ s p, parent s p = G.piece (frames s).root p)
    (hesub : ∀ s p j, material (equalizer s p j) ⊆ parent s p)
    (hold : ∀ r p, material (old r p) ⊆ G.piece r p) (r : RootId) (p : Fin n) :
    material (patchedCache state hall cycle visited frames gap out old equalizer frontier r p) ⊆
      G.piece r p := by
  apply ComponentPhysical.patch_subset frames G old _ hold
  intro s p
  rw [← hparent]
  exact next_cache_subset state hall cycle visited frames gap out equalizer frontier cost parent
    blocks hp hf he hfrontier hblocks hparts hesub s p

variable (hvalues : ∀ s i p j,
    (frames s).equalizerCost i p j = (cost i).real (material (equalizer s p j)))
  (hgap : ∀ s p i, gap s p i = (cost i).real (parent s p) - (frames s).baseline i)
include hvalues hgap

theorem output_cost_realized
    (hmany : Fintype.card (Task state hall cycle) < Fintype.card Root)
    (hlive : ∀ s, (packages s).live = some (frames s))
    (hdistinct : (Finset.univ.toList.flatMap (fun s => (packages s).ids)).Nodup)
    (hold : ∀ s a, a ∈ (packages s).frozen → ∀ i p,
      a.cost i p = (cost i).real (material (old a.root p))) :
    ∀ a ∈ (outputPackage state hall cycle visited packages frames gap hmany out).allocations,
      ∀ i p, a.cost i p =
        (cost i).real (material (patchedCache state hall cycle visited frames gap out old equalizer frontier a.root p)) := by
  apply ComponentPhysical.patch_realizes packages frames cost old _
    (nextAllocation state hall cycle visited frames gap out)
    (ComponentPhysical.live_roots_injective packages frames hlive hdistinct)
    (ComponentPhysical.frozen_root_not_live packages frames hlive hdistinct)
    (next_allocation_root state hall cycle visited frames gap out) hold
  · exact next_cache_cost state hall cycle visited frames gap out equalizer frontier cost parent
      blocks hp hf he hfrontier hblocks hparts hvalues hgap
  · exact output_allocation_member state hall cycle visited packages frames gap out hmany

end EnvyFreeResearch.Full.Chores.ComponentBatch
