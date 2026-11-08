import EnvyFreeResearch.Full.ChoresComponentClosedNext
import EnvyFreeResearch.Full.ChoresComponentDonorCaches

/-! Concrete all-observer piece caches after a closed affine
group, for every donor and the one live survivor. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentClosed
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open Persistent Suffix SubCoreEntry SubCorePhysical ChoreComposition IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (visited : Visited state)
  (participants : Finset (Fin n))
  (frames : Root → Frame (Fin n) RootId) (gap : Root → Fin n → Fin n → ℝ)
  (out : Result (Root := Root) participants)
  (equalizer : Root → Fin n → Fin n → List (Parent n))
  (frontier : Root → Fin n → List (Parent n))

def nextCache (s : Root) : Fin n → List (Parent n) :=
  ComponentAssignment.dispatch out.allocation
    (fun s p => equalizer s p ((frames s).owner p))
    (fun j => affineCache state visited frames Subtype.val gap out equalizer frontier j) s

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

theorem next_cache_valid (s : Root) (p : Fin n) :
    Valid (measureProfile cost) (nextCache state visited participants frames gap out equalizer frontier s p) ∧
      Ordered (nextCache state visited participants frames gap out equalizer frontier s p) := by
  have h := ComponentAssignment.dispatch_property out.allocation
    (fun s p => equalizer s p ((frames s).owner p))
    (fun j => affineCache state visited frames Subtype.val gap out equalizer frontier j)
    (fun _ (cache : Fin n → List (Parent n)) =>
      ∀ p, Valid (measureProfile cost) (cache p) ∧ Ordered (cache p))
    (fun s p => ⟨(he s p _).1, (he s p _).2.1⟩)
    (fun j p =>
      let h := affine_cache_correct state visited frames Subtype.val gap out equalizer frontier
        cost parent blocks hp hf he hfrontier hblocks hparts j p
      ⟨h.1, h.2.1⟩) s
  exact h p

theorem next_cache_subset
    (hesub : ∀ s p j, material (equalizer s p j) ⊆ parent s p) (s : Root) (p : Fin n) :
    material (nextCache state visited participants frames gap out equalizer frontier s p) ⊆ parent s p := by
  have h := ComponentAssignment.dispatch_property out.allocation
    (fun s p => equalizer s p ((frames s).owner p))
    (fun j => affineCache state visited frames Subtype.val gap out equalizer frontier j)
    (fun s (cache : Fin n → List (Parent n)) => ∀ p, material (cache p) ⊆ parent s p)
    (fun s p => hesub s p _) (fun j p => by
      have h := affine_cache_correct state visited frames Subtype.val gap out equalizer frontier
        cost parent blocks hp hf he hfrontier hblocks hparts j p
      rw [h.2.2]
      exact PackageGeometry.proposal_piece_subset _ _ (hesub _) _ _ _) s
  exact h p

variable (hvalues : ∀ s i p j,
    (frames s).equalizerCost i p j = (cost i).real (material (equalizer s p j)))
  (hgap : ∀ s p i, gap s p i = (cost i).real (parent s p) - (frames s).baseline i)
include hvalues hgap

theorem next_cache_cost (s : Root) (i p : Fin n) :
    (nextAllocation state visited participants frames gap out s).cost i p =
      (cost i).real (material (nextCache state visited participants frames gap out equalizer frontier s p)) := by
  unfold nextAllocation nextCache ComponentAssignment.dispatch
  split_ifs with h
  · have hc := affine_cache_correct state visited frames Subtype.val gap out equalizer frontier
      cost parent blocks hp hf he hfrontier hblocks hparts h.choose p
    rw [material_value cost _ hc.1 hc.2.1]
    exact affine_cached_cost state visited frames Subtype.val gap out equalizer frontier
      cost parent blocks hp hf he hfrontier hblocks hparts hvalues hgap h.choose i p
  · exact hvalues s i p _

end EnvyFreeResearch.Full.Chores.ComponentClosed
