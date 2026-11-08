import EnvyFreeResearch.Full.ChoresComponentPieceCache

/-! Actual donor allocations are accompanied by finite-union caches of
all retained prefixes. Their numerical proposal costs equal those cached
original-observer values. No further oracle query is needed. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentDonors
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentPieces
open Persistent Suffix SubCoreEntry SubCorePhysical ChoreComposition IntervalOracle InitialPartition OrderedUnion
open scoped Classical

variable {n : ℕ} {Task Root RootId Payload : Type*} [Fintype Task] [DecidableEq Task]
  [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (visited : Visited state)
  (frames : Root → Frame (Fin n) RootId) (agent : Task → Fin n)
  (gap : Root → Fin n → Fin n → ℝ) (out : Recorded Payload Task Root n)
  (equalizer : Root → Fin n → Fin n → List (Parent n))
  (frontier : Root → Fin n → List (Parent n))

def ordinaryCache (j : Task) (p : Fin n) : List (Parent n) :=
  proposalCache (equalizer (out.allocation.assigned j))
    (frontier (out.allocation.assigned j) (state.partition.representative (agent j)))
    (ordinary state visited frames agent gap out j) (out.parts j) p

def affineCache (j : Task) (p : Fin n) : List (Parent n) :=
  proposalCache (equalizer (out.allocation.assigned j))
    (frontier (out.allocation.assigned j) (state.partition.representative (agent j)))
    (affine state visited frames agent gap out j) (out.parts j) p

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (parent blocks : Root → Fin n → Set ℝ)
  (hp : ∀ s p, parent s p ⊆ Ioc (0 : ℝ) 1)
  (hf : ∀ s p, CacheValid (measureProfile cost) (material (frontier s p)) (frontier s p))
  (he : ∀ s p j, CacheValid (measureProfile cost) (material (equalizer s p j)) (equalizer s p j))
  (hfrontier : ∀ s p, material (frontier s p) ⊆ parent s p)
  (hblocks : ∀ s p, blocks s p = parent s p \ material (frontier s p))
  (hparts : PartsCorrect cost (domains blocks state.partition.representative) agent out)
include hp hf he hfrontier hblocks hparts

theorem ordinary_cache_correct (j : Task) (p : Fin n) :
    CacheValid (measureProfile cost)
      (PackageGeometry.proposalPiece (parent (out.allocation.assigned j))
        (fun p k => material (equalizer (out.allocation.assigned j) p k))
        (ordinary state visited frames agent gap out j) (material (out.parts j).suffixParts) p)
      (ordinaryCache state visited frames agent gap out equalizer frontier j p) := by
  apply proposal_cache_correct _ _ _ _ _ _
    (1 - (out.allocation.point (out.allocation.assigned j)).record.point)
    (hf _ _) (he _) (hfrontier _ _) (hp _ _)
  simpa only [PartsCorrect, ComponentPayments.domains, hblocks, ordinary, ordinaryProposal] using hparts j

theorem affine_cache_correct (j : Task) (p : Fin n) :
    CacheValid (measureProfile cost)
      (PackageGeometry.proposalPiece (parent (out.allocation.assigned j))
        (fun p k => material (equalizer (out.allocation.assigned j) p k))
        (affine state visited frames agent gap out j) (material (out.parts j).suffixParts) p)
      (affineCache state visited frames agent gap out equalizer frontier j p) := by
  apply proposal_cache_correct _ _ _ _ _ _
    (1 - (out.allocation.point (out.allocation.assigned j)).record.point)
    (hf _ _) (he _) (hfrontier _ _) (hp _ _)
  simpa only [PartsCorrect, ComponentPayments.domains, hblocks, affine, affineProposal] using hparts j

variable (hvalues : ∀ s i p j,
    (frames s).equalizerCost i p j = (cost i).real (material (equalizer s p j)))
  (hgap : ∀ s p i, gap s p i = (cost i).real (parent s p) - (frames s).baseline i)
include hvalues hgap

theorem ordinary_cached_cost (j : Task) (i p : Fin n) :
    (ordinary state visited frames agent gap out j).output.cost i p =
      cachedValue (ordinaryCache state visited frames agent gap out equalizer frontier j p) i := by
  have h := ordinary_cache_correct state visited frames agent gap out equalizer frontier cost
    parent blocks hp hf he hfrontier hblocks hparts j p
  rw [← material_value cost _ h.1 h.2.1, h.2.2]
  exact ordinary_piece_value state visited frames agent gap cost blocks parent
    (fun s p j => material (equalizer s p j)) (fun s p => by rw [hblocks]; exact sdiff_subset)
    hvalues hgap out hparts j i p

theorem affine_cached_cost (j : Task) (i p : Fin n) :
    (affine state visited frames agent gap out j).output.cost i p =
      cachedValue (affineCache state visited frames agent gap out equalizer frontier j p) i := by
  have h := affine_cache_correct state visited frames agent gap out equalizer frontier cost
    parent blocks hp hf he hfrontier hblocks hparts j p
  rw [← material_value cost _ h.1 h.2.1, h.2.2]
  exact affine_piece_value state visited frames agent gap cost blocks parent
    (fun s p j => material (equalizer s p j)) (fun s p => by rw [hblocks]; exact sdiff_subset)
    hvalues hgap out hparts j i p

end EnvyFreeResearch.Full.Chores.ComponentDonors
