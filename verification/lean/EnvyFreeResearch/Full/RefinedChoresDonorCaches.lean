import EnvyFreeResearch.Full.RefinedChoresPhysicalPayment
import EnvyFreeResearch.Full.ChoresComponentPieceCache

/-! Physical finite-union caches for the new deferred-payment donor outputs.
All retained donor pieces are assembled from actual recorded prefixes and
suffixes; zero-cost intervals are retained in their physical material. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresDonorCaches
open Set MeasureTheory IntervalOracle
open Chores.InitialPartition Chores.OrderedUnion
open ChoreComposition Chores Chores.ComponentRecording Chores.ComponentPayments
open Chores.ComponentPieces Chores.SubCorePhysical RefinedChoresPhysicalPayment
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
    (C : Finset (Fin n)) (p : Fin n)
    (frames : Root → Frame (Fin n) RootId)
    (hpath : ∀ s j, j ∈ C → Relation.ReflTransGen (fun a b => b ∈ (frames s).allowed a) j p)
    (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) C)

def donorProposal (j : ↥C) : ChoreComposition.Proposal (Fin n) RootId :=
  ordinaryProposal (frames (out.allocation.assigned j)) p j
    (owners C p frames hpath out j) (fun i => utilities C p gap out i j)

variable (equalizer : Root → Fin n → Fin n → List (Parent n))
    (frontier : Root → Fin n → List (Parent n))

def donorCache (j : ↥C) (a : Fin n) : List (Parent n) :=
  proposalCache (equalizer (out.allocation.assigned j))
    (frontier (out.allocation.assigned j) p)
    (donorProposal C p frames hpath gap out j) (out.parts j) a

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (parent blocks : Root → Fin n → Set ℝ)
    (hp : ∀ s a, parent s a ⊆ Ioc (0 : ℝ) 1)
    (hf : ∀ s a, CacheValid (measureProfile cost) (material (frontier s a)) (frontier s a))
    (he : ∀ s a j, CacheValid (measureProfile cost) (material (equalizer s a j)) (equalizer s a j))
    (hfrontier : ∀ s a, material (frontier s a) ⊆ parent s a)
    (hblocks : ∀ s, blocks s p = parent s p \ material (frontier s p))
    (hparts : PartsCorrect cost (domains blocks (fun _ => p)) Subtype.val out)
include hp hf he hfrontier hblocks hparts

theorem donor_cache_correct (j : ↥C) (a : Fin n) :
    CacheValid (measureProfile cost)
      (PackageGeometry.proposalPiece (parent (out.allocation.assigned j))
        (fun a k => material (equalizer (out.allocation.assigned j) a k))
        (donorProposal C p frames hpath gap out j) (material (out.parts j).suffixParts) a)
      (donorCache C p frames hpath gap out equalizer frontier j a) := by
  apply proposal_cache_correct _ _ _ _ _ _
    (1 - (out.allocation.point (out.allocation.assigned j)).record.point)
    (hf _ _) (he _) (hfrontier _ _) (hp _ _)
  simpa only [PartsCorrect,ComponentPayments.domains,hblocks,donorProposal,ordinaryProposal] using hparts j

variable (hvalues : ∀ s i a j,
    (frames s).equalizerCost i a j = (cost i).real (material (equalizer s a j)))
    (hgap : ∀ s i, gap s p i = (cost i).real (parent s p) - (frames s).baseline i)
include hvalues hgap

theorem donor_cached_cost (j : ↥C) (i a : Fin n) :
    (donorProposal C p frames hpath gap out j).output.cost i a =
      cachedValue (donorCache C p frames hpath gap out equalizer frontier j a) i := by
  have hc := donor_cache_correct C p frames hpath gap out equalizer frontier cost
    parent blocks hp hf he hfrontier hblocks hparts j a
  rw [← material_value cost _ hc.1 hc.2.1,hc.2.2]
  have hdec : (instDecidableEqFin n) = (fun a b : Fin n => Classical.propDecidable (a=b)) :=
    Subsingleton.elim _ _
  rw [hdec]
  apply PackageGeometry.proposal_piece_value
  · exact (suffix_subset cost blocks (Subtype.val : ↥C → Fin n) (fun _ => p) out hparts j).trans
      (by rw [hblocks]; exact sdiff_subset)
  · exact material_measurable _
  · exact hvalues _
  · intro k
    change utilities C p gap out k j = _
    simp only [utilities,dite_eq_left j.property]
    rw [suffix_values cost blocks (Subtype.val : ↥C → Fin n) (fun _ => p) gap out hparts,hgap]
    rfl

end EnvyFreeResearch.Full.RefinedChoresDonorCaches
#print axioms EnvyFreeResearch.Full.RefinedChoresDonorCaches.donor_cached_cost
