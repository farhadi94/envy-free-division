import EnvyFreeResearch.Full.RefinedChoresDonorCaches
import EnvyFreeResearch.Full.ChoresComponentClosedNext

/-! Concrete all-observer piece caches after a deferred-payment
group, for every donor and the one live survivor. -/

noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresDonorCaches
open Set MeasureTheory ChoreComposition IntervalOracle
open Chores Chores.ComponentPayments Chores.ComponentRecording Chores.Persistent Chores.Suffix
open Chores.SubCoreEntry Chores.SubCorePhysical Chores.InitialPartition Chores.OrderedUnion
open RefinedChoresPhysicalPayment
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (participants : Finset (Fin n)) (label : Fin n)
  (frames : Root → Frame (Fin n) RootId)
  (hpath : ∀ s j, j ∈ participants → Relation.ReflTransGen (fun a b => b ∈ (frames s).allowed a) j label)
  (gap : Root → Fin n → Fin n → ℝ)
  (out : Result (Root := Root) participants)
  (equalizer : Root → Fin n → Fin n → List (Parent n))
  (frontier : Root → Fin n → List (Parent n))

def nextAllocation (s : Root) : ChoreComposition.Allocation (Fin n) RootId :=
  ComponentAssignment.dispatch out.allocation (fun s => (frames s).allocation)
    (fun j => (donorProposal participants label frames hpath gap out j).output) s

theorem next_allocation_assigned (j : participants) :
    nextAllocation participants label frames hpath gap out (out.allocation.assigned j) =
      (donorProposal participants label frames hpath gap out j).output :=
  ComponentAssignment.dispatch_assigned _ _ _ _

theorem next_allocation_unused (hmany : Fintype.card participants < Fintype.card Root) :
    nextAllocation participants label frames hpath gap out (ComponentAssignment.unused out.allocation hmany) =
      (frames (ComponentAssignment.unused out.allocation hmany)).allocation :=
  ComponentAssignment.dispatch_unassigned _ _ _ _ (ComponentAssignment.unused_spec _ _)

theorem next_allocation_root (s : Root) :
    (nextAllocation participants label frames hpath gap out s).root=(frames s).root := by
  unfold nextAllocation
  apply ComponentAssignment.dispatch_property out.allocation _ _
    (fun s (a : ChoreComposition.Allocation (Fin n) RootId) => a.root=(frames s).root)
  · intro s
    rfl
  · intro j
    exact proposal_root _

def nextCache (s : Root) : Fin n → List (Parent n) :=
  ComponentAssignment.dispatch out.allocation
    (fun s p => equalizer s p ((frames s).owner p))
    (fun j => donorCache participants label frames hpath gap out equalizer frontier j) s

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (parent blocks : Root → Fin n → Set ℝ)
  (hp : ∀ s p, parent s p ⊆ Ioc (0 : ℝ) 1)
  (hf : ∀ s p, CacheValid (measureProfile cost) (material (frontier s p)) (frontier s p))
  (he : ∀ s p j, CacheValid (measureProfile cost) (material (equalizer s p j)) (equalizer s p j))
  (hfrontier : ∀ s p, material (frontier s p) ⊆ parent s p)
  (hblocks : ∀ s, blocks s label = parent s label \ material (frontier s label))
  (hparts : PartsCorrect cost (domains blocks (fun _ => label)) Subtype.val out)
include hp hf he hfrontier hblocks hparts

theorem next_cache_valid (s : Root) (p : Fin n) :
    Valid (measureProfile cost) (nextCache participants label frames hpath gap out equalizer frontier s p) ∧
      Ordered (nextCache participants label frames hpath gap out equalizer frontier s p) := by
  have h := ComponentAssignment.dispatch_property out.allocation
    (fun s p => equalizer s p ((frames s).owner p))
    (fun j => donorCache participants label frames hpath gap out equalizer frontier j)
    (fun _ (cache : Fin n → List (Parent n)) =>
      ∀ p, Valid (measureProfile cost) (cache p) ∧ Ordered (cache p))
    (fun s p => ⟨(he s p _).1, (he s p _).2.1⟩)
    (fun j p =>
      let h := donor_cache_correct participants label frames hpath gap out equalizer frontier
        cost parent blocks hp hf he hfrontier hblocks hparts j p
      ⟨h.1, h.2.1⟩) s
  exact h p

theorem next_cache_subset
    (hesub : ∀ s p j, material (equalizer s p j) ⊆ parent s p) (s : Root) (p : Fin n) :
    material (nextCache participants label frames hpath gap out equalizer frontier s p) ⊆ parent s p := by
  have h := ComponentAssignment.dispatch_property out.allocation
    (fun s p => equalizer s p ((frames s).owner p))
    (fun j => donorCache participants label frames hpath gap out equalizer frontier j)
    (fun s (cache : Fin n → List (Parent n)) => ∀ p, material (cache p) ⊆ parent s p)
    (fun s p => hesub s p _) (fun j p => by
      have h := donor_cache_correct participants label frames hpath gap out equalizer frontier
        cost parent blocks hp hf he hfrontier hblocks hparts j p
      rw [h.2.2]
      exact PackageGeometry.proposal_piece_subset _ _ (hesub _) _ _ _) s
  exact h p

variable (hvalues : ∀ s i p j,
    (frames s).equalizerCost i p j = (cost i).real (material (equalizer s p j)))
  (hgap : ∀ s i, gap s label i = (cost i).real (parent s label) - (frames s).baseline i)
include hvalues hgap

theorem next_cache_cost (s : Root) (i p : Fin n) :
    (nextAllocation participants label frames hpath gap out s).cost i p =
      (cost i).real (material (nextCache participants label frames hpath gap out equalizer frontier s p)) := by
  unfold nextAllocation nextCache ComponentAssignment.dispatch
  split_ifs with h
  · have hc := donor_cache_correct participants label frames hpath gap out equalizer frontier
      cost parent blocks hp hf he hfrontier hblocks hparts h.choose p
    rw [material_value cost _ hc.1 hc.2.1]
    exact donor_cached_cost participants label frames hpath gap out equalizer frontier
      cost parent blocks hp hf he hfrontier hblocks hparts hvalues hgap h.choose i p
  · exact hvalues s i p _

end EnvyFreeResearch.Full.RefinedChoresDonorCaches
