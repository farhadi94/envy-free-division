import EnvyFreeResearch.Full.ChoresOuterPrivateCache
import EnvyFreeResearch.Full.ChoresComponentClosedCache

/-! Complementary caches for the actual closed affine donor dispatch and unused root. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open ChoreComposition IntervalOracle InitialPartition OrderedUnion
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (visited : Visited state)
  (participants : Finset (Fin n))
  (frames : Root → Frame (Fin n) RootId) (gap : Root → Fin n → Fin n → ℝ)
  (out : ComponentClosed.Result (Root := Root) participants)
  (equalizer equalizerSuffix : Root → Fin n → Fin n → List (Parent n))
  (frontier : Root → Fin n → List (Parent n))

def closedPrivateCache (s : Root) : Fin n → List (Parent n) :=
  ComponentAssignment.dispatch out.allocation
    (fun s p => equalizerSuffix s p ((frames s).owner p))
    (fun j => ComponentPieces.proposalResidueCache (equalizerSuffix (out.allocation.assigned j))
      (affine state visited frames Subtype.val gap out j) (out.parts j)) s

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (parent blocks : Root → Fin n → Set ℝ)
  (hp : ∀ s p, parent s p ⊆ Ioc (0 : ℝ) 1)
  (hf : ∀ s p, CacheValid (measureProfile cost) (material (frontier s p)) (frontier s p))
  (he : ∀ s p j, CacheValid (measureProfile cost) (material (equalizer s p j)) (equalizer s p j))
  (hfrontier : ∀ s p, material (frontier s p) ⊆ parent s p)
  (hblocks : ∀ s p, blocks s p = parent s p \ material (frontier s p))
  (hparts : PartsCorrect cost (domains blocks state.partition.representative) Subtype.val out)
  (hsuffix : ∀ s p j, CacheValid (measureProfile cost)
    (parent s p \ material (equalizer s p j)) (equalizerSuffix s p j))
include hp hf he hfrontier hblocks hparts hsuffix

theorem closed_private_correct (s : Root) (p : Fin n) :
    CacheValid (measureProfile cost)
      (parent s p \ material (ComponentClosed.nextCache state visited participants frames gap out equalizer frontier s p))
      (closedPrivateCache state visited participants frames gap out equalizerSuffix s p) := by
  unfold ComponentClosed.nextCache closedPrivateCache ComponentAssignment.dispatch
  split
  next h =>
    have hc := affine_cache_correct state visited frames Subtype.val gap out equalizer frontier
      cost parent blocks hp hf he hfrontier hblocks hparts h.choose p
    rw [hc.2.2]
    have hsub : material (out.parts h.choose).suffixParts ⊆
        parent (out.allocation.assigned h.choose)
          (state.partition.representative (h.choose : Fin n)) := by
      apply (suffix_subset cost blocks Subtype.val state.partition.representative out hparts h.choose).trans
      rw [hblocks]
      exact sdiff_subset
    have hh := ComponentPieces.proposal_residue_cache_correct (measureProfile cost)
      (parent (out.allocation.assigned h.choose)) (equalizer (out.allocation.assigned h.choose))
      (equalizerSuffix (out.allocation.assigned h.choose))
      (affine state visited frames Subtype.val gap out h.choose) (out.parts h.choose)
      (hsuffix _) ⟨(hparts h.choose).2.1,(hparts h.choose).2.2.1,rfl⟩ hsub p
    simpa only [h.choose_spec] using hh
  next _ => exact hsuffix s p _
end EnvyFreeResearch.Full.Chores.Outer
