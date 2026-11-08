import EnvyFreeResearch.Full.ChoresOuterPrivateCache
import EnvyFreeResearch.Full.ChoresComponentNextCache

/-! Complementary caches for the actual donor dispatch and survivor. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open ChoreComposition IntervalOracle InitialPartition OrderedUnion
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (hall : state.partition.labels ⊆ state.pending)
  (cycle : ProposalCycle (state.outgoing hall)) (visited : Visited state)
  (frames : Root → Frame (Fin n) RootId) (gap : Root → Fin n → Fin n → ℝ)
  (out : ComponentBatch.Result state hall cycle)
  (equalizer equalizerSuffix : Root → Fin n → Fin n → List (Parent n))
  (frontier : Root → Fin n → List (Parent n))

def nextPrivateCache (s : Root) : Fin n → List (Parent n) :=
  ComponentAssignment.dispatch out.allocation
    (fun s p => equalizerSuffix s p ((ComponentFrames.advance state hall cycle visited frames s).owner p))
    (fun j => ComponentPieces.proposalResidueCache (equalizerSuffix (out.allocation.assigned j))
      (ordinary state visited frames Subtype.val gap out j) (out.parts j)) s

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

theorem next_private_correct (s : Root) (p : Fin n) :
    CacheValid (measureProfile cost)
      (parent s p \ material (ComponentBatch.nextCache state hall cycle visited frames gap out equalizer frontier s p))
      (nextPrivateCache state hall cycle visited frames gap out equalizerSuffix s p) := by
  unfold ComponentBatch.nextCache nextPrivateCache ComponentAssignment.dispatch
  split
  next h =>
    have hc := ordinary_cache_correct state visited frames Subtype.val gap out equalizer frontier
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
      (ordinary state visited frames Subtype.val gap out h.choose) (out.parts h.choose)
      (hsuffix _) ⟨(hparts h.choose).2.1,(hparts h.choose).2.2.1,rfl⟩ hsub p
    simpa only [h.choose_spec] using hh
  next _ => exact hsuffix s p _
end EnvyFreeResearch.Full.Chores.Outer
