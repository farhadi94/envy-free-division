import EnvyFreeResearch.Full.ChoresOuterPrivateNext
import EnvyFreeResearch.Full.ChoresOuterPrivateClosed
import EnvyFreeResearch.Full.ChoresComponentBoundaryRecorded

/-! Literal private complements use only recorded equalizer suffixes or
recorded donor split parts. No new oracle endpoint is introduced. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open ChoreComposition IntervalOracle InitialPartition OrderedUnion Boundary SubCorePhysical Suffix
open scoped Classical
variable {n : ℕ} {Root RootId : Type*}

theorem proposal_private_known (points : Set ℝ)
    (suffix : Fin n → Fin n → List (Parent n))
    (proposal : ChoreComposition.Proposal (Fin n) RootId) (parts : Split n)
    (hs : ∀ p j, CacheKnown points (suffix p j))
    (hp : CacheKnown points parts.suffixParts) (p : Fin n) :
    CacheKnown points (ComponentPieces.proposalResidueCache suffix proposal parts p) := by
  unfold ComponentPieces.proposalResidueCache
  split
  · split
    · exact hp
    · exact hs _ _
  · exact hs _ _

variable [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (visited : Visited state)
  (frames : Root → Frame (Fin n) RootId) (gap : Root → Fin n → Fin n → ℝ)
  (suffix : Root → Fin n → Fin n → List (Parent n))
  (points : Set ℝ) (hs : ∀ s p j, CacheKnown points (suffix s p j))
include hs

theorem next_private_known
    (hall : state.partition.labels ⊆ state.pending)
    (cycle : ProposalCycle (state.outgoing hall)) (out : ComponentBatch.Result state hall cycle)
    (ho : RecordedKnown ClippedRecord.record points out) (s : Root) (p : Fin n) :
    CacheKnown points (nextPrivateCache state hall cycle visited frames gap out suffix s p) := by
  unfold nextPrivateCache ComponentAssignment.dispatch
  split
  · apply proposal_private_known points _ _ _ (hs _)
    intro parent hp
    exact (ho.2.2.2 _) parent (List.mem_append_right _ hp)
  · exact hs _ _ _

theorem closed_private_known (participants : Finset (Fin n))
    (out : ComponentClosed.Result (Root := Root) participants)
    (ho : RecordedKnown id points out) (s : Root) (p : Fin n) :
    CacheKnown points (closedPrivateCache state visited participants frames gap out suffix s p) := by
  unfold closedPrivateCache ComponentAssignment.dispatch
  split
  · apply proposal_private_known points _ _ _ (hs _)
    intro parent hp
    exact (ho.2.2.2 _) parent (List.mem_append_right _ hp)
  · exact hs _ _ _

end EnvyFreeResearch.Full.Chores.Outer
