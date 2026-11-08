import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryProgram
import EnvyFreeResearch.Full.ChoresOuterBatchCache
import EnvyFreeResearch.Full.ChoresComponentBoundaryAssembly

/-! Free physical cohort assembly and the simultaneous old-root patch
preserve the actual query boundary ledger, including frozen ancestors. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Scheduler Components ChoreComposition Boundary SubCoreEntry Persistent Suffix SubCorePhysical
open scoped Classical
variable {n : ℕ} {RootId : Type*}

theorem proposal_cache_known (points : Set ℝ)
    (equalizer : Fin n → Fin n → List (Parent n)) (frontier : List (Parent n))
    (proposal : ChoreComposition.Proposal (Fin n) RootId) (parts : Split n)
    (he : ∀ p j, CacheKnown points (equalizer p j)) (hf : CacheKnown points frontier)
    (hp : CacheKnown points parts.prefixParts) (p : Fin n) :
    CacheKnown points (ComponentPieces.proposalCache equalizer frontier proposal parts p) := by
  unfold ComponentPieces.proposalCache
  split
  · split
    · exact assemble_known (hf.append hp)
    · exact he _ _
  · exact he _ _

variable (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))
  (original : RootId → Snapshot.Output n) (points : Set ℝ)
  (hknown : ∀ root, SnapshotKnown points (original root))
include hknown

theorem group_next_cache_known (out : GroupResult data hall cycle)
    (hout : RecordedKnown ClippedRecord.record points out.result)
    (s : Fin out.group.roots.length) (p : Fin n) :
    CacheKnown points (out.nextCache data hall cycle original s p) := by
  unfold GroupResult.nextCache ComponentBatch.nextCache ComponentAssignment.dispatch
  split
  · unfold ComponentDonors.ordinaryCache
    apply proposal_cache_known points
    · intro q j parent hp
      exact ((hknown _).table (q,j)).2 parent (List.mem_append_left _ hp)
    · intro parent hp
      exact ((hknown _).table _).2 parent (List.mem_append_left _ hp)
    · intro parent hp
      exact (hout.2.2.2 _) parent (List.mem_append_left _ hp)
  · intro parent hp
    exact ((hknown _).table _).2 parent (List.mem_append_left _ hp)

theorem batch_cache_known (outputs : List (GroupResult data hall cycle))
    (hout : ∀ out ∈ outputs, RecordedKnown ClippedRecord.record points out.result)
    (hold : ∀ root p, CacheKnown points (data.cache root p)) (root : RootId) (p : Fin n) :
    CacheKnown points (batchCache data hall cycle original outputs root p) := by
  unfold batchCache
  split
  · exact group_next_cache_known data hall cycle original points hknown _
      (hout _ (List.get_mem _ _)) _ p
  · exact hold root p

end EnvyFreeResearch.Full.Chores.Outer
