import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryPrivate
import EnvyFreeResearch.Full.ChoresOuterPrivateBatch
import EnvyFreeResearch.Full.ChoresOuterBoundarySnapshot

/-! Boundary preservation for the actual whole-batch private-residue map. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set IntervalOracle InitialPartition OrderedUnion Boundary Scheduler Components Suffix
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))
  (original : RootId → Snapshot.Output n) (points : Set ℝ)
  (hknown : ∀ root, SnapshotKnown points (original root))
include hknown

theorem group_private_known (out : GroupResult data hall cycle)
    (hout : RecordedKnown ClippedRecord.record points out.result)
    (s : Fin out.group.roots.length) (p : Fin n) :
    CacheKnown points (out.nextPrivate data hall cycle original s p) := by
  apply next_private_known (out.group.state data hall cycle).pending
    (out.group.state data hall cycle).visited (out.group.state data hall cycle).frames
    (originalGaps (out.group.state data hall cycle) original)
    (equalizerSuffixCache (out.group.state data hall cycle) original) points _
    (out.group.all_pending data hall cycle) (out.group.recordedCycle data hall cycle) out.result hout s p
  intro t q j parent hp
  exact ((hknown _).table (q,j)).2 parent (List.mem_append_right _ hp)

theorem batch_private_known (oldPrivate : RootId → Fin n → List (Parent n))
    (outputs : List (GroupResult data hall cycle))
    (hout : ∀ out ∈ outputs, RecordedKnown ClippedRecord.record points out.result)
    (hold : ∀ root p, CacheKnown points (oldPrivate root p)) (root : RootId) (p : Fin n) :
    CacheKnown points (batchPrivateCache data hall cycle original oldPrivate outputs root p) := by
  unfold batchPrivateCache
  split
  · exact group_private_known data hall cycle original points hknown _
      (hout _ (List.get_mem _ _)) _ p
  · exact hold root p
end EnvyFreeResearch.Full.Chores.Outer
