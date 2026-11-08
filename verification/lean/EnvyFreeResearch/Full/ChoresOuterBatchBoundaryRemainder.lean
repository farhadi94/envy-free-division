import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryPrivate
import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryAssembly
import EnvyFreeResearch.Full.ChoresOuterPrivateTerminal
import EnvyFreeResearch.Full.ChoresOuterResidueRemoval
import EnvyFreeResearch.Full.ChoresComponentExtraction

/-! Terminal extraction and omission of entire private pieces preserve
literal coordinate provenance, including zero-value affine assignments. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set IntervalOracle InitialPartition OrderedUnion Boundary Scheduler Components
open ChoreComposition ComponentRecording Persistent Suffix SubCorePhysical
open scoped Classical
variable {n : ℕ} {RootId : Type*}

theorem extracted_cache_known {Task Root Payload : Type*} [Fintype Task]
    [DecidableEq Task] [Fintype Root] [Nonempty Root]
    (points : Set ℝ) (out : Recorded Payload Task Root n) (view : Payload → Record n)
    (ho : RecordedKnown view points out) :
    CacheKnown points (ComponentExtraction.extractedCache out) := by
  apply join_labels_known
  intro j parent hp
  exact (ho.2.2.2 j) parent (List.mem_append_right _ hp)

theorem remove_private_known (points : Set ℝ) (cache : RootId → Fin n → List (Parent n))
    (removed : Finset (RootId × Fin n)) (hc : ∀ root p, CacheKnown points (cache root p))
    (root : RootId) (p : Fin n) :
    CacheKnown points (removePrivate cache removed root p) := by
  unfold removePrivate
  split
  · simp [CacheKnown]
  · exact hc root p

variable [Fintype RootId] (data : Data n RootId) [Nonempty (Fin data.size)]
    (original : RootId → Snapshot.Output n) (A : Finset (Fin n))
    (out : ComponentClosed.Result (Root := Fin data.size) A)
    (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (original root))
    (hout : RecordedKnown id points out)
include hknown hout

theorem terminal_private_known (oldPrivate : RootId → Fin n → List (Parent n))
    (hold : ∀ root p, CacheKnown points (oldPrivate root p)) (root : RootId) (p : Fin n) :
    CacheKnown points (terminalPrivateCache data original A out oldPrivate root p) := by
  unfold terminalPrivateCache ComponentPhysical.patchCache
  split
  · apply closed_private_known data.pending data.visited data.frames (originalGaps data original)
      (equalizerSuffixCache data original) points _ A out hout _ p
    intro s q j parent hp
    exact ((hknown _).table (q,j)).2 parent (List.mem_append_right _ hp)
  · exact hold root p
end EnvyFreeResearch.Full.Chores.Outer
