import EnvyFreeResearch.Full.RefinedChoresTerminalCohortPrivate
import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryTerminal
import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryPrivate
import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryCache

/-! Terminal cache assembly retains literal recorded endpoints in every
 donor, untouched original, and complementary slot. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.QueryProgram
open Chores.InitialPartition Chores.OrderedUnion Chores.Boundary Chores.Suffix
open Chores.ComponentRecording Chores.ComponentPayments
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H) (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)
    (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (original root))
include hknown

theorem TerminalGroup.front_known (s : group.Root) (a : Fin n) :
    CacheKnown points (TerminalGroup.front data normal original r H group s a) :=
  Outer.outcome_front_known points _ (hknown _).table a _

theorem TerminalGroup.masked_known : MaskedCacheKnown points (TerminalGroup.masked data normal original r H group) := by
  intro s i
  exact Outer.outcome_offer_known points _ (hknown _).table group.label _ ((hknown _).parents group.label) _

variable (out : Result (Root := group.Root) group.terminalClass.participants)
    (hout : RecordedKnown id points out)
include hout

theorem TerminalGroup.next_known (s : group.Root) (a : Fin n) :
    CacheKnown points (TerminalGroup.next data normal original r H group hr0 hH0 out s a) := by
  unfold TerminalGroup.next nextCache ComponentAssignment.dispatch
  split
  · unfold donorCache
    apply Outer.proposal_cache_known points
    · intro q j parent hp
      exact ((hknown _).table (q,j)).2 parent (List.mem_append_left _ hp)
    · exact TerminalGroup.front_known data normal original r H group points hknown _ _
    · intro parent hp
      exact (hout.2.2.2 _) parent (List.mem_append_left _ hp)
  · intro parent hp
    exact ((hknown _).table _).2 parent (List.mem_append_left _ hp)

theorem TerminalGroup.pool_cache_known
    (hold : ∀ root a, CacheKnown points (data.cache root a)) (root : RootId) (a : Fin n) :
    CacheKnown points (TerminalGroup.poolCache data normal original r H group hr0 hH0 out root a) := by
  change CacheKnown points (ComponentPhysical.patchCache _ _ _ root a)
  unfold ComponentPhysical.patchCache
  split
  · exact TerminalGroup.next_known data normal original r H group hr0 hH0 points hknown out hout _ a
  · exact hold root a

theorem TerminalGroup.next_private_known (s : group.Root) (a : Fin n) :
    CacheKnown points (TerminalGroup.nextPrivate data normal original r H group hr0 hH0 out s a) := by
  unfold TerminalGroup.nextPrivate ComponentAssignment.dispatch
  split
  · apply Outer.proposal_private_known points
    · intro q j parent hp
      exact ((hknown _).table (q,j)).2 parent (List.mem_append_right _ hp)
    · intro parent hp
      exact (hout.2.2.2 _) parent (List.mem_append_right _ hp)
  · intro parent hp
    exact ((hknown _).table _).2 parent (List.mem_append_right _ hp)

theorem TerminalGroup.pool_private_known
    (oldPrivate : RootId → Fin n → List (Parent n))
    (hold : ∀ root a, CacheKnown points (oldPrivate root a)) (root : RootId) (a : Fin n) :
    CacheKnown points (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate root a) := by
  unfold TerminalGroup.poolPrivate ComponentPhysical.patchCache
  split
  · exact TerminalGroup.next_private_known data normal original r H group hr0 hH0 points hknown out hout _ a
  · exact hold root a

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.pool_private_known
