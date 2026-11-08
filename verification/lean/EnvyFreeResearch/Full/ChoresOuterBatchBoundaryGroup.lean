import EnvyFreeResearch.Full.ChoresOuterBatchProgram
import EnvyFreeResearch.Full.ChoresOuterBoundarySnapshot
import EnvyFreeResearch.Full.ChoresComponentBoundaryRecorded

/-! Boundary provenance for actual old-pool cohort executions. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Scheduler Components ChoreComposition Boundary SubCoreEntry Persistent Suffix SubCorePhysical
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (points : Set ℝ) (hknown : ∀ root, SnapshotKnown points (xs.get (index root)))
  (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
include hknown

theorem offered_masked_known (data : Data n RootId) :
    MaskedCacheKnown points (offeredMaskedCache data (fun root => xs.get (index root))) := by
  intro s i parent hp
  exact ((hknown (data.source s)).table _).2 parent (List.mem_append_right _ hp)

include hsound hzero hone

theorem open_group_known (data : Data n RootId) [Nonempty (Fin data.size)]
    (hall : data.pending.partition.labels ⊆ data.pending.pending)
    (cycle : ProposalCycle (data.pending.outgoing hall))
    (hmany : Fintype.card (ComponentBatch.Task data.pending hall cycle) < Fintype.card (Fin data.size))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ)
    (out : ComponentBatch.Result data.pending hall cycle) (package : Package (Fin n) RootId)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (openGroup data (fun root => xs.get (index root)) hall cycle hmany)
      prior (some (out,package)) trace) :
    RecordedKnown ClippedRecord.record (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨source,first,second,hfirst,hsecond,htrace⟩ := Executes.split_bind _ _ h
  cases source with
  | none => cases hsecond
  | some result =>
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    apply clipped_recorded_known cost
      (ComponentPayments.domains (offeredBlocks data (fun root => xs.get (index root)))
        data.pending.partition.representative)
      (offeredMaskedCache data (fun root => xs.get (index root)))
      (offered_masked_cache cost xs index c hsound data) Subtype.val
      (ComponentPayments.offsets (originalGaps data (fun root => xs.get (index root)))
        data.pending.partition.representative) _
      (ComponentBatch.task_positive data.pending hall cycle) hmany oracle hpolicy
      points (offered_masked_known xs index points hknown data) hzero hone prior out first hfirst
    intro s i
    obtain ⟨U,hs⟩ := hsound (data.source s)
    exact Clearance.gap_nonnegative hs i _

theorem cohort_known (data : Data n RootId)
    (hall : data.pending.partition.labels ⊆ data.pending.pending)
    (cycle : ProposalCycle (data.pending.outgoing hall)) (group : Cohort data hall cycle)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) (out : group.RunResult data hall cycle)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (group.program data hall cycle (fun root => xs.get (index root)))
      prior (some out) trace) :
    RecordedKnown ClippedRecord.record (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨source,first,second,hfirst,hsecond,htrace⟩ := Executes.split_bind _ _ h
  cases source with
  | none => cases hsecond
  | some pair =>
    rcases pair with ⟨result,package⟩
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    exact open_group_known cost xs index c hsound points hknown hzero hone
      (group.state data hall cycle) (group.all_pending data hall cycle)
      (group.recordedCycle data hall cycle) (group.more_roots data hall cycle)
      oracle hpolicy prior result package first hfirst
end EnvyFreeResearch.Full.Chores.Outer
