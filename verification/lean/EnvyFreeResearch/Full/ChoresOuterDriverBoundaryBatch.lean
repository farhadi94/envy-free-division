import EnvyFreeResearch.Full.ChoresOuterDriverBoundaryState
import EnvyFreeResearch.Full.ChoresOuterBatchBoundaryCache
import EnvyFreeResearch.Full.ChoresOuterBatchCommit

/-! The actual batch execution followed by its free simultaneous commit
preserves the scheduler boundary invariant at the complete returned history. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Scheduler Components ChoreComposition Boundary SubCoreEntry Persistent Suffix
open scoped Classical
variable {n : ℕ} {RootId : Type*}

theorem commit_batch_known (data : Data n RootId)
    (hall : data.pending.partition.labels ⊆ data.pending.pending)
    (cycle : ProposalCycle (data.pending.outgoing hall))
    (original : RootId → Snapshot.Output n) (outputs : List (GroupResult data hall cycle))
    (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)
    (points : Set ℝ) (hold : DataKnown points original data)
    (hout : ∀ out ∈ outputs, RecordedKnown ClippedRecord.record points out.result) :
    DataKnown points original (commitBatch data hall cycle original outputs keep hk) :=
  ⟨hold.snapshots,batch_cache_known data hall cycle original points hold.snapshots outputs hout hold.cache⟩

theorem executed_batch_known [Fintype RootId]
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
    (data : Data n RootId)
    (hall : data.pending.partition.labels ⊆ data.pending.pending)
    (cycle : ProposalCycle (data.pending.outgoing hall))
    (groups : List (Cohort data hall cycle)) (outputs : List (GroupResult data hall cycle))
    (keep : Fin n) (hk : keep ∈ data.pending.selected hall cycle)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (points : Set ℝ) (hold : DataKnown points (fun root => xs.get (index root)) data)
    (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (prior trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (batchProgram data hall cycle (fun root => xs.get (index root)) groups)
      prior (some outputs) trace) :
    DataKnown (Known points trace) (fun root => xs.get (index root))
      (commitBatch data hall cycle (fun root => xs.get (index root)) outputs keep hk) ∧
      Scoped points trace := by
  obtain ⟨hout,hscope⟩ := batch_known cost xs index c hsound data hall cycle groups oracle hpolicy
    points hold.snapshots hzero hone prior outputs trace h
  exact ⟨commit_batch_known data hall cycle _ outputs keep hk _
    (hold.mono subset_union_left) hout,hscope⟩
end EnvyFreeResearch.Full.Chores.Outer
