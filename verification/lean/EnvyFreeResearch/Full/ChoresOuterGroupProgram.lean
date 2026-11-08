import EnvyFreeResearch.Full.ChoresOuterCohorts

/-! Each reserved cohort executes the actual compensation program against
its restricted old state. Success and the common per-group query ledger
are derived from the committed state's physical invariants. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open Scheduler Components ChoreComposition
open scoped Classical

variable {n : ℕ} {RootId : Type*} (data : Data n RootId)
  (hall : data.pending.partition.labels ⊆ data.pending.pending)
  (cycle : ProposalCycle (data.pending.outgoing hall))

instance (group : Cohort data hall cycle) : Nonempty (Fin (group.state data hall cycle).size) :=
  inferInstanceAs (Nonempty (Fin group.roots.length))

abbrev Cohort.RunResult (group : Cohort data hall cycle) :=
  ComponentBatch.Result (group.state data hall cycle).pending (group.all_pending data hall cycle)
    (group.recordedCycle data hall cycle)

def Cohort.package (original : RootId → Snapshot.Output n) (group : Cohort data hall cycle)
    (out : group.RunResult data hall cycle) : Package (Fin n) RootId :=
  openPackage (group.state data hall cycle) original (group.all_pending data hall cycle)
    (group.recordedCycle data hall cycle) (group.more_roots data hall cycle) out

def Cohort.program (original : RootId → Snapshot.Output n) (group : Cohort data hall cycle) :
    Program (Query (Fin n)) ℝ (Option (group.RunResult data hall cycle)) :=
  (openGroup (group.state data hall cycle) original (group.all_pending data hall cycle)
    (group.recordedCycle data hall cycle) (group.more_roots data hall cycle)).bind
    (fun result => .returned (result.map Prod.fst))

def Cohort.ResultCorrect (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (original : RootId → Snapshot.Output n) (group : Cohort data hall cycle)
    (out : group.RunResult data hall cycle) : Prop :=
  (group.package data hall cycle original out).Valid ∧
    SubCoreEntry.PhysicalCorrect
      (SubCoreEntry.clippedUtility cost
        (ComponentPayments.domains (offeredBlocks (group.state data hall cycle) original)
          data.pending.partition.representative)
        (ComponentPayments.offsets (originalGaps (group.state data hall cycle) original)
          data.pending.partition.representative)) Subtype.val out.allocation ∧
    ComponentRecording.PartsCorrect cost
      (ComponentPayments.domains (offeredBlocks (group.state data hall cycle) original)
        data.pending.partition.representative) Subtype.val out ∧
    Masked.CacheCorrect (measureProfile cost)
      (ComponentPayments.domains (offeredBlocks (group.state data hall cycle) original)
        data.pending.partition.representative) out.cache

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
  (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (xs.get (index root)))
  (R : Set ℝ) (H : ℝ)
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (good : data.Good (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H)

include hsound hsep hr hH hscale good

theorem cohort_executes (group : Cohort data hall cycle)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : group.RunResult data hall cycle, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (group.program data hall cycle (fun root => xs.get (index root))) prior (some out) trace ∧
      group.ResultCorrect data hall cycle cost (fun root => xs.get (index root)) out ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card (ComponentBatch.Task data.pending hall cycle)) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ SubCore.sourceBudget (Fintype.card (ComponentBatch.Task data.pending hall cycle)) := by
  have hg := filter_good data (fun root => xs.get (index root)) cost (fun i => (cost i).real R) H
    good group.roots group.nodup
  obtain ⟨out,trace,hexec,hvalid,hcorrect,hparts,hQ,hC,hcache⟩ :=
    open_group_executes (group.state data hall cycle) (group.all_pending data hall cycle)
      (group.recordedCycle data hall cycle) (group.more_roots data hall cycle)
      cost xs index c hsound R H hsep hr hH hscale hg oracle hpolicy prior
  refine ⟨out,trace,?_,⟨hvalid,hcorrect,hparts,hcache⟩,?_,?_⟩
  · simpa only [Cohort.program,List.append_nil,Option.map_some] using
      hexec.bind (fun result => Program.returned (result.map Prod.fst))
        (Executes.returned _ (prior++trace))
  · simpa only [group.task_card] using hQ
  · simpa only [group.task_card] using hC

end EnvyFreeResearch.Full.Chores.Outer
