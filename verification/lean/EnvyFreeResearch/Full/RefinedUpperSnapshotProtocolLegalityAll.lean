import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolLegalityAllHistory
import EnvyFreeResearch.Full.UpperQueryLegality

/-! Genuine Option-oracle execution of the whole actual Snapshot program on
every tape. All grid, rejected candidate, Repair, and margin-check histories
are retained and every attempted request is legal at its actual history. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open IntervalOracle UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperQueryPrograms Chores.QueryProgram UpperQueryLegality
variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (cutter : Fin k)
include hinj hgood hpositive

theorem snapshot_option_executes
    (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle) (tape : Tape n k) :
    ∃ trace, Executes oracle (snapshotProgram hk chores active origin cutter tape) origin.history
      (snapshotExecute (AdaptiveOracle.answer oracle) hk chores active origin cutter tape) trace ∧
      (snapshotExecute (AdaptiveOracle.answer oracle) hk chores active origin cutter tape).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 12*n*RefinedUpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 6*RefinedUpperRepair.fine n ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧ ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  let policy := AdaptiveOracle.answer oracle
  have hpolicy := UpperQueryLegality.answer_admissible _ oracle horacle
  let testPolicy := rejectingPolicy (Chores.measureProfile μ) policy
  have htpolicy : Admissible (Chores.measureProfile μ) testPolicy := rejectingPolicy_admissible _ policy hpolicy
  obtain ⟨testTrace,he,hh,_,_⟩ := snapshot_program_cost testPolicy hk chores active hinj origin cutter tape
  have htruth := snapshot_history_truthful μ testPolicy htpolicy hk chores active hinj origin hgood hpositive cutter tape
  rw [hh] at htruth
  have hnew : ∀ entry ∈ testTrace, ValidReply (Chores.measureProfile μ) entry.1 entry.2 :=
    fun entry he => htruth entry (List.mem_append_right _ he)
  obtain ⟨hreplay,hlegal⟩ := truthful_replay (Chores.measureProfile μ) policy he hnew
  obtain ⟨trace,hrun,hfinal,hq,hc⟩ := snapshot_program_cost policy hk chores active hinj origin cutter tape
  have heq := hreplay.deterministic hrun
  have hall : ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧
      ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
    intro entry he
    rw [← heq.2] at he
    exact ⟨hlegal entry he,hnew entry he⟩
  exact ⟨trace,option_replay _ oracle horacle hrun (fun entry hm => (hall entry hm).1),hfinal,hq,hc,hall⟩

theorem snapshot_option_run
    (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle) (tape : Tape n k) :
    ∃ trace, AdaptiveOracle.run (snapshotProgram hk chores active origin cutter tape).protocol
      (fun history => oracle (origin.history++history)) () (12*n*RefinedUpperRepair.fine n) [] =
        ⟨trace,.returned (snapshotExecute (AdaptiveOracle.answer oracle) hk chores active origin cutter tape)⟩ ∧
      (snapshotExecute (AdaptiveOracle.answer oracle) hk chores active origin cutter tape).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 12*n*RefinedUpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 6*RefinedUpperRepair.fine n ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧ ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  obtain ⟨trace,he,hh,hq,hc,hl⟩ := snapshot_option_executes μ hk chores active hinj origin hgood hpositive cutter oracle horacle tape
  exact ⟨trace,compiled_from_prior oracle he _ hq,hh,hq,hc,hl⟩

end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
