import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolRepair
import EnvyFreeResearch.Full.RefinedUpperRepairLegality

/-! Genuine Option-oracle execution for the fresh Repair and cached margin
check, retaining all attempts even when the check restores the old material. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open IntervalOracle UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperRepairPreparationChecks UpperQueryPrograms Chores.QueryProgram
variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (gamma : ℝ) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (hnear : Near chores μ active origin old (RefinedUpperRepair.nearError n))
include hinj hgood hpositive hold hnear

theorem option_executes (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle) (p : RefinedUpperRepair.Tape n k) :
    ∃ trace, Executes oracle (program hk chores active gamma origin old p) origin.history
      (execute (AdaptiveOracle.answer oracle) hk chores active gamma origin old p) trace ∧
      (execute (AdaptiveOracle.answer oracle) hk chores active gamma origin old p).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 6*n*RefinedUpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 3*RefinedUpperRepair.fine n ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧
        ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  obtain ⟨trace,he,hh,hq,hc,hl⟩ := RefinedUpperRepairLegality.option_executes μ hk chores active hinj origin hgood hpositive
    old hold hnear oracle horacle p
  refine ⟨trace,?_,?_,hq,hc,hl⟩
  · simpa only [program,execute,List.append_nil] using he.bind
      (fun result => Program.returned (finish (by omega) chores active gamma origin old result))
      (Executes.returned _ _)
  · exact (finish_history _ _ _ _ _ _ _).trans hh

theorem option_run (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle) (p : RefinedUpperRepair.Tape n k) :
    ∃ trace, AdaptiveOracle.run (program hk chores active gamma origin old p).protocol
      (fun history => oracle (origin.history ++ history)) () (6*n*RefinedUpperRepair.fine n) [] =
        ⟨trace, .returned (execute (AdaptiveOracle.answer oracle) hk chores active gamma origin old p)⟩ ∧
      (execute (AdaptiveOracle.answer oracle) hk chores active gamma origin old p).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 6*n*RefinedUpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 3*RefinedUpperRepair.fine n ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧
        ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  obtain ⟨trace,he,hh,hq,hc,hl⟩ := option_executes μ hk chores active hinj gamma origin hgood hpositive old hold hnear oracle horacle p
  exact ⟨trace,UpperQueryLegality.compiled_from_prior oracle he _ hq,hh,hq,hc,hl⟩
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
