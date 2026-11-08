import EnvyFreeResearch.Full.UpperGlobalProtocolCorrectness
import EnvyFreeResearch.Full.UpperGlobalProtocolExecution
import EnvyFreeResearch.Full.UpperQueryLegality

/-! Every actual global step is an ordinary legal query program. The proof
uses the all-tape physical invariant and retains the full rejected history. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperGlobalTape UpperQueryPrograms Chores.QueryProgram
open UpperEndpointCache UpperQueryLegality IntervalOracle
variable {n : ℕ}
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)

theorem Phase.Valid.history_truthful (phase : Phase n) (hv : phase.Valid μ chores whole) :
    Truthful μ phase.history := by
  cases phase with
  | normalize a => exact hv.1.1.residue_wellFormed.2.2.1
  | snapshot a => exact hv.1.1.residue_wellFormed.2.2.1
  | firstShrink p G => exact hv.physical.buffer_wf.2.2.1
  | secondShrink p => exact hv.physical.buffer_wf.2.2.1
  | finalRepair p => exact hv.physical.buffer_wf.2.2.1
  | done a => exact hv.1.1.residue_wellFormed.2.2.1

theorem step_all_attempts (phase : Phase n) (hv : phase.Valid μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (fallback : Fin n) (draw : Universal n) :
    ∃ trace, Executes (totalPolicy policy) (phase.stepProgram fallback chores draw) phase.history
      (phase.step policy fallback chores draw) trace ∧
      (phase.step policy fallback chores draw).history=phase.history++trace ∧
      trace.length ≤ phase.queryCap ∧ (trace.map Prod.fst).countP isCut ≤ phase.cutCap ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧
        ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  let testPolicy := rejectingPolicy (Chores.measureProfile μ) policy
  have ht := rejectingPolicy_admissible (Chores.measureProfile μ) policy hpolicy
  obtain ⟨testTrace,he,hh,_,_⟩ := step_executes μ whole chores phase hv testPolicy fallback draw
  have hnext := step_valid μ whole chores phase hv testPolicy ht fallback draw
  have htruth := Phase.Valid.history_truthful μ whole chores _ hnext
  rw [hh] at htruth
  have hnew : ∀ entry ∈ testTrace, ValidReply (Chores.measureProfile μ) entry.1 entry.2 :=
    fun entry he => htruth entry (List.mem_append_right _ he)
  obtain ⟨hreplay,hlegal⟩ := truthful_replay (Chores.measureProfile μ) policy he hnew
  obtain ⟨trace,hrun,hfinal,hq,hc⟩ := step_executes μ whole chores phase hv policy fallback draw
  have heq := hreplay.deterministic hrun
  refine ⟨trace,hrun,hfinal,hq,hc,?_⟩
  intro entry he
  rw [←heq.2] at he
  exact ⟨hlegal entry he,hnew entry he⟩

theorem step_option_executes (phase : Phase n) (hv : phase.Valid μ chores whole)
    (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (fallback : Fin n) (draw : Universal n) :
    ∃ trace, Executes oracle (phase.stepProgram fallback chores draw) phase.history
      (phase.step (AdaptiveOracle.answer oracle) fallback chores draw) trace ∧
      (phase.step (AdaptiveOracle.answer oracle) fallback chores draw).history=phase.history++trace ∧
      trace.length ≤ phase.queryCap ∧ (trace.map Prod.fst).countP isCut ≤ phase.cutCap ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧
        ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  obtain ⟨tr,he,hh,hq,hc,hl⟩ := step_all_attempts μ whole chores phase hv (AdaptiveOracle.answer oracle)
    (answer_admissible _ oracle horacle) fallback draw
  exact ⟨tr,option_replay _ oracle horacle he (fun entry he => (hl entry he).1),hh,hq,hc,hl⟩

end EnvyFreeResearch.Full.UpperGlobalPhysical
