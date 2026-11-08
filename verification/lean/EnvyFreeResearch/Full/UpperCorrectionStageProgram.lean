import EnvyFreeResearch.Full.UpperCorrectionOutputMeasurable
import EnvyFreeResearch.Full.UpperCorrectionLoopProgram

/-! Ordinary-query program for the complete correction stage and output
postprocessing. Every rejecting attempt remains charged in the trace. -/

noncomputable section

open MeasureTheory
open scoped Classical

namespace EnvyFreeResearch.Full.UpperCorrectionStageProgram

open UpperRecordedDomain UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionSetup
  UpperCorrectionAccepted UpperCorrectionOutcome UpperCorrectionPieces UpperQueryPrograms
  UpperCircularStage Chores.QueryProgram UpperStageMeasurable

variable {n k m : ℕ} [Nonempty (Fin k)]

abbrev Result (n k : ℕ) := (Fin k → List Component) × State n × Bool

def finish (active : Fin k → Fin n) (reserve : State n) (cuts : Fin (m + 2) → ℝ)
    (t : Fin k → ℝ) (eta : ℝ) (final : LoopState n) : Result n k :=
  let paid := payments (startState active reserve cuts t eta).current.cells final.accepted
  ((fun j => wholeAtoms active reserve cuts t eta j ++ paid[j.val]?.getD []), final.current, final.stopped)

def program (active : Fin k → Fin n) (reserve : State n) (cuts : Fin (m + 2) → ℝ)
    (t : Fin k → ℝ) (eta lam : ℝ) (tape : Fin k → UpperCircular.Circle) : QProgram n (Result n k) :=
  (UpperCorrectionLoopProgram.loopProgram (tasks active reserve cuts t eta lam)
    (startState active reserve cuts t eta) tape).bind
      (fun result => .returned (finish active reserve cuts t eta result.2))

def executeStage (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (tape : Fin k → UpperCircular.Circle) : Result n k :=
  finish active reserve cuts t eta (run policy (tasks active reserve cuts t eta lam)
    (startState active reserve cuts t eta) tape).2

theorem executeStage_output (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (tape : Fin k → UpperCircular.Circle) :
    (executeStage policy active reserve cuts t eta lam tape).1 = output policy active reserve cuts t eta lam tape := rfl

/-- The complete raw-unit correction stage is an ordinary input-independent
query program. Finite output reconstruction issues no oracle calls. -/
theorem program_executes (policy : Policy n) (active : Fin k → Fin n) (reserve : State n)
    (cuts : Fin (m + 2) → ℝ) (t : Fin k → ℝ) (eta lam : ℝ) (tape : Fin k → UpperCircular.Circle) :
    ∃ trace, Executes (totalPolicy policy) (program active reserve cuts t eta lam tape) reserve.history
      (executeStage policy active reserve cuts t eta lam tape) trace ∧
      (executeStage policy active reserve cuts t eta lam tape).2.1.history = reserve.history ++ trace ∧
      trace.length ≤ k * (2 * (n + 1)) ∧ (trace.map Prod.fst).countP isCut ≤ k * 2 := by
  obtain ⟨trace, hrun, heq, hq, hc⟩ := UpperCorrectionLoopProgram.loopProgram_executes_bounded policy
    (tasks active reserve cuts t eta lam) (startState active reserve cuts t eta) tape
  refine ⟨trace, ?_, heq, hq, hc⟩
  have h := hrun.bind (fun result => Program.returned (finish active reserve cuts t eta result.2))
    (Executes.returned (executeStage policy active reserve cuts t eta lam tape) (reserve.history ++ trace))
  simpa only [program, List.append_nil, startState, initial, UpperPendingExclusion.remove] using h

/-- Joint execution/output measurability follows from the concrete real
cache and fresh-tape computations. A compiled next-action Borel proof is a
separate obligation. -/
theorem executeStage_measurable {X : Type*} [MeasurableSpace X]
    (policy : Policy n) (hpolicy : MeasurablePolicy policy)
    (active : Fin k → Fin n) (reserve : X → State n) (cuts : X → Fin (m + 2) → ℝ)
    (t : X → Fin k → ℝ) (eta lam : X → ℝ) (tape : X → Fin k → UpperCircular.Circle)
    (hreserve : Measurable reserve) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (ht : ∀ j, Measurable (fun z => t z j)) (heta : Measurable eta) (hlam : Measurable lam)
    (htape : ∀ j, Measurable (fun z => tape z j)) :
    Measurable (fun z => executeStage policy active (reserve z) (cuts z) (t z) (eta z) (lam z) (tape z)) := by
  have hstart := startState_measurable active reserve cuts t eta hreserve hcuts ht heta
  have hjobs := tasks_measurable active reserve cuts t eta lam hreserve hcuts ht heta hlam
  have hrun := UpperCorrectionOutputMeasurable.run_measurable policy hpolicy _ _ tape
    (fun j => (measurable_pi_apply j).comp hjobs) hstart htape
  exact (UpperCorrectionOutputMeasurable.output_measurable policy hpolicy active reserve cuts t eta lam tape
    hreserve hcuts ht heta hlam htape).prodMk
      ((loop_current_measurable.comp (measurable_snd.comp hrun)).prodMk
        (loop_stopped_measurable.comp (measurable_snd.comp hrun)))

end EnvyFreeResearch.Full.UpperCorrectionStageProgram
