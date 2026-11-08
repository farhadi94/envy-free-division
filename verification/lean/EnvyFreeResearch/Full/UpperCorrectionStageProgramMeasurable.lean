import EnvyFreeResearch.Full.UpperCorrectionLoopProgramMeasurable
import EnvyFreeResearch.Full.UpperCorrectionStageProgram

/-! Borel certification through physical correction output reconstruction. -/

noncomputable section

open MeasureTheory
open scoped Classical

namespace EnvyFreeResearch.Full.UpperCorrectionStageProgramMeasurable

open Chores.QueryProgram ProgramMeasurable ProtocolMeasurable UpperRecordedDomain
  UpperCorrectionExecution UpperCorrectionLoop UpperCorrectionSetup UpperCorrectionAccepted
  UpperCorrectionPieces UpperCorrectionOutcome UpperCorrectionOutputMeasurable
  UpperCorrectionLoopProgramMeasurable UpperCorrectionStageProgram

variable {n k m : ℕ} [Nonempty (Fin k)] {X : Type} [MeasurableSpace X]

theorem finish_measurable (active : Fin k → Fin n) (reserve : X → State n)
    (cuts : X → Fin (m + 2) → ℝ) (t : X → Fin k → ℝ) (eta : X → ℝ) (final : X → LoopState n)
    (hreserve : Measurable reserve) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (ht : ∀ j, Measurable (fun z => t z j)) (heta : Measurable eta) (hfinal : Measurable final) :
    Measurable (fun z => finish active (reserve z) (cuts z) (t z) (eta z) (final z)) := by
  have hstart := startState_measurable active reserve cuts t eta hreserve hcuts ht heta
  have hpaid := payments_measurable _ _
    (state_cells_measurable.comp (loop_current_measurable.comp hstart))
    (loop_accepted_measurable.comp hfinal)
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro j
    exact measurable_list_append.comp
      ((wholeAtoms_measurable active reserve cuts t eta hreserve hcuts ht heta j).prodMk
        (getD_measurable _ ((measurable_list_getElem j.val).comp hpaid) []))
  · exact (loop_current_measurable.comp hfinal).prodMk (loop_stopped_measurable.comp hfinal)

theorem program_certified (active : Fin k → Fin n) (reserve : X → State n)
    (cuts : X → Fin (m + 2) → ℝ) (t : X → Fin k → ℝ) (eta lam : X → ℝ)
    (tape : X → Fin k → UpperCircular.Circle)
    (hreserve : Measurable reserve) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (ht : ∀ j, Measurable (fun z => t z j)) (heta : Measurable eta) (hlam : Measurable lam)
    (htape : ∀ j, Measurable (fun z => tape z j)) :
    Certified (fun z => program active (reserve z) (cuts z) (t z) (eta z) (lam z) (tape z)) := by
  have hstart := startState_measurable active reserve cuts t eta hreserve hcuts ht heta
  have hjobs := tasks_measurable active reserve cuts t eta lam hreserve hcuts ht heta hlam
  have hloop := loopProgram_certified _ _ tape
    (fun j => (measurable_pi_apply j).comp hjobs) hstart htape
  have hfinish : Measurable (fun z : X × ((Fin k → Bool) × LoopState n) =>
      finish active (reserve z.1) (cuts z.1) (t z.1) (eta z.1) z.2.2) :=
    finish_measurable active _ _ _ _ _ (hreserve.comp measurable_fst)
      (fun e => (hcuts e).comp measurable_fst) (fun j => (ht j).comp measurable_fst)
      (heta.comp measurable_fst) (measurable_snd.comp measurable_snd)
  exact hloop.bind _ (Certified.returned _ hfinish)

end EnvyFreeResearch.Full.UpperCorrectionStageProgramMeasurable
