import EnvyFreeResearch.Full.UpperCorrectionProgramMeasurable
import EnvyFreeResearch.Full.UpperProgramIterationMeasurable
import EnvyFreeResearch.Full.UpperCorrectionLoopProgram

/-! Borel certification of the actual stopped correction program. Rejection
restores material while preserving every answer already recorded. -/

noncomputable section

open MeasureTheory
open scoped Classical

namespace EnvyFreeResearch.Full.UpperCorrectionLoopProgramMeasurable

open Chores.QueryProgram ProgramMeasurable ProtocolMeasurable UpperQueryPrograms
  UpperCircularStage UpperDomainDifference UpperCorrectionExecution UpperCorrectionLoop
  UpperCorrectionProgramMeasurable UpperCorrectionLoopProgram UpperProgramIterationMeasurable

abbrev Circle := UpperCircular.Circle

variable {n m : ℕ} {X : Type} [MeasurableSpace X]

theorem stepProgram_certified (state : X → LoopState n) (draw : X → Job n × Circle)
    (hstate : Measurable state) (hdraw : Measurable draw) :
    Certified (fun x => stepProgram (state x) (draw x)) := by
  have hcurrent := loop_current_measurable.comp hstate
  have hjob := measurable_fst.comp hdraw
  have hcorrect := correction_certified _ _ _ _ hcurrent (job_owner_measurable.comp hjob)
    (job_deficit_measurable.comp hjob) (measurable_snd.comp hdraw)
  let Y := X × (Correction × State n)
  have haccept : Measurable (fun z : Y => accepts (draw z.1).1 (state z.1).current z.2.2) :=
    accepts_measurable _ _ _ (hjob.comp measurable_fst) (hcurrent.comp measurable_fst)
      (measurable_snd.comp measurable_snd)
  have haccepted := loop_accepted_measurable.comp (hstate.comp (measurable_fst : Measurable (Prod.fst : Y → X)))
  have hcommit : Measurable (fun z : Y =>
      (false, (⟨z.2.2, false, (state z.1).accepted ++ [z.2.1]⟩ : LoopState n))) :=
    measurable_const.prodMk (loop_mk_measurable _ _ _ (measurable_snd.comp measurable_snd)
      measurable_const (measurable_list_append.comp (haccepted.prodMk
        (measurable_list_singleton.comp (measurable_fst.comp measurable_snd)))))
  have hrestore : Measurable (fun z : Y =>
      (⟨(state z.1).current.cells, z.2.2.history⟩ : State n)) := by
    apply measurable_comap_iff.mpr
    change Measurable (fun z : Y => ((state z.1).current.cells, z.2.2.history))
    exact (state_cells_measurable.comp (hcurrent.comp measurable_fst)).prodMk
      (state_history_measurable.comp (measurable_snd.comp measurable_snd))
  have habort : Measurable (fun z : Y =>
      (true, (⟨⟨(state z.1).current.cells, z.2.2.history⟩, true, (state z.1).accepted⟩ : LoopState n))) :=
    measurable_const.prodMk (loop_mk_measurable _ _ _ hrestore measurable_const haccepted)
  have htail := Certified.branch (Query := Query n) (Reply := ℝ) _ haccept _ _
    (Certified.returned _ hcommit) (Certified.returned _ habort)
  have hopen := hcorrect.bind _ htail
  exact Certified.branch _ (loop_stopped_measurable.comp hstate) _ _
    (Certified.returned _ (measurable_const.prodMk hstate)) hopen

theorem loopProgram_certified (jobs : X → Fin m → Job n) (state : X → LoopState n)
    (tape : X → Fin m → Circle) (hjobs : ∀ i, Measurable (fun x => jobs x i))
    (hstate : Measurable state) (htape : ∀ i, Measurable (fun x => tape x i)) :
    Certified (fun x => loopProgram (jobs x) (state x) (tape x)) := by
  have hstep : Certified (fun z : Unit × LoopState n × (Job n × Circle) => stepProgram z.2.1 z.2.2) :=
    stepProgram_certified _ _ (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  exact runProgram_family_certified (fun _ : Unit => stepProgram) hstep m
    (fun _ : X => ()) state (fun x i => (jobs x i, tape x i)) measurable_const hstate
    (fun i => (hjobs i).prodMk (htape i))

end EnvyFreeResearch.Full.UpperCorrectionLoopProgramMeasurable
