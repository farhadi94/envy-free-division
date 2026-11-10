import EnvyFreeResearch.Full.RefinedUpperBatchLoop
import EnvyFreeResearch.Full.UpperCorrectionLoopProgramMeasurable

/-! Borel next actions for the actual finite rejection-and-retry executor. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperRepairBatchCertified
open UpperCircularStage UpperCorrectionExecution UpperCorrectionLoop UpperQueryPrograms
  Chores.QueryProgram ProgramMeasurable UpperStageMeasurable UpperProgramIterationMeasurable
  RefinedUpperCorrectionRetries RefinedUpperBatchLoop
variable {n r k : ℕ} {X : Type} [MeasurableSpace X]

theorem attempt_certified (state : X → RetryState n) (draw : X → Job n × UpperCircular.Circle)
    (hs : Measurable state) (hd : Measurable draw) :
    Certified (fun x => attemptProgram (state x) (draw x)) := by
  have hb : Measurable (fun x => (state x).1 || (state x).2.stopped) :=
    (measurable_of_countable (fun b : Bool × Bool => b.1 || b.2)).comp
      ((measurable_fst.comp hs).prodMk (loop_stopped_measurable.comp (measurable_snd.comp hs)))
  have hbase := UpperCorrectionLoopProgramMeasurable.stepProgram_certified _ draw (measurable_snd.comp hs) hd
  have htail := hbase.bind (fun z => .returned (update z.2))
    (Certified.returned _ (update_measurable.comp measurable_snd))
  exact Certified.branch _ hb _ _ (Certified.returned _ (measurable_const.prodMk hs)) htail

theorem retry_certified (job : X → Job n) (state : X → LoopState n)
    (tape : X → Fin r → UpperCircular.Circle) (hj : Measurable job) (hs : Measurable state)
    (ht : ∀ a, Measurable (fun x => tape x a)) :
    Certified (fun x => retryProgram (job x) (state x) (tape x)) := by
  have hstep : Certified (fun z : Unit × RetryState n × (Job n × UpperCircular.Circle) => attemptProgram z.2.1 z.2.2) :=
    attempt_certified _ _ (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  exact runProgram_family_certified (fun _ : Unit => attemptProgram) hstep r
    (fun _ : X => ()) (fun x => (false,state x)) (fun x i => (job x,tape x i))
    measurable_const (measurable_const.prodMk hs) (fun i => hj.prodMk (ht i))

theorem transition_certified (state : X → LoopState n) (draw : X → RefinedUpperBatchLoop.Draw n r)
    (hs : Measurable state) (hd : Measurable draw) :
    Certified (fun x => transitionProgram (state x) (draw x)) := by
  have hbase := retry_certified (fun x => (draw x).1) state (fun x => (draw x).2)
    (measurable_fst.comp hd) hs (fun i => (measurable_pi_apply i).comp (measurable_snd.comp hd))
  exact hbase.bind _ (Certified.returned _
    (measurable_const.prodMk (finish_measurable.comp (measurable_snd.comp measurable_snd))))

theorem program_certified (jobs : X → Fin k → Job n) (state : X → LoopState n)
    (tape : X → Fin k → Fin r → UpperCircular.Circle)
    (hj : ∀ i, Measurable (fun x => jobs x i)) (hs : Measurable state)
    (ht : ∀ i, Measurable (fun x => tape x i)) :
    Certified (fun x => RefinedUpperBatchLoop.program (jobs x) (state x) (tape x)) := by
  have hstep : Certified (fun z : Unit × LoopState n × RefinedUpperBatchLoop.Draw n r => transitionProgram z.2.1 z.2.2) :=
    transition_certified _ _ (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  exact runProgram_family_certified (fun _ : Unit => transitionProgram) hstep k
    (fun _ : X => ()) state (fun x i => (jobs x i,tape x i)) measurable_const hs
    (fun i => (hj i).prodMk (ht i))

end EnvyFreeResearch.Full.RefinedUpperRepairBatchCertified
