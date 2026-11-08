import EnvyFreeResearch.Full.UpperShrinkCarveMeasurableRounds
import EnvyFreeResearch.Full.UpperShrinkProtocol

/-! Borel query-program certificates for the prescribed carving algorithm and
the full Shrink attempt. These hold on all coded histories, without physical
validity assumptions. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrink
open UpperCorrectionExecution UpperRecordedDomain UpperCircularStage UpperDomainDifference
  UpperQueryPrograms ProgramMeasurable ProtocolMeasurable Chores.QueryProgram UpperShrinkCarve
variable {n k : ℕ}

theorem carved_old_measurable (j : Fin k) :
    Measurable (fun out : Carved n k => out.old j) :=
  (measurable_pi_apply j).comp (measurable_fst.comp (comap_measurable carvedCode))

theorem carved_buffer_measurable :
    Measurable (fun out : Carved n k => out.buffer) :=
  measurable_snd.comp (comap_measurable carvedCode)

theorem carvingProgram_certified {X : Type} [MeasurableSpace X]
    (active : Fin k → Fin n) (origin : X → State n) (G : X → ℝ)
    (ho : Measurable origin) (hG : Measurable G) :
    Certified (fun x => carvingProgram active (origin x) (G x)) := by
  have hn : Measurable (fun x => fun i => total (origin x) (active i)) :=
    Measurable.of_eval (fun i => total_measurable origin (fun _ => active i) ho measurable_const)
  have hf : Measurable (fun x => fraction k (G x)) := by
    unfold fraction
    fun_prop
  exact rounds_assembled_certified active _ _ (fun _ => UpperShrinkPrecision.depth n k)
    hn (initial_measurable origin _ ho hf) measurable_const

theorem program_certified {X : Type} [MeasurableSpace X] [Nonempty (Fin k)]
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (G : X → ℝ) (p : X → UpperRepair.Tape n k)
    (ho : Measurable origin) (hG : Measurable G) (hp : Measurable p) :
    Certified (fun x => program hk chores active (origin x) (G x) (p x)) := by
  exact (carvingProgram_certified active origin G ho hG).bind _
    (UpperRepair.program_certified hk chores active
      (fun z : X × Carved n k => z.2.buffer) (fun z => z.2.old) (fun z => p z.1)
      (carved_buffer_measurable.comp measurable_snd)
      (fun j => (carved_old_measurable j).comp measurable_snd)
      (hp.comp measurable_fst))

end EnvyFreeResearch.Full.UpperShrink
