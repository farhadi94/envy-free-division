import EnvyFreeResearch.Full.RefinedUpperShrinkCertified
import EnvyFreeResearch.Full.UpperShrinkExecuteMeasurable

/-! Joint measurability of the actual refined Shrink executor, including
its deterministic carve and new full-history Repair tape. -/
noncomputable section
open MeasureTheory
namespace EnvyFreeResearch.Full.RefinedUpperShrink
open UpperShrink
open UpperCorrectionExecution UpperCircularStage UpperDomainDifference UpperShrinkCarve ProtocolMeasurable UpperStageMeasurable
variable {n k : ℕ} {X : Type} [MeasurableSpace X]

theorem carvingExecute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : X → State n) (G : X → ℝ)
    (ho : Measurable origin) (hG : Measurable G) :
    Measurable (fun x => carvingExecute policy active (origin x) (G x)) := by
  have hn : Measurable (fun x => fun i => total (origin x) (active i)) :=
    Measurable.of_eval (fun i => total_measurable origin (fun _ => active i) ho measurable_const)
  have hf : Measurable (fun x => fraction k (G x)) := by
    unfold fraction
    fun_prop
  exact meshCarve_measurable.comp
    (roundsExecute_measurable policy hmeas active (RefinedUpperShrinkPrecision.depth n k) _ _ hn
      (initial_measurable origin _ ho hf))

theorem execute_measurable [Nonempty (Fin k)] (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (G : X → ℝ) (tape : X → RefinedUpperRepair.Tape n k)
    (ho : Measurable origin) (hG : Measurable G) (ht : Measurable tape) :
    Measurable (fun x => execute policy hk chores active (origin x) (G x) (tape x)) := by
  have hc := carvingExecute_measurable policy hmeas active origin G ho hG
  exact RefinedUpperRepair.execute_measurable policy hmeas hk chores active
    (fun x => (carvingExecute policy active (origin x) (G x)).buffer)
    (fun x => (carvingExecute policy active (origin x) (G x)).old) tape
    (carved_buffer_measurable.comp hc) (fun j => (carved_old_measurable j).comp hc) ht

end EnvyFreeResearch.Full.RefinedUpperShrink
