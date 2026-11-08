import EnvyFreeResearch.Full.UpperShrinkExecuteMeasurableRefine
import EnvyFreeResearch.Full.UpperRepairOutputMeasurable

/-! Joint measurability of the actual prescribed carving and Shrink outputs,
for arbitrary coded inputs and full-history measurable response policies. -/
noncomputable section
open MeasureTheory
namespace EnvyFreeResearch.Full.UpperShrinkCarve
open UpperCorrectionExecution UpperCircularStage ProtocolMeasurable UpperStageMeasurable
variable {n k : ℕ}

theorem roundsExecute_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (J : ℕ) :
    ∀ {X : Type} [MeasurableSpace X] (normal : X → Fin k → ℝ) (mesh : X → Mesh n k),
      Measurable normal → Measurable mesh →
      Measurable (fun x => roundsExecute policy active (normal x) J (mesh x)) := by
  induction J with
  | zero =>
    intro X _ normal mesh hn hm
    exact (floated_measurable active).comp (hn.prodMk hm)
  | succ J ih =>
    intro X _ normal mesh hn hm
    have hready := (floated_measurable active).comp (hn.prodMk hm)
    exact ih normal _ hn (refinePiecesExecute_measurable policy hmeas active _ _
      (mesh_pieces_measurable.comp hready) (mesh_history_measurable.comp hready))

end EnvyFreeResearch.Full.UpperShrinkCarve

namespace EnvyFreeResearch.Full.UpperShrink
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
    (roundsExecute_measurable policy hmeas active (UpperShrinkPrecision.depth n k) _ _ hn
      (initial_measurable origin _ ho hf))

theorem execute_measurable [Nonempty (Fin k)] (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : X → State n) (G : X → ℝ) (tape : X → UpperRepair.Tape n k)
    (ho : Measurable origin) (hG : Measurable G) (ht : Measurable tape) :
    Measurable (fun x => execute policy hk chores active (origin x) (G x) (tape x)) := by
  have hc := carvingExecute_measurable policy hmeas active origin G ho hG
  exact UpperRepairOutputMeasurable.execute_measurable policy hmeas hk chores active
    (fun x => (carvingExecute policy active (origin x) (G x)).buffer)
    (fun x => (carvingExecute policy active (origin x) (G x)).old)
    (UpperRepair.coarse n) (UpperRepair.fine n) (UpperRepair.repeats n) (UpperRepair.reserveMark n)
    (UpperRepair.cutoff n) (UpperRepair.cellBound n) (UpperRepair.gapMultiplier n) tape
    (carved_buffer_measurable.comp hc) (fun j => (carved_old_measurable j).comp hc) ht

end EnvyFreeResearch.Full.UpperShrink
