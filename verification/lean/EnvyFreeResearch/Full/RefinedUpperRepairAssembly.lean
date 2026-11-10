import EnvyFreeResearch.Full.RefinedUpperRepairTrialCertified
import EnvyFreeResearch.Full.RefinedUpperRepairFinalCache

/-! Policy-independent extraction of recorded payment lists from the actual
returned preparation and finite retry transcript. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperRepairAssembly
open UpperRecordedDomain UpperCorrectionExecution UpperCorrectionLoop UpperCircularStage
  UpperStageMeasurable UpperCorrectionPieces RefinedUpperCorrectionAccepted
  RefinedUpperPreparationProgram RefinedUpperRepairTargets RefinedUpperCorrectionSetup ProtocolMeasurable
variable {n k coarse fine : ℕ} [Nonempty (Fin k)]

def paymentCells (chores : Bool) (active : Fin k → Fin n) (p : Prepared n k coarse fine)
    (eta lam : ℝ) (s : LoopState n) (j : Fin k) : List Component :=
  wholeAtoms active p.2.1 (UpperGridData.cuts p.1) (targets chores active p eta lam) eta j ++
    (payments (startState active p.2.1 (UpperGridData.cuts p.1) (targets chores active p eta lam) eta).current.cells
      s.accepted)[j.val]?.getD []

def stage (chores : Bool) (active : Fin k → Fin n) (eta lam : ℝ)
    (result : RefinedUpperRepairTrial.Result n k coarse fine) : RefinedUpperRepairFinalCache.Result n k :=
  (paymentCells chores active result.1 eta lam result.2,result.2.current,result.2.stopped)

theorem stage_history (chores : Bool) (active : Fin k → Fin n) (eta lam : ℝ)
    (result : RefinedUpperRepairTrial.Result n k coarse fine) :
    (stage chores active eta lam result).2.1.history = result.2.current.history := rfl

theorem stage_stopped (chores : Bool) (active : Fin k → Fin n) (eta lam : ℝ)
    (result : RefinedUpperRepairTrial.Result n k coarse fine) :
    (stage chores active eta lam result).2.2 = result.2.stopped := rfl

/-- Actual execution equals the physical stage verified by the cache and
payment theorems, on all cycle-approved outcomes, including failed retries. -/
theorem stage_after {r : ℕ} (policy : Policy n) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (p : Prepared n k coarse fine) (eta lam : ℝ)
    (tape : Fin k → Fin r → UpperCircular.Circle) (ha : approved chores active p lam = true) :
    stage chores active eta lam (RefinedUpperRepairTrial.after policy chores active origin p eta lam tape) =
      RefinedUpperRepairFinalCache.executeStage policy active p.2.1 (UpperGridData.cuts p.1)
        (targets chores active p eta lam) eta lam tape := by
  simp only [RefinedUpperRepairTrial.after,ha,ite_true]
  rfl

variable {X : Type} [MeasurableSpace X]

theorem paymentCells_measurable (chores : Bool) (active : Fin k → Fin n)
    (p : X → Prepared n k coarse fine) (eta lam : ℝ) (s : X → LoopState n)
    (hp : Measurable p) (hs : Measurable s) (j : Fin k) :
    Measurable (fun x => paymentCells chores active (p x) eta lam (s x) j) := by
  have hres := measurable_fst.comp (measurable_snd.comp hp)
  have hcuts (e) := (measurable_pi_apply e).comp (UpperGridData.cuts_measurable _ (measurable_fst.comp hp))
  have ht := targets_measurable chores active p eta lam hp
  have hw := RefinedUpperCorrectionOutputMeasurable.wholeAtoms_measurable active _ _ _ (fun _ => eta)
    hres hcuts ht measurable_const j
  have hstart := startState_measurable active _ _ _ (fun _ => eta) hres hcuts ht measurable_const
  have hpayments := payments_measurable _ _
    (state_cells_measurable.comp (loop_current_measurable.comp hstart)) (loop_accepted_measurable.comp hs)
  exact measurable_list_append.comp (hw.prodMk
    (RefinedUpperCorrectionOutputMeasurable.getD_measurable _ ((measurable_list_getElem j.val).comp hpayments) []))

theorem stage_measurable (chores : Bool) (active : Fin k → Fin n) (eta lam : ℝ)
    (result : X → RefinedUpperRepairTrial.Result n k coarse fine) (hr : Measurable result) :
    Measurable (fun x => stage chores active eta lam (result x)) :=
  (Measurable.of_eval (paymentCells_measurable chores active _ eta lam _
    (measurable_fst.comp hr) (measurable_snd.comp hr))).prodMk
      ((loop_current_measurable.comp (measurable_snd.comp hr)).prodMk
        (loop_stopped_measurable.comp (measurable_snd.comp hr)))

end EnvyFreeResearch.Full.RefinedUpperRepairAssembly
