import EnvyFreeResearch.Full.UpperRepair

/-! Every answer from every attempted Repair query remains in a truthful
final history. This holds on preparation, cycle, correction and upper-mass
rejection branches, without assuming successful output or Borel replies. -/

noncomputable section
open MeasureTheory
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairHistory

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperEndpointCache UpperLogicalIsolation UpperLogicalPreparation UpperRepairJobs
  UpperCorrectionFinalCache UpperCorrectionStageProgram UpperPreparedEnvelopeMean
  UpperRepairPreparationChecks UpperRepairTrialProgram UpperRepairTrialLaw UpperPreparedTrialProgram

variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (q m L : ℕ) (theta : I) (htheta : 0 < (theta : ℝ)) (cap eta lam tau : ℝ)
  (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : (k : ℝ)^2 ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (htau : 0 ≤ tau) (hnear : Near chores μ active origin old tau)
  (hcell : cellCap q theta ≤ eta) (htarget : (k : ℝ) * targetBudget k q L theta tau lam < 1 / 16)
  (p : Tape k q m L)

set_option hygiene false
local notation "d" => UpperGridMerge.prepare policy active origin q m p.2.1.1
local notation "R" => UpperGridData.reserve d theta p.1
local notation "cuts" => UpperGridData.cuts d
local notation "targets" => dataTargets hk q chores active origin old d L theta p.1 p.2.1.2.1 p.2.1.2.2 lam
local notation "stage" => executeStage policy active R cuts targets eta lam p.2.2
local notation "selected" => reserveCells (UpperGridData.parent d) theta p.1

include hpolicy hinj hgood hpositive hold htheta heta hlam hsize hmargin htau hnear hcell htarget in
theorem final_history_truthful :
    Truthful μ (UpperRepairProgram.execute policy hk chores active origin old q m L theta cap eta lam p).2.1.history := by
  unfold UpperRepairProgram.execute
  rw [UpperRepairProgram.finish_history, UpperRepairTrialFull.result, UpperRepairTrialFull.finish_history]
  change Truthful μ (afterGrid policy active origin d theta p.1 eta lam
    (fun grid => dataTargets hk q chores active origin old grid L theta p.1 p.2.1.2.1 p.2.1.2.2 lam)
    (fun grid => approved hk chores active origin old grid L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2) p.2.2).2.2.1.history
  by_cases ha : approved hk chores active origin old d L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2 = true
  · simp only [afterGrid, ha, ite_true, rollback_history]
    have hc := approved_checks μ policy hpolicy active origin hgood hpositive hk chores old hold q m L p.2.1.1
      theta htheta cap eta lam tau p.1 p.2.1.2.1 p.2.1.2.2 htau hnear hlam hcell htarget ha
    exact (stage_recording μ policy hpolicy active hinj R cuts targets eta lam cap
      heta hlam hsize hmargin selected hc p.2.2).1.2.2.1
  · simp only [afterGrid, ha, ite_false]
    exact (UpperGridMerge.prepare_wellFormed μ policy hpolicy active origin hgood hpositive q m p.2.1.1).2.2.1

include hpolicy hinj hgood hpositive hold in
theorem original_history_truthful
    (hnear : Near chores μ active origin old (UpperRepair.nearError n)) (p : UpperRepair.Tape n k) :
    Truthful μ (UpperRepair.execute policy hk chores active origin old p).2.1.history := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hf := UpperRepairParameters.original_population_facts n k hk hkn
  have hs := UpperRepairParameters.scale_large n
  have hell : (1 : ℝ) ≤ UpperRepairParameters.logarithm (UpperRepairParameters.scale n) := by
    exact_mod_cast UpperRepairParameters.logarithm_positive hs
  apply final_history_truthful μ policy hpolicy hk chores active hinj origin hgood hpositive old hold
    (UpperRepair.coarse n) (UpperRepair.fine n) (UpperRepair.repeats n) (UpperRepair.reserveMark n)
    (UpperRepairParameters.reserve_positive hs hell) (UpperRepair.cutoff n) (UpperRepair.cellBound n)
    (UpperRepair.gapMultiplier n) (UpperRepair.nearError n)
    (UpperRepairParameters.fineCap_positive hs hell).le (UpperRepairParameters.multiplier_positive hs).le
    _ hf.correction_extra (UpperRepairParameters.oldError_positive hs hell).le hnear
    hf.normalized_cell_cap hf.total_target_budget p
  have hb := hf.rounding_margin
  change (k : ℝ)^2 ≤ UpperRepairParameters.multiplier (UpperRepairParameters.scale n)
  linarith [UpperRepairParameters.multiplier_positive hs]

end EnvyFreeResearch.Full.UpperRepairHistory
