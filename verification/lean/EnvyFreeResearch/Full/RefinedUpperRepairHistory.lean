import EnvyFreeResearch.Full.RefinedUpperRepair

/-! Every attempted new Repair query remains in a truthful final history,
including cycle rejection and every rejected correction attempt. -/
noncomputable section
open MeasureTheory
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperRepairHistory
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable UpperEndpointCache
  UpperRepairPreparationChecks RefinedUpperPreparation RefinedUpperParameterCounts RefinedUpperRepairParameters
  RefinedUpperRepairTargets RefinedUpperRepairFinalCache
open UpperRepairParameters (scale logarithm scale_large logarithm_positive active_scale)
variable {n k : ℕ} [Nonempty (Fin k)]

 theorem original_history_truthful
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : Near chores μ active origin old (RefinedUpperRepair.nearError n)) (p : RefinedUpperRepair.Tape n k) :
    Truthful μ (RefinedUpperRepair.execute policy hk chores active origin old p).2.1.history := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hs := scale_large n
  have he : (1 : ℝ) ≤ logarithm (scale n) := by exact_mod_cast logarithm_positive hs
  have ha := active_scale n k hkn
  let data := UpperGridMerge.prepare policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) p.1.1
  let prepared := RefinedUpperPreparationProgram.finish hk chores active origin old data (RefinedUpperRepair.repeats n) p.1.2.1 p.1.2.2
  have hc := physical_checks hs he ha μ policy hpolicy active origin hgood hpositive hk chores old hold hnear p.1.1 p.1.2.1 p.1.2.2
  unfold RefinedUpperRepair.execute RefinedUpperRepairLaw.execute RefinedUpperRepairProgram.execute
  rw [RefinedUpperRepairProgram.finish_history]
  change Truthful μ (RefinedUpperRepairTrial.after policy chores active origin prepared
    (RefinedUpperRepair.cellBound n) (RefinedUpperRepair.gapMultiplier n) p.2).2.current.history
  by_cases hp : approved chores active prepared (RefinedUpperRepair.gapMultiplier n) = true
  · simp only [RefinedUpperRepairTrial.after,hp,ite_true]
    exact (stage_recording μ policy hpolicy active hinj prepared.2.1 (UpperGridData.cuts data)
      (targets chores active prepared (RefinedUpperRepair.cellBound n) (RefinedUpperRepair.gapMultiplier n))
      (RefinedUpperRepair.cellBound n) (RefinedUpperRepair.gapMultiplier n) (2*(RefinedUpperRepair.fine n : ℝ))
      (by unfold RefinedUpperRepair.cellBound fineCap; positivity)
      (by unfold RefinedUpperRepair.gapMultiplier multiplier; positivity)
      (linear_margin hs ha) (correction_spending hs he ha)
      (RefinedUpperRepairSeedIndices.reserved active origin data (RefinedUpperRepair.repeats n)) hc p.2).1.2.2.1
  · simp only [RefinedUpperRepairTrial.after,hp,ite_false,RefinedUpperRepairTrial.rejected]
    exact hc.wellFormed.2.2.1

end EnvyFreeResearch.Full.RefinedUpperRepairHistory
