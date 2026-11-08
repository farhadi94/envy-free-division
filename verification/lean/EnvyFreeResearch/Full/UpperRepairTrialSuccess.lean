import EnvyFreeResearch.Full.UpperRepairTrialFull

/-! Pathwise correspondence of an accepted complete trial with the actual
approved correction stage and both reserve checks. -/

noncomputable section
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairTrialSuccess

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperPreparedTrialProgram
  UpperRepairTrialProgram UpperRepairTrialLaw UpperLogicalIsolation UpperSnapshotCandidates

variable {n k q m L : ℕ} [Nonempty (Fin k)]

theorem afterGrid_success (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (data : Grid n k q m) (theta : I) (labels : Labels k q) (eta lam : ℝ)
    (targets : Grid n k q m → Fin k → ℝ) (approved : Grid n k q m → Bool)
    (starts : Fin k → UpperCircular.Circle)
    (hsuccess : (afterGrid policy active origin data theta labels eta lam targets approved starts).2.2.2 = false) :
    approved data = true ∧
      afterGrid policy active origin data theta labels eta lam targets approved starts =
        (data, UpperCorrectionStageProgram.executeStage policy active (UpperGridData.reserve data theta labels)
          (UpperGridData.cuts data) (targets data) eta lam starts) ∧
      (UpperCorrectionStageProgram.executeStage policy active (UpperGridData.reserve data theta labels)
        (UpperGridData.cuts data) (targets data) eta lam starts).2.2 = false := by
  by_cases ha : approved data = true
  · simp only [afterGrid, ha, ite_true, UpperRepairTrialRejection.rollback_stopped] at hsuccess
    refine ⟨ha, ?_, hsuccess⟩
    simp only [afterGrid, ha, ite_true, rollback, hsuccess, Bool.false_eq_true, ite_false]
  · simp only [afterGrid, ha, Bool.false_eq_true, ite_false, Bool.true_eq_false] at hsuccess

theorem accepted_stage (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L)
    (hsuccess : (UpperRepairTrialFull.result policy hk chores active origin old q m L theta cap eta lam p).2.2.2 = false) :
    let d := data policy active origin q p.2.1
    let stage := UpperCorrectionStageProgram.executeStage policy active (UpperGridData.reserve d theta p.1)
      (UpperGridData.cuts d) (dataTargets hk q chores active origin old d L theta p.1 p.2.1.2.1 p.2.1.2.2 lam) eta lam p.2.2
    approved hk chores active origin old d L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2 = true ∧
      UpperRepairTrialFull.result policy hk chores active origin old q m L theta cap eta lam p = (d, stage) ∧
      stage.2.2 = false ∧ upperReserve active origin (UpperGridData.reserve d theta p.1) theta = true := by
  dsimp only
  change (UpperRepairTrialFull.finish active origin theta p.1
    (UpperRepairTrialRejection.result policy hk chores active origin old q m L theta cap eta lam p)).2.2.2 = false at hsuccess
  rw [UpperRepairTrialFull.finish_stopped, Bool.or_eq_false_iff] at hsuccess
  have hu := Bool.eq_true_of_not_eq_false' hsuccess.2
  have hbase := afterGrid_success policy active origin (data policy active origin q p.2.1) theta p.1 eta lam
    (fun d => dataTargets hk q chores active origin old d L theta p.1 p.2.1.2.1 p.2.1.2.2 lam)
    (fun d => approved hk chores active origin old d L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2) p.2.2 hsuccess.1
  refine ⟨hbase.1, ?_, hbase.2.2, ?_⟩
  · change UpperRepairTrialFull.finish active origin theta p.1
      (UpperRepairTrialRejection.result policy hk chores active origin old q m L theta cap eta lam p) = _
    simp only [UpperRepairTrialFull.finish, hu, ite_true]
    exact hbase.2.1
  · simpa only [UpperRepairTrialFull.grid_result] using hu

end EnvyFreeResearch.Full.UpperRepairTrialSuccess
