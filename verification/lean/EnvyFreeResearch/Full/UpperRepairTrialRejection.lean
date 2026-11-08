import EnvyFreeResearch.Full.UpperRepairPreparationProbability

/-! The actual trial's rejection bit is exactly the preparation/isolation
failure or the actual correction loop's failure. This is a pathwise statement
about the ordinary-program executor, including its rollback branch. -/

noncomputable section

open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairTrialRejection

open UpperRecordedDomain UpperCircularStage UpperCorrectionExecution UpperStageMeasurable
  UpperRepairTrialProgram UpperRepairTrialLaw UpperPreparedTrialProgram UpperLogicalIsolation
  UpperLogicalPreparationGuard UpperRepairPreparationProbability

variable {n k q m L : ℕ} [Nonempty (Fin k)]

def result (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L) : Result n k q m :=
  execute policy hk chores active origin old q m L p.2.1.1 theta cap eta lam p.1
    p.2.1.2.1 p.2.1.2.2 p.2.2

def Failed (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ) :
    Set (Tape k q m L) :=
  {p | (result policy hk chores active origin old q m L theta cap eta lam p).2.2.2 = true}

theorem rollback_stopped (origin : State n) (r : UpperCorrectionStageProgram.Result n k) :
    (rollback origin r).2.2 = r.2.2 := by
  unfold rollback
  split_ifs with h
  · exact h.symm
  · rfl

theorem approved_actual (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q L : ℕ) (theta : I) (cap lam : ℝ)
    (labels : Labels k q) (x : Parameter k m L) :
    approved hk chores active origin old (data policy active origin q x) L theta cap lam labels x.2.1 x.2.2 =
      (guard policy active origin q m (requests k L) theta cap x.1 labels &&
        !cycleReject chores (cachedMatrix hk policy active origin old q m L x.1 theta labels x.2.1 x.2.2)
          (disagreement policy active origin q m x.1 theta labels) lam) := by
  simp only [approved, data, UpperGridData.guard_execute, dataMatrix_execute, dataDisagreement_execute]

theorem failed_iff (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L) :
    p ∈ Failed policy hk chores active origin old q m L theta cap eta lam ↔
      approved hk chores active origin old (data policy active origin q p.2.1)
        L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2 = false ∨
      UpperCorrectionRejectionMeasurable.rejected policy active
        (UpperGridData.reserve (data policy active origin q p.2.1) theta p.1)
        (UpperGridData.cuts (data policy active origin q p.2.1))
        (dataTargets hk q chores active origin old (data policy active origin q p.2.1)
          L theta p.1 p.2.1.2.1 p.2.1.2.2 lam) eta lam
        (approved hk chores active origin old (data policy active origin q p.2.1)
          L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2) p.2.2 = true := by
  by_cases h : approved hk chores active origin old (data policy active origin q p.2.1)
      L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2 = true
  · change approved hk chores active origin old (UpperGridMerge.prepare policy active origin q m p.2.1.1)
      L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2 = true at h
    simp only [Failed, Set.mem_setOf_eq, result, UpperRepairTrialProgram.execute, executeTrial, afterGrid,
      data, h, ite_true, rollback_stopped, Bool.true_eq_false, false_or,
      UpperCorrectionRejectionMeasurable.rejected,
      UpperPreparedEnvelopeFamily.preparedInitial, Bool.true_and,
      UpperCorrectionStageProgram.executeStage, UpperCorrectionStageProgram.finish]
  · have hf : approved hk chores active origin old (data policy active origin q p.2.1)
        L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2 = false := Bool.eq_false_iff.mpr h
    change approved hk chores active origin old (UpperGridMerge.prepare policy active origin q m p.2.1.1)
      L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2 = false at hf
    simp only [Failed, Set.mem_setOf_eq, result, UpperRepairTrialProgram.execute, executeTrial, afterGrid,
      data, hf, Bool.false_eq_true, ite_false, true_or]

end EnvyFreeResearch.Full.UpperRepairTrialRejection
