import EnvyFreeResearch.Full.UpperRepairProgram

/-! Exact accepted/rejected output correspondence for the physical ordinary
Repair program, before applying measure-theoretic correctness lemmas. -/

noncomputable section
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairProgram

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperRepairTrialProgram
  UpperRepairTrialLaw UpperLogicalIsolation UpperCorrectionStageProgram UpperSnapshotCandidates

variable {n k : ℕ} [Nonempty (Fin k)]

theorem execute_stopped (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L) :
    (execute policy hk chores active origin old q m L theta cap eta lam p).2.2 =
      (UpperRepairTrialFull.result policy hk chores active origin old q m L theta cap eta lam p).2.2.2 :=
  finish_stopped hk chores active origin old L theta p.1 p.2.1.2.1 p.2.1.2.2 _

theorem rejected_restore (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L)
    (hreject : (execute policy hk chores active origin old q m L theta cap eta lam p).2.2 = true) :
    (execute policy hk chores active origin old q m L theta cap eta lam p).1 = old ∧
      (execute policy hk chores active origin old q m L theta cap eta lam p).2.1.cells = origin.cells := by
  rw [execute_stopped] at hreject
  simp only [execute, finish, hreject, ite_true, and_self]

theorem accepted_output (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (theta : I) (cap eta lam : ℝ)
    (p : Tape k q m L)
    (hsuccess : (execute policy hk chores active origin old q m L theta cap eta lam p).2.2 = false) :
    let d := data policy active origin q p.2.1
    let stage := executeStage policy active (UpperGridData.reserve d theta p.1) (UpperGridData.cuts d)
      (dataTargets hk q chores active origin old d L theta p.1 p.2.1.2.1 p.2.1.2.2 lam) eta lam p.2.2
    approved hk chores active origin old d L theta cap lam p.1 p.2.1.2.1 p.2.1.2.2 = true ∧
      execute policy hk chores active origin old q m L theta cap eta lam p =
        (UpperRepairAllocation.allocation hk chores active origin old d L theta p.1 p.2.1.2.1 p.2.1.2.2 stage,
          UpperRepairRemaining.remaining hk active origin d L theta p.1 p.2.1.2.1 p.2.1.2.2 stage.2.1, false) ∧
      stage.2.2 = false ∧ upperReserve active origin (UpperGridData.reserve d theta p.1) theta = true := by
  rw [execute_stopped] at hsuccess
  obtain ⟨ha, he, hs, hu⟩ := UpperRepairTrialSuccess.accepted_stage policy hk chores active origin old q m L
    theta cap eta lam p hsuccess
  refine ⟨ha, ?_, hs, hu⟩
  unfold execute
  rw [he]
  simp only [finish, hs, Bool.false_eq_true, ite_false]

end EnvyFreeResearch.Full.UpperRepairProgram
