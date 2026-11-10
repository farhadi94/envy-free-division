import EnvyFreeResearch.Full.RefinedUpperRepairProgram

/-! Exact accepted and rejected physical outputs of the new ordinary Repair. -/
noncomputable section
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperRepairProgram
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperRepairJobs
  RefinedUpperRepairTargets RefinedUpperRepairFinalCache
variable {n k r : ℕ} [Nonempty (Fin k)]

theorem execute_stopped (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle) :
    (execute policy hk chores active origin old q m L draw pi threshold eta lam tape).2.2 =
      (RefinedUpperRepairTrial.execute policy hk chores active origin old q m L draw pi threshold eta lam tape).2.stopped :=
  finish_stopped hk chores active origin old L pi threshold eta lam _

theorem rejected_restore (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle)
    (hr : (execute policy hk chores active origin old q m L draw pi threshold eta lam tape).2.2 = true) :
    (execute policy hk chores active origin old q m L draw pi threshold eta lam tape).1 = old ∧
      (execute policy hk chores active origin old q m L draw pi threshold eta lam tape).2.1.cells = origin.cells := by
  rw [execute_stopped] at hr
  simp only [execute,finish,hr,ite_true,and_self]

theorem accepted_output (policy : Policy n) (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1))
    (eta lam : ℝ) (tape : Fin k → Fin r → UpperCircular.Circle)
    (hsuccess : (execute policy hk chores active origin old q m L draw pi threshold eta lam tape).2.2 = false) :
    let p := RefinedUpperPreparationProgram.execute policy hk chores active origin old q m L draw pi threshold
    let stage := executeStage policy active p.2.1 (UpperGridData.cuts p.1) (targets chores active p eta lam) eta lam tape
    approved chores active p lam = true ∧
      execute policy hk chores active origin old q m L draw pi threshold eta lam tape =
        (RefinedUpperRepairAllocation.allocation hk chores active origin old p.1 L pi threshold stage,
          RefinedUpperRepairRemaining.remaining hk active origin p.1 L pi threshold stage.2.1,false) ∧
      stage.2.2 = false := by
  let p := RefinedUpperPreparationProgram.execute policy hk chores active origin old q m L draw pi threshold
  rw [execute_stopped] at hsuccess
  change (RefinedUpperRepairTrial.after policy chores active origin p eta lam tape).2.stopped = false at hsuccess
  have ha : approved chores active p lam = true := by
    by_contra hn
    simp [RefinedUpperRepairTrial.after,hn,RefinedUpperRepairTrial.rejected] at hsuccess
  have hs : (executeStage policy active p.2.1 (UpperGridData.cuts p.1)
      (targets chores active p eta lam) eta lam tape).2.2 = false := by
    simpa only [RefinedUpperRepairTrial.after,ha,ite_true,executeStage] using hsuccess
  refine ⟨ha,?_,hs⟩
  unfold execute
  rw [finish]
  change (if (RefinedUpperRepairTrial.after policy chores active origin p eta lam tape).2.stopped = true then _ else _) = _
  rw [hsuccess]
  simp only [Bool.false_eq_true,ite_false]
  simp only [RefinedUpperRepairTrial.execute]
  rw [RefinedUpperRepairAssembly.stage_after policy chores active origin p eta lam tape ha]
  have hfirst : (RefinedUpperRepairTrial.after policy chores active origin p eta lam tape).1 = p := by
    simp only [RefinedUpperRepairTrial.after,ha,ite_true]
  have hcurrent : (RefinedUpperRepairTrial.after policy chores active origin p eta lam tape).2.current =
      (executeStage policy active p.2.1 (UpperGridData.cuts p.1) (targets chores active p eta lam) eta lam tape).2.1 := by
    simp only [RefinedUpperRepairTrial.after,ha,ite_true,executeStage]
  rw [hfirst,hcurrent]

end EnvyFreeResearch.Full.RefinedUpperRepairProgram
