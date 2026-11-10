import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
import EnvyFreeResearch.Full.RefinedUpperRepairProgram

/-! Whole-old-label transport for the actual accepted ordinary Repair run. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperRepairJobs
variable {n k coarse fine : ℕ} [Nonempty (Fin k)]

theorem finish_whole_label_identity (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (L : ℕ) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k-1+1) → Fin (L+1)) (eta lam : ℝ)
    (r : RefinedUpperRepairTrial.Result n k coarse fine)
    (hsuccess : (RefinedUpperRepairProgram.finish hk chores active origin old L pi threshold eta lam r).2.2 = false)
    (j : Fin k) :
    domain ((RefinedUpperRepairProgram.finish hk chores active origin old L pi threshold eta lam r).1
      (receiver hk chores active origin old r.1.1 L pi threshold j)).cells =
    domain (old j).cells ∪ domain (additions hk chores active origin old r.1.1 L pi threshold
      (RefinedUpperRepairAssembly.stage chores active eta lam r) j).cells := by
  have hr : r.2.stopped = false := by
    simpa only [RefinedUpperRepairProgram.finish_stopped] using hsuccess
  simp only [RefinedUpperRepairProgram.finish,hr,Bool.false_eq_true,ite_false]
  exact whole_label_identity hk chores active origin old r.1.1 L pi threshold _ j

theorem execute_whole_label_identity {r : ℕ} (policy : Policy n) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k-1+1) → Fin (L+1)) (eta lam : ℝ)
    (tape : Fin k → Fin r → UpperCircular.Circle)
    (hsuccess : (RefinedUpperRepairProgram.execute policy hk chores active origin old q m L draw pi threshold eta lam tape).2.2 = false) :
    let result := RefinedUpperRepairTrial.execute policy hk chores active origin old q m L draw pi threshold eta lam tape
    ∀ j, domain ((RefinedUpperRepairProgram.execute policy hk chores active origin old q m L draw pi threshold eta lam tape).1
      (receiver hk chores active origin old result.1.1 L pi threshold j)).cells =
      domain (old j).cells ∪ domain (additions hk chores active origin old result.1.1 L pi threshold
        (RefinedUpperRepairAssembly.stage chores active eta lam result) j).cells := by
  intro result j
  exact finish_whole_label_identity hk chores active origin old L pi threshold eta lam result hsuccess j

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
