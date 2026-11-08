import EnvyFreeResearch.Full.UpperGlobalPhysicalRepair
import EnvyFreeResearch.Full.UpperRepairProgram

/-! Whole-old-label transport for the actual accepted ordinary Repair run,
not merely its output constructor or an abstract success specification. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperGlobalPhysicalRepair
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperRepairTrialProgram
  UpperRepairTrialLaw UpperPreparedTrialProgram
variable {n k q m L : ℕ} [Nonempty (Fin k)]

theorem finish_whole_label_identity (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (old : Fin k → State n) (L : ℕ) (theta : I)
    (labels : Labels k q) (pi : Equiv.Perm (Fin k)) (threshold : Thresholds k L)
    (r : Result n k q m)
    (hsuccess : (UpperRepairProgram.finish hk chores active origin old L theta labels pi threshold r).2.2 = false)
    (j : Fin k) :
    domain ((UpperRepairProgram.finish hk chores active origin old L theta labels pi threshold r).1
      (receiver hk chores active origin old r.1 L theta labels pi threshold j)).cells =
    domain (old j).cells ∪ domain (additions hk chores active origin old r.1 L theta labels pi threshold r.2 j).cells := by
  have hr : r.2.2.2 = false := by
    simpa only [UpperRepairProgram.finish_stopped] using hsuccess
  simp only [UpperRepairProgram.finish,hr,Bool.false_eq_true,ite_false]
  exact whole_label_identity hk chores active origin old r.1 L theta labels pi threshold r.2 j

theorem execute_whole_label_identity (policy : Policy n) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (q m L : ℕ) (theta : I) (cap eta lam : ℝ) (p : Tape k q m L)
    (hsuccess : (UpperRepairProgram.execute policy hk chores active origin old q m L theta cap eta lam p).2.2 = false) :
    let r := UpperRepairTrialFull.result policy hk chores active origin old q m L theta cap eta lam p
    ∀ j, domain ((UpperRepairProgram.execute policy hk chores active origin old q m L theta cap eta lam p).1
      (receiver hk chores active origin old r.1 L theta p.1 p.2.1.2.1 p.2.1.2.2 j)).cells =
      domain (old j).cells ∪
        domain (additions hk chores active origin old r.1 L theta p.1 p.2.1.2.1 p.2.1.2.2 r.2 j).cells := by
  intro r j
  exact finish_whole_label_identity hk chores active origin old L theta p.1 p.2.1.2.1 p.2.1.2.2 r hsuccess j

end EnvyFreeResearch.Full.UpperGlobalPhysicalRepair
