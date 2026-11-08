import EnvyFreeResearch.Full.UpperGlobalPhysicalRepairRun
import EnvyFreeResearch.Full.UpperRepairCorrespondence

/-! Actual seed and payment locations place every whole-label addition
inside the original Repair buffer, including literal null material. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperGlobalPhysicalRepair
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairJobs UpperCorrectionFinalCache
  UpperCorrectionStageProgram UpperComponentAssembly
variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
  (theta : I) (eta lam : ℝ) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
  (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (tape : Fin k → UpperCircular.Circle)
set_option hygiene false
local notation "d" => UpperGridMerge.prepare policy active origin q m draw
local notation "R" => UpperGridData.reserve d theta labels
local notation "cuts" => UpperGridData.cuts d
local notation "targets" => dataTargets hk q chores active origin old d L theta labels pi threshold lam
local notation "stage" => executeStage policy active R cuts targets eta lam tape

include hpolicy hgood hpositive in
theorem actual_additions_subset (hrun : stage.2.2 = false) (j : Fin k) :
    domain (additions hk chores active origin old d L theta labels pi threshold stage j).cells ⊆
      domain origin.cells := by
  unfold additions
  rw [join_domain,group_domain]
  apply union_subset
  · apply iUnion_subset
    intro a
    split_ifs
    · exact UpperRepairPackages.seeds_subset μ policy hpolicy active origin hgood hpositive
        hk q m L draw theta labels pi threshold a
    · exact empty_subset _
  · have hpay := paymentState_subset policy active R cuts targets eta lam tape hrun
      (receiver hk chores active origin old d L theta labels pi threshold j)
    apply hpay.trans
    rw [UpperGridData.reserve_execute]
    exact reserveState_subset μ policy hpolicy active origin hgood hpositive q m draw theta labels

end EnvyFreeResearch.Full.UpperGlobalPhysicalRepair
