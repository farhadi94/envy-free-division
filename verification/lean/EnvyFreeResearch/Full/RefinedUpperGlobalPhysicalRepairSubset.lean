import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepairRun
import EnvyFreeResearch.Full.RefinedUpperRepairCorrespondence

/-! Every whole-label addition is literal original-buffer material: the
new recorded seeds and the actual successful corrected payments. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairJobs RefinedUpperRepairFinalCache
  RefinedUpperPreparation UpperComponentAssembly
variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
  (eta lam : ℝ) (pi : Equiv.Perm (Fin k))
  (threshold : Fin (jobCount k-1+1) → Fin (L+1)) {r : ℕ} (tape : Fin k → Fin r → UpperCircular.Circle)
set_option hygiene false
local notation "d" => UpperGridMerge.prepare policy active origin q m draw
local notation "R" => dataRetained active origin d L
local notation "cuts" => UpperGridData.cuts d
local notation "targets" => RefinedUpperRepairTargets.targets chores active
  (RefinedUpperPreparationProgram.finish hk chores active origin old d L pi threshold) eta lam
local notation "stage" => executeStage policy active R cuts targets eta lam tape

include hpolicy hgood hpositive in
theorem actual_additions_subset (hrun : stage.2.2 = false) (j : Fin k) :
    domain (additions hk chores active origin old d L pi threshold stage j).cells ⊆ domain origin.cells := by
  unfold additions
  rw [join_domain,group_domain]
  apply union_subset
  · apply iUnion_subset
    intro a
    split_ifs
    · rw [RefinedUpperPreparation.dataSeedState_domain μ policy hpolicy active origin hgood hpositive]
      exact (Seeds.seed_subset _ _ _ _).trans (iUnion_subset fun b =>
        RefinedUpperPreparation.seedCells_subset μ policy hpolicy active origin hgood hpositive hk q m L draw pi a b)
    · exact empty_subset _
  · have hpay := paymentState_subset policy active R cuts targets eta lam tape hrun
      (receiver hk chores active origin old d L pi threshold j)
    apply hpay.trans
    rw [dataRetained_execute]
    exact reserveState_subset μ policy hpolicy active origin hgood hpositive q m draw 0 _

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalRepair
