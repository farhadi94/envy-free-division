import EnvyFreeResearch.Full.RefinedUpperRepairAllocation
import EnvyFreeResearch.Full.RefinedUpperRepairTargets
import EnvyFreeResearch.Full.UpperCorrections

/-! The assembled actual Repair allocation has recorded caches, literal
disjointness and the physical margin derived from the actual accepted cycle
test and correction values. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.RefinedUpperRepairAllocation

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation RefinedUpperPreparation UpperLogicalPreparation UpperRepairJobs RefinedUpperRepairFinalCache
  UpperComponentAssembly UpperPreparedEnvelopeMean

variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ c, WellFormed μ (old c))
  (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells))
  (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2 * (jobCount k * L) < q + 1)
  (cap eta lam : ℝ) (pi : Equiv.Perm (Fin k))
  (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) {r : ℕ} (tape : Fin k → Fin r → UpperCircular.Circle)

set_option hygiene false

local notation "d" => UpperGridMerge.prepare policy active origin q m draw
local notation "R" => dataRetained active origin d L
local notation "cuts" => UpperGridData.cuts d
local notation "targets" => RefinedUpperRepairTargets.targets chores active
  (RefinedUpperPreparationProgram.finish hk chores active origin old d L pi threshold) eta lam
local notation "stage" => executeStage policy active R cuts targets eta lam tape
local notation "V" => dataMatrix hk active origin old d L pi threshold
local notation "A" => dataDisagreement active origin d L
local notation "X" => allocation hk chores active origin old d L pi threshold stage

variable (heta : 0 ≤ eta) (hlam : 0 ≤ lam) (hsize : 4*(k : ℝ) ≤ lam)
  (hmargin : (k : ℝ) * lam * eta < 1 / 16)
  (selected : Finset (Fin (UpperRecordedQuantiles.count (Agent := Fin k) q + m + 1)))
  (hc : Checks μ active R cuts targets eta selected cap)
  (hrun : stage.2.2 = false)

include hpolicy hgood hpositive holdbuffer hbudget hrun in
theorem package_payment_disjoint (c j : Fin k) :
    Disjoint (domain (RefinedUpperPreparation.packages hk active origin old d L pi threshold c).cells)
      (domain (paymentState stage j).cells) := by
  have hp := RefinedUpperPreparation.packages_retained_disjoint μ policy hpolicy active origin hgood hpositive hk old
    holdbuffer q m L draw hbudget pi threshold c
  have hs := paymentState_subset policy active R cuts targets eta lam tape hrun j
  exact hp.mono_right hs

include hpolicy hinj hgood hpositive hold holdbuffer hbudget heta hlam hsize hmargin hc hrun in
theorem allocation_wellFormed (holdHistory : ∀ c, (old c).history ⊆ origin.history) (j : Fin k) :
    WellFormed μ (X j) := by
  have hf := stage_recording μ policy hpolicy active hinj R cuts targets eta lam cap heta hlam hsize hmargin selected hc tape
  apply join_wellFormed μ _ _ stage.2.1.history
    (RefinedUpperPreparation.packages_wellFormed μ policy hpolicy active origin hgood hpositive hk old hold holdbuffer
      holdHistory q m L draw hbudget pi threshold _)
    (paymentState_wellFormed μ policy hpolicy active hinj R cuts targets eta lam cap heta hlam hsize hmargin selected hc tape hrun j)
    (package_payment_disjoint μ policy hpolicy hk chores active origin hgood hpositive old holdbuffer q m L draw hbudget
      eta lam pi threshold tape hrun _ j) hf.1.2.2.1 hf.2.1 Subset.rfl

include hpolicy hgood hpositive hold holdbuffer hbudget hrun in
theorem allocation_values (i j : Fin k) :
    (μ (active i)).real (domain (X j).cells) / (μ (active i)).real (domain (R).cells) =
      V i (assignment chores V j) +
        (μ (active i)).real (domain (paymentState stage j).cells) / (μ (active i)).real (domain (R).cells) := by
  rw [allocation, join_mass _ _ _ _
    (package_payment_disjoint μ policy hpolicy hk chores active origin hgood hpositive old holdbuffer q m L draw hbudget
      eta lam pi threshold tape hrun _ j), add_div]
  congr 1
  exact RefinedUpperPreparation.packages_values μ policy hpolicy active origin hgood hpositive hk old hold holdbuffer
    q m L draw hbudget pi threshold i _

include hpolicy hgood hpositive holdbuffer hbudget heta hc hrun in
theorem allocation_disjoint
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells))) :
    Pairwise (fun i j => Disjoint (domain (X i).cells) (domain (X j).cells)) := by
  intro i j hij
  change Disjoint (domain (join _ _ _).cells) (domain (join _ _ _).cells)
  rw [join_domain, join_domain]
  apply disjoint_union_left.mpr
  constructor
  · apply disjoint_union_right.mpr
    refine ⟨?_, package_payment_disjoint μ policy hpolicy hk chores active origin hgood hpositive old holdbuffer
      q m L draw hbudget eta lam pi threshold tape hrun _ j⟩
    exact RefinedUpperPreparation.packages_pairwise μ policy hpolicy active origin hgood hpositive hk old holdpair holdbuffer
      q m L draw hbudget pi threshold (fun h => hij ((assignment chores V).injective h))
  · apply disjoint_union_right.mpr
    refine ⟨(package_payment_disjoint μ policy hpolicy hk chores active origin hgood hpositive old holdbuffer
      q m L draw hbudget eta lam pi threshold tape hrun _ i).symm, ?_⟩
    exact paymentState_disjoint μ policy active R cuts targets eta lam cap heta selected hc tape hrun hij

include hpolicy hinj hgood hpositive hold holdbuffer hbudget heta hsize hmargin hc hrun in
theorem allocation_margin
    (hcycle : cycleReject chores V A lam = false) (i j : Fin k) :
    lam * A i j ≤
      if chores then
        (μ (active i)).real (domain (X j).cells) / (μ (active i)).real (domain (R).cells) -
        (μ (active i)).real (domain (X i).cells) / (μ (active i)).real (domain (R).cells)
      else
        (μ (active i)).real (domain (X i).cells) / (μ (active i)).real (domain (R).cells) -
        (μ (active i)).real (domain (X j).cells) / (μ (active i)).real (domain (R).cells) := by
  have hvalue := allocation_values μ policy hpolicy hk chores active origin hgood hpositive old hold holdbuffer
    q m L draw hbudget eta lam pi threshold tape hrun
  have hpay := paymentState_values μ policy hpolicy active hinj R cuts targets eta lam cap
    heta hsize hmargin selected hc tape hrun
  let payment (r c : Fin k) := (μ (active r)).real (domain (paymentState stage c).cells) /
    (μ (active r)).real (domain (R).cells)
  have hown (j) : payment j j = targets j := (hpay j).1
  have herr (i j) : |payment i j - targets j| ≤ lam * A i j := (hpay j).2 i
  have hdiag : ∀ i, A i i = 0 := UpperPayments.cellGap_diagonal _
  cases chores
  · simp only [Bool.false_eq_true, ite_false]
    rw [hvalue i i, hvalue i j]
    exact UpperCorrections.accepted_cake_margin V A lam hdiag
      ((cycleReject_eq_false false V A lam).mp hcycle) payment hown herr i j
  · simp only [ite_true]
    rw [hvalue i j, hvalue i i]
    exact UpperCorrections.accepted_chore_margin V A lam eta hdiag
      ((cycleReject_eq_false true V A lam).mp hcycle) payment hown herr i j

end EnvyFreeResearch.Full.RefinedUpperRepairAllocation
