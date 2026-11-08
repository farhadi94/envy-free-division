import EnvyFreeResearch.Full.UpperGlobalRunChanceActual
import EnvyFreeResearch.Full.UpperExpectedRuntimeThreeClasses
import EnvyFreeResearch.Full.UpperGlobalRunBudgetTsum
import EnvyFreeResearch.Full.UpperGlobalRunTerminationFiniteMean

/-! Actual global paid-call accounting and almost-sure termination. All three
primitive laws, pathwise success budgets, and dispatcher measurability are
derived from the concrete execution and its initial invariant. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperGlobalTape UpperStageMeasurable
  UpperGlobalRun.DispatchMeasurable UpperExpectedRuntime
variable {n : ℕ}

theorem actual_paidCount_measurable (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (fallback : Fin n) (chores : Bool) (initial : Phase n) :
    Measurable (paidCount policy fallback chores initial) := by
  exact Finset.measurable_sum _ (fun kind _ => attempts_measurable _
    (paidEvent_measurable policy fallback chores (step_measurable policy hmeas fallback chores) initial kind))

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (whole : Set ℝ) (chores : Bool) (a : Anchor n) (ha : (Phase.normalize a).Valid μ chores whole)
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hmeas : MeasurablePolicy policy) (fallback : Fin n)
include ha hpolicy hmeas

theorem actual_paid_mean :
    (∫⁻ omega, paidCount policy fallback chores (.normalize a) omega ∂streamLaw (universalLaw n)) ≤
      8 * (n*(n-1) : ℕ) := by
  simp_rw [paidCount_eq_three]
  apply three_class_attempt_bound (streamLaw (universalLaw n))
    (paidEvent policy fallback chores (.normalize a) .snapshot)
    (paidEvent policy fallback chores (.normalize a) .shrink)
    (paidEvent policy fallback chores (.normalize a) .repair)
    (successEvent policy fallback chores (.normalize a) .snapshot)
    (successEvent policy fallback chores (.normalize a) .shrink)
    (successEvent policy fallback chores (.normalize a) .repair)
  · exact paidEvent_measurable policy fallback chores (step_measurable policy hmeas fallback chores) _ _
  · exact paidEvent_measurable policy fallback chores (step_measurable policy hmeas fallback chores) _ _
  · exact paidEvent_measurable policy fallback chores (step_measurable policy hmeas fallback chores) _ _
  · exact successEvent_measurable policy hmeas fallback chores _ _
  · exact successEvent_measurable policy hmeas fallback chores _ _
  · exact successEvent_measurable policy hmeas fallback chores _ _
  · exact actual_snapshot_attempt_bound μ whole chores (.normalize a) ha policy hpolicy hmeas fallback
  · exact actual_shrink_attempt_bound μ whole chores (.normalize a) ha policy hpolicy hmeas fallback
  · exact actual_repair_attempt_bound μ whole chores (.normalize a) ha policy hpolicy hmeas fallback
  · exact UpperGlobalRunBudget.snapshot_success_count μ whole chores policy hpolicy fallback a ha
  · intro omega
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      UpperGlobalRunBudget.other_success_count μ whole chores policy hpolicy fallback a ha omega

theorem actual_terminates :
    ∀ᵐ omega ∂streamLaw (universalLaw n), finishedRun policy fallback chores (.normalize a) omega :=
  terminates_of_measurable_step_paid_mean policy fallback chores
    (step_measurable policy hmeas fallback chores) (.normalize a) (streamLaw (universalLaw n))
    _ (by finiteness)
    (actual_paid_mean μ whole chores a ha policy hpolicy hmeas fallback)

end EnvyFreeResearch.Full.UpperGlobalPhysical
