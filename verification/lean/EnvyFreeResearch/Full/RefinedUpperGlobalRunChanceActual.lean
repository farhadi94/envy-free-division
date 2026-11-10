import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunChanceReached
import EnvyFreeResearch.Full.RefinedUpperGlobalRunChanceSnapshot
import EnvyFreeResearch.Full.RefinedUpperGlobalRunDispatchMeasurableAccepted

/-! Concrete original-law bounds with all dispatcher Borel premises discharged.
Only the actual model's legal measurable response policy and initial invariant
remain as inputs. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage RefinedUpperGlobalTape UpperStageMeasurable
  RefinedUpperGlobalRun.DispatchMeasurable
variable {n : ℕ}
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (whole : Set ℝ) (chores : Bool) (initial : Phase n) (hinit : initial.Valid μ chores whole)
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hmeas : MeasurablePolicy policy) (fallback : Fin n)
include hinit hpolicy hmeas

theorem actual_shrink_attempt_bound (t : ℕ) :
    streamLaw (universalLaw n) (paidEvent policy fallback chores initial .shrink t) ≤
      (64/63 : ℝ≥0∞) * streamLaw (universalLaw n)
        (successEvent policy fallback chores initial .shrink t) :=
  shrink_original_attempt_bound μ whole chores initial hinit policy hpolicy hmeas fallback
    (step_measurable policy hmeas fallback chores) (accepted_measurable policy hmeas chores) t

theorem actual_repair_attempt_bound (t : ℕ) :
    streamLaw (universalLaw n) (paidEvent policy fallback chores initial .repair t) ≤
      (64/63 : ℝ≥0∞) * streamLaw (universalLaw n)
        (successEvent policy fallback chores initial .repair t) :=
  repair_original_attempt_bound μ whole chores initial hinit policy hpolicy hmeas fallback
    (step_measurable policy hmeas fallback chores) (accepted_measurable policy hmeas chores) t


theorem actual_snapshot_attempt_bound (t : ℕ) :
    streamLaw (universalLaw n) (paidEvent policy fallback chores initial .snapshot t) ≤
      (4 : ℝ≥0∞) * streamLaw (universalLaw n)
        (successEvent policy fallback chores initial .snapshot t) :=
  snapshot_original_attempt_bound μ whole chores initial hinit policy hpolicy hmeas fallback
    (step_measurable policy hmeas fallback chores) (accepted_measurable policy hmeas chores) t

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
