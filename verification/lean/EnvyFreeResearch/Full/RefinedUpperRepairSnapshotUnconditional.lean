import EnvyFreeResearch.Full.RefinedUpperRepairSnapshotProbability
import EnvyFreeResearch.Full.RefinedUpperRepairFailure

/-! Actual unconditional physical Snapshot margin for the refined Repair.
The finite-trial failure estimate is derived from its executed protocol. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperRepairSnapshot
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperRepairPreparationChecks RefinedUpperRepairAllocation UpperSnapshotContrast
variable {n k : ℕ} [Nonempty (Fin k)]
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (hnear : Near chores μ active origin old (RefinedUpperRepair.nearError n))
include hpolicy hmeas hinj hgood hpositive hold hnear

theorem failure_real_lt :
    (RefinedUpperRepair.law n k).real (Success policy hk chores active origin old)ᶜ < 1/64 := by
  have h := RefinedUpperRepair.failure_lt μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive old hold hnear
  have heq : (Success policy hk chores active origin old)ᶜ =
      {p | (RefinedUpperRepair.execute policy hk chores active origin old p).2.2 = true} := by
    ext p
    cases hs : (RefinedUpperRepair.execute policy hk chores active origin old p).2.2 <;> simp [Success,hs]
  rw [heq,measureReal_def]
  have hr := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (by norm_num : (1/64 : ℝ≥0∞) ≠ ⊤)).mpr h
  norm_num at hr ⊢
  exact hr

theorem original_trial_margin
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
    (holdHistory : ∀ j, (old j).history ⊆ origin.history)
    (chosen : Preparation n k → Selection k) (hchosen : Measurable chosen)
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hbaseline : ∀ p ∈ Success policy hk chores active origin old,
      Lambda ≤ contrast (prepOld policy active origin old (view p).1)
        (chosen (view p).1).1.1 (chosen (view p).1).1.2
        (chosen (view p).1).2.1 (chosen (view p).1).2.2) :
    31/64 < (RefinedUpperRepair.law n k).real (MarginEvent μ policy hk chores active origin old Lambda) :=
  original_trial_margin_of_failure_bound μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive
    old hold hnear holdpair holdbuffer holdHistory chosen hchosen
    (failure_real_lt μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive old hold hnear)
    Lambda hLambda hbaseline

end EnvyFreeResearch.Full.RefinedUpperRepairSnapshot
