import EnvyFreeResearch.Full.RefinedUpperSnapshotMargin
import EnvyFreeResearch.Full.RefinedUpperRepairSnapshotUnconditional

/-! Unconditional acceptance of the actual recorded margin-check procedure. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperSnapshotContrast UpperSnapshotRepair RefinedUpperRepairSnapshot UpperRepairPreparationChecks
variable {n k : ℕ} [Nonempty (Fin k)]

theorem acceptance_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : Near chores μ active origin old (RefinedUpperRepair.nearError n))
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
    (holdHistory : ∀ j, (old j).history ⊆ origin.history)
    (chosen : Preparation n k → Selection k) (hchosen : Measurable chosen)
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hbaseline : ∀ p ∈ Success policy hk chores active origin old,
      Lambda ≤ contrast (prepOld policy active origin old (view p).1)
        (chosen (view p).1).1.1 (chosen (view p).1).1.2
        (chosen (view p).1).2.1 (chosen (view p).1).2.2) :
    31/64 < (RefinedUpperRepair.law n k).real {p |
      (UpperSnapshotProtocol.finish (by omega) chores active (Lambda/8) origin old
        (RefinedUpperRepair.execute policy hk chores active origin old p)).2.2 = false} :=
  acceptance_probability_of_failure_bound μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive
    old hold hnear holdpair holdbuffer holdHistory chosen hchosen
    (failure_real_lt μ policy hpolicy hmeas hk chores active hinj origin hgood hpositive old hold hnear)
    Lambda hLambda hbaseline

end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
