import EnvyFreeResearch.Full.RefinedUpperRepairEvents

/-! The preparation exceptions under the unchanged original parameter law:
the queried grid is iid and assignment isolation is uniform over each grid. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperRepairEvents
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  RefinedUpperRepairLaw RefinedUpperStability RefinedUpperPreparation
variable {n k m L : ℕ} [Nonempty (Fin k)]

theorem grid_probability
    (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (active : Fin k → Fin n)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (q : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    UpperRepairTrialLaw.parameterLaw k m L (badGrid μ policy active origin q δ) ≤
      ENNReal.ofReal ((((4*(UpperLogicalIsolation.requests k L).length+
        4*(RefinedUpperActualCorrectionBound.finalJobs k).length : ℕ) : ℝ)/(m+1 : ℕ))/δ) := by
  let law := UpperMixtureSampling.mixture μ active origin.cells
  letI : IsProbabilityMeasure law := UpperMixtureSampling.mixture_probability μ active origin.cells hpositive
  let permanent := (UpperRecordedQuantiles.run policy active origin q).1
  let event : Set (Fin m → ℝ) := {samples | δ ≤ law.real
    (physicalBad μ policy active origin q (UpperLogicalIsolation.requests k L)
      (RefinedUpperActualCorrectionBound.finalJobs k) permanent samples)}
  have hmass : Measurable (fun samples : Fin m → ℝ => law.real
      (physicalBad μ policy active origin q (UpperLogicalIsolation.requests k L)
        (RefinedUpperActualCorrectionBound.finalJobs k) permanent samples)) :=
    protectedMass_measurable _ (RefinedUpperPeeling.endpointProcedure_measurable _
      (RefinedUpperPeeling.physicalCumulative_measurable μ active origin) _ _ _) permanent law
  have hevent : MeasurableSet event := measurableSet_le measurable_const hmass
  have hlaw := UpperRepairTrialLaw.original_samples_law (m := m) (L := L)
    μ policy hp hm active origin hgood hpositive q
  have heq := hlaw.measure_preimage hevent.nullMeasurableSet
  change UpperRepairTrialLaw.parameterLaw k m L (badGrid μ policy active origin q δ) =
    (Measure.pi (fun _ : Fin m => law)) event at heq
  rw [heq]
  exact physical_bad_grid_probability μ policy active origin q _ _ permanent law δ hδ

theorem cycle_probability
    (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (old : Fin k → State n) (q : ℕ) (hbudget : 2*(UpperRepairJobs.jobCount k*L) < q+1)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    UpperRepairTrialLaw.parameterLaw k m L (badCycle policy hk chores active origin old q lam) ≤
      ENNReal.ofReal (UpperLogicalIsolation.isolationBound k L lam) := by
  rw [UpperRepairTrialLaw.parameterLaw,Measure.prod_apply (badCycle_measurable policy hm hk chores active origin old q lam)]
  calc
    _ ≤ ∫⁻ _draw, ENNReal.ofReal (UpperLogicalIsolation.isolationBound k L lam)
        ∂UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m := by
      apply lintegral_mono
      intro draw
      have h := data_cycle_probability μ policy hp active origin hgood hpositive hk q m L draw hbudget old lam hlam chores
      simpa only [badCycle,prepared,RefinedUpperPreparationProgram.execute,
        RefinedUpperPreparationProgram.finish,RefinedUpperRepairTargets.approved,
        RefinedUpperRepairTargets.disagreement,dataDisagreement,
        Set.preimage_ofPred_eq,Bool.not_eq_false_eq_eq_true] using h
    _ = _ := by simp

end EnvyFreeResearch.Full.RefinedUpperRepairEvents
