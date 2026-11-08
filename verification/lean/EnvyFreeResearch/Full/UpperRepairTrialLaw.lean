import EnvyFreeResearch.Full.UpperRepairPreparationChecks
import EnvyFreeResearch.Full.UpperMixtureRegularity

/-! The full original Repair random parameter retains sampler owners and
targets together with independent isolation randomness. Only its point
projection is transported to an iid law; no successful branch is conditioned. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairTrialLaw

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperRepairTrialProgram UpperPreparedTrialProgram

abbrev Parameter (k m L : ℕ) := (Fin m → Fin k × I) × IsolationDraw k L
abbrev Tape (k q m L : ℕ) := Labels k q × (Parameter k m L × (Fin k → UpperCircular.Circle))

def parameterLaw (k m L : ℕ) : Measure (Parameter k m L) :=
  (UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m).prod (isolationLaw k L)

instance parameterLaw_probability {k m L : ℕ} [Nonempty (Fin k)] :
    IsProbabilityMeasure (parameterLaw k m L) := by unfold parameterLaw; infer_instance

def trialLaw (k q m L : ℕ) : Measure (Tape k q m L) :=
  UpperReserve.labelLaw.prod ((parameterLaw k m L).prod
    (Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle))))

instance trialLaw_probability {k q m L : ℕ} [Nonempty (Fin k)] :
    IsProbabilityMeasure (trialLaw k q m L) := by unfold trialLaw; infer_instance

def data {n k m L : ℕ} (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q : ℕ) (parameter : Parameter k m L) : Grid n k q m :=
  UpperGridMerge.prepare policy active origin q m parameter.1

set_option maxHeartbeats 200000 in
theorem data_measurable {n k m L : ℕ} (policy : Policy n) (hmeas : MeasurablePolicy policy)
    (active : Fin k → Fin n) (origin : State n) (q : ℕ) :
    Measurable (data (m := m) (L := L) policy active origin q) := by
  exact UpperLogicalPreparationGuard.fixed_origin_projection_measurable
    (fun p : State n × (Fin m → Fin k × I) => UpperGridMerge.prepare policy active p.1 q m p.2)
    (UpperGridMerge.prepare_measurable policy hmeas active q m) origin

set_option maxHeartbeats 1000000 in
theorem original_samples_law {n k m L : ℕ} [Nonempty (Fin k)]
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (active : Fin k → Fin n) (origin : State n)
    (hgood : WellFormed μ origin) (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells)) (q : ℕ) :
    MeasurePreserving (fun x : Parameter k m L => (data policy active origin q x).2.1)
      (parameterLaw k m L)
      (Measure.pi (fun _ : Fin m => UpperMixtureSampling.mixture μ active origin.cells)) :=
  (UpperGridMerge.iid_sample_law μ policy hpolicy hmeas active origin hgood hpositive q m).comp
    measurePreserving_fst

theorem data_cuts {n k m L : ℕ} (policy : Policy n) (active : Fin k → Fin n) (origin : State n)
    (q : ℕ) (x : Parameter k m L) :
    UpperGridData.cuts (data policy active origin q x) =
      UpperSortedGrid.sorted (UpperGridInterpolation.augmented
        (UpperRecordedQuantiles.run policy active origin q).1 (data policy active origin q x).2.1) :=
  UpperGridData.cuts_eq_augmented _

end EnvyFreeResearch.Full.UpperRepairTrialLaw
