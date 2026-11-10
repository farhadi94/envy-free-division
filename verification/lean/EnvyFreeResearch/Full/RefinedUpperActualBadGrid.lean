import EnvyFreeResearch.Full.RefinedUpperBadGridProbability
import EnvyFreeResearch.Full.UpperMixtureRegularity

/-! The bad-grid bound under the actual ordinary-query sampling law,
conditional on the complete preceding query history. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperStability
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
variable {n k b m K : ℕ} [Nonempty (Fin k)]

theorem protectedMass_measurable
    (procedure : (Fin (b+(m+1)+2) → ℝ) → Fin K → ℝ)
    (hp : ∀ k, Measurable (fun s => procedure s k)) (permanent : Fin b → ℝ)
    (μ : Measure ℝ) [SFinite μ] :
    Measurable (fun samples : Fin m → ℝ => μ.real (protectedBad procedure permanent samples)) := by
  let join (z : (Fin m → ℝ) × ℝ) : Fin (m+1) → ℝ := Fin.cons z.2 z.1
  have hj : Measurable join := by
    apply Measurable.of_eval
    intro i
    refine Fin.cases measurable_snd (fun j => (measurable_pi_apply j).comp measurable_fst) i
  have he : Measurable (fun z : (Fin m → ℝ) × ℝ => coincidence procedure permanent (join z) 0) :=
    (coincidence_measurable procedure hp permanent 0).comp hj
  have h := he.stronglyMeasurable.integral_prod_right' (ν := μ)
  simpa only [join,coincidence_integral_eq_measure procedure hp] using h.measurable

theorem actual_bad_grid_probability
    (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (hm : MeasurablePolicy policy) (active : Fin k → Fin n)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (q : ℕ) (jobs finalJobs : List (Fin k × Fin k))
    (δ : ℝ) (hδ : 0 < δ) :
    let law := UpperMixtureSampling.mixture μ active origin.cells
    UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m
      {draw | δ ≤ law.real (physicalBad μ policy active origin q jobs finalJobs
        (UpperGridMerge.prepare policy active origin q m draw).1
        (UpperGridMerge.prepare policy active origin q m draw).2.1)} ≤
      ENNReal.ofReal ((((4*jobs.length+4*finalJobs.length : ℕ) : ℝ)/(m+1 : ℕ))/δ) := by
  let law := UpperMixtureSampling.mixture μ active origin.cells
  letI : IsProbabilityMeasure law := UpperMixtureSampling.mixture_probability μ active origin.cells hpositive
  let permanent := (UpperRecordedQuantiles.run policy active origin q).1
  let event : Set (Fin m → ℝ) := {samples | δ ≤ law.real
    (physicalBad μ policy active origin q jobs finalJobs permanent samples)}
  have hmass : Measurable (fun samples : Fin m → ℝ => law.real
      (physicalBad μ policy active origin q jobs finalJobs permanent samples)) :=
    protectedMass_measurable _ (RefinedUpperPeeling.endpointProcedure_measurable _
      (RefinedUpperPeeling.physicalCumulative_measurable μ active origin) _ jobs finalJobs) permanent law
  have hevent : MeasurableSet event := measurableSet_le measurable_const hmass
  have hlaw := UpperGridMerge.iid_sample_law μ policy hp hm active origin hgood hpositive q m
  have heq := hlaw.measure_preimage hevent.nullMeasurableSet
  change UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m
      {draw | δ ≤ law.real (physicalBad μ policy active origin q jobs finalJobs permanent
        (UpperGridMerge.prepare policy active origin q m draw).2.1)} =
    UpperAdaptiveProduct.tapeLaw law m event at heq
  change UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k)) m
      {draw | δ ≤ law.real (physicalBad μ policy active origin q jobs finalJobs permanent
        (UpperGridMerge.prepare policy active origin q m draw).2.1)} ≤ _
  rw [heq]
  exact physical_bad_grid_probability μ policy active origin q jobs finalJobs permanent law δ hδ

end EnvyFreeResearch.Full.RefinedUpperStability
