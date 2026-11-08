import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateGrid
import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateParameters

/-! The complete original-tape Snapshot interpolation exception at the
manuscript's sample count and accuracy, with the shared endpoint budget. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperAggregateInterpolation Chores
variable {n k q s ell : ℕ} [Nonempty (Fin k)]
  {Draw Generated : Type*} [MeasurableSpace Draw] [Fintype Generated]

theorem original_grid_full_budget_small
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (policy : Policy n)
    (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (normalizer : Fin k → ℝ) (errorDomain : List Component)
    (drawLaw : Measure Draw) [IsProbabilityMeasure drawLaw]
    (points : (Fin (UpperRepairParameters.samples s ell) → Fin k × I) × Draw → Generated → ℝ)
    (hpoints : ∀ j, Measurable (fun p => points p j))
    (hs : (4 : ℝ) ≤ s) (hell : (1 : ℝ) ≤ ell) (hks : (k : ℝ) ≤ s)
    (hfiber : ∀ᵐ p ∂UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k))
        (UpperRepairParameters.samples s ell),
      ∀ u : ℝ → ℝ≥0∞, Measurable u → u 0 = 0 →
      (∫⁻ draw, ∑ j, u (points (p, draw) j) ∂drawLaw) ≤
        ENNReal.ofReal (64*(k : ℝ)^4) * ∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active origin.cells) :
    ((UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw (Fin k))
      (UpperRepairParameters.samples s ell)).prod drawLaw)
      {p | BadSupportedRecordedUnion (fun i => μ (active i)) normalizer errorDomain
        (UpperGridMerge.cuts policy active origin q (UpperRepairParameters.samples s ell) p.1)
        (points p) (snapshotAccuracy s)} < 1/64 := by
  have hsp : 0 < s := by exact_mod_cast (show (0 : ℝ) < s by linarith)
  have h := original_grid_supported_probability (q := q) μ active policy hpolicy hmeas origin hgood hpositive
    normalizer errorDomain drawLaw points hpoints (64*(k : ℝ)^4) (snapshotAccuracy s)
    (by positivity) (snapshot_accuracy_positive hsp) hfiber
  simp only [Fintype.card_fin] at h
  exact h.trans_lt (snapshot_full_budget_failure_small hs hell hks)

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
