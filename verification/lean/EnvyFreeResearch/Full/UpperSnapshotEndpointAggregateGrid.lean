import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregateSupported
import EnvyFreeResearch.Full.UpperGridData
import EnvyFreeResearch.Full.UpperMixtureRegularity

/-! The aggregate event is evaluated on the actual quantile-and-sample grid.
The complete sampler seed tape, and therefore its complete ordinary-query
history, remains available to every later endpoint computation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperAggregateInterpolation UpperGridInterpolation UpperSortedGrid Chores
variable {n q m : ℕ} {Row Draw Generated : Type*}
  [Fintype Row] [Nonempty Row] [MeasurableSpace Row] [MeasurableSingletonClass Row]
  [MeasurableSpace Draw] [Fintype Generated]

/-- Actual original-sampler specialization. The iid projection, support,
atomlessness, and deterministic permanent endpoint conditions are all derived. -/
theorem original_grid_supported_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Row → Fin n) (policy : Policy n)
    (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (normalizer : Row → ℝ) (errorDomain : List Component)
    (drawLaw : Measure Draw) [IsProbabilityMeasure drawLaw]
    (points : (Fin m → Row × I) × Draw → Generated → ℝ)
    (hpoints : ∀ j, Measurable (fun p => points p j))
    (Λ b : ℝ) (hΛ : 0 ≤ Λ) (hb : 0 < b)
    (hfiber : ∀ᵐ p ∂UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw Row) m,
      ∀ u : ℝ → ℝ≥0∞, Measurable u → u 0 = 0 →
      (∫⁻ draw, ∑ j, u (points (p, draw) j) ∂drawLaw) ≤
        ENNReal.ofReal Λ * ∫⁻ z, u z ∂UpperMixtureSampling.mixture μ active origin.cells) :
    ((UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw Row) m).prod drawLaw)
      {p | BadSupportedRecordedUnion (fun i => μ (active i)) normalizer errorDomain
        (UpperGridMerge.cuts policy active origin q m p.1) (points p) b} ≤
      ENNReal.ofReal (2 * ((Fintype.card Row : ℝ) - 1) * Λ * (1 + b) /
        (b * (m + 1 : ℕ))) := by
  letI := UpperMixtureSampling.mixture_probability μ active origin.cells hpositive
  have heq (draw : Fin m → Row × I) : UpperGridMerge.cuts policy active origin q m draw =
      sorted (augmented (UpperRecordedQuantiles.run policy active origin q).1
        (UpperGridMerge.prepare policy active origin q m draw).2.1) :=
    UpperGridData.cuts_eq_augmented (UpperGridMerge.prepare policy active origin q m draw)
  simp_rw [heq]
  exact endpoint_vector_supported_probability (fun i => μ (active i)) normalizer errorDomain
    (UpperRecordedQuantiles.run policy active origin q).1
    (fun i => (UpperGridMerge.coarse_endpoints μ policy hpolicy active origin hgood hpositive q i).1)
    (UpperMixtureSampling.mixture μ active origin.cells)
    (UpperMixtureSampling.mixture_supported μ active origin.cells)
    (UpperAdaptiveProduct.tapeLaw (UpperMixtureSampling.seedLaw Row) m)
    (fun draw => (UpperGridMerge.prepare policy active origin q m draw).2.1)
    (UpperGridMerge.iid_sample_law μ policy hpolicy hmeas active origin hgood hpositive q m)
    drawLaw points hpoints Λ b hΛ hb hfiber

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
