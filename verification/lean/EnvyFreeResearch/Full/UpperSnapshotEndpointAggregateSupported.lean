import EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
import EnvyFreeResearch.Full.UpperAggregateInterpolationSupported

/-! Physical Snapshot pieces may have arbitrary inherited domain joins.
The interpolation event charges only the virtual grid/generated endpoints. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
open UpperRecordedDomain UpperAggregateInterpolation UpperGridInterpolation UpperSortedGrid
  UpperGridSensitivity
variable {permanentCount sampleCount : ℕ}
  {Row Parameter Draw Generated : Type*} [Fintype Row] [Nonempty Row]
  [MeasurableSpace Parameter] [MeasurableSpace Draw] [Fintype Generated]

theorem endpoint_vector_supported_probability
    (μ : Row → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (normalizer : Row → ℝ) (errorDomain : List Component)
    (permanent : Fin permanentCount → ℝ) (hpermanent : ∀ i, 0 ≤ permanent i)
    (sampleLaw : Measure ℝ) [IsProbabilityMeasure sampleLaw] [NullSingletonClass sampleLaw]
    (hsupport : ∀ᵐ x ∂sampleLaw, x ∈ Icc (0 : ℝ) 1)
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw]
    (samples : Parameter → Fin sampleCount → ℝ)
    (hsamples : MeasurePreserving samples parameterLaw (Measure.pi (fun _ : Fin sampleCount => sampleLaw)))
    (drawLaw : Measure Draw) [IsProbabilityMeasure drawLaw]
    (points : Parameter × Draw → Generated → ℝ)
    (hpoints : ∀ j, Measurable (fun p => points p j))
    (Λ b : ℝ) (hΛ : 0 ≤ Λ) (hb : 0 < b)
    (hfiber : ∀ᵐ p ∂parameterLaw, ∀ u : ℝ → ℝ≥0∞, Measurable u → u 0 = 0 →
      (∫⁻ draw, ∑ j, u (points (p, draw) j) ∂drawLaw) ≤
        ENNReal.ofReal Λ * ∫⁻ z, u z ∂sampleLaw) :
    (parameterLaw.prod drawLaw)
      {p | BadSupportedRecordedUnion μ normalizer errorDomain
        (sorted (augmented permanent (samples p.1))) (points p) b} ≤
      ENNReal.ofReal (2 * ((Fintype.card Row : ℝ) - 1) * Λ * (1 + b) /
        (b * (sampleCount + 1 : ℕ))) := by
  simp_rw [badSupportedRecordedUnion_iff]
  exact endpoint_vector_interpolation_probability μ normalizer errorDomain permanent hpermanent
    sampleLaw hsupport parameterLaw samples hsamples drawLaw points hpoints Λ b hΛ hb hfiber

/-- Outside the single aggregate bad event, equality of immutable cell rows
implies exact equality on every physically supported recorded union. -/
theorem equal_rows_exact_on_supported_union {g : ℕ}
    (μ : Row → Measure ℝ) (normalizer : Row → ℝ) (buffer : List Component)
    (cuts : Fin (g + 2) → ℝ) (points : Generated → ℝ) (b : ℝ)
    (hgood : ¬ BadSupportedRecordedUnion μ normalizer buffer cuts points b)
    (i j : Row) (hequal : ∀ e, physicalRows μ normalizer buffer cuts i e =
      physicalRows μ normalizer buffer cuts j e)
    (virtual : List Component) (actual : Set ℝ)
    (hendpoints : RecordedEndpoints cuts points virtual)
    (hactual : actual = domain buffer ∩ domain virtual) :
    (μ i).real actual / normalizer i = (μ j).real actual / normalizer j := by
  have hd : distance (physicalRows μ normalizer buffer cuts) i j = 0 := by
    simp [distance, hequal]
  have he : UpperEnvelope.estimate (physicalRows μ normalizer buffer cuts)
      (UpperEnvelope.uniformCells (UpperLogicalCells.cell (domain buffer) cuts)) i j actual = 0 := by
    simp [UpperEnvelope.estimate, hequal]
  have hle : |(μ i).real actual / normalizer i - (μ j).real actual / normalizer j| ≤ 0 := by
    by_contra hn
    apply hgood
    refine ⟨i, j, virtual, actual, hendpoints, hactual, ?_⟩
    simpa only [hd, he, mul_zero, sub_zero] using lt_of_not_ge hn
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
