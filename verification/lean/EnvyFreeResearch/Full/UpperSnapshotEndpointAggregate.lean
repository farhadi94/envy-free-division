import EnvyFreeResearch.Full.UpperAggregateInterpolation

/-!
# Aggregate interpolation with the full preparation history

An arbitrary preparation parameter retains the sampler's complete history.
Only its point projection has the proved iid law. The correction program may
depend on the entire parameter. The fixed analytic reserve/error domain is
separate from the larger original buffer used for sampling and raw supply.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate

open UpperRecordedDomain UpperAggregateInterpolation UpperGridInterpolation UpperSortedGrid
  UpperGridSensitivity

variable {permanentCount sampleCount : ℕ}
  {Row Parameter Draw Generated : Type*} [Fintype Row] [Nonempty Row]
  [MeasurableSpace Parameter] [MeasurableSpace Draw] [Fintype Generated]

theorem vector_charge_measurable
    (u : Parameter → ℝ → ℝ≥0∞) (hu : Measurable (Function.uncurry u))
    (points : Parameter × Draw → Generated → ℝ)
    (hpoints : ∀ j, Measurable (fun p => points p j)) :
    Measurable (fun p : Parameter × Draw => ∑ j, u p.1 (points p j)) := by
  have hterm (j : Generated) : Measurable (fun p : Parameter × Draw => u p.1 (points p j)) := by
    have hmap : Measurable (fun p : Parameter × Draw => (p.1, points p j)) :=
      measurable_fst.prodMk (hpoints j)
    exact hu.comp hmap
  exact Finset.measurable_sum Finset.univ (fun j _ => hterm j)

theorem immutable_charge_zero
    (μ : Row → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (normalizer : Row → ℝ) (errorDomain : List Component)
    (permanent : Fin permanentCount → ℝ) (hpermanent : ∀ i, 0 ≤ permanent i)
    (samples : Fin sampleCount → ℝ) (hvalid : ValidSamples samples) :
    immutableCharge (normalizedCumulative μ normalizer errorDomain)
      (domainCumulative volume errorDomain) permanent samples 0 = 0 := by
  have hzero : sorted (augmented permanent samples) 0 = 0 :=
    first_eq_zero _ (augmented_nonneg permanent samples hpermanent (fun i => (hvalid i).1))
      ⟨0, by simp [augmented]⟩
  unfold immutableCharge
  rw [linearMaximum_eq_physical μ normalizer errorDomain _ (sorted_monotone _) hzero]
  rw [← hzero, physicalMaximum_at_boundary μ normalizer errorDomain _ (sorted_monotone _) hzero 0]
  simp

set_option maxHeartbeats 1600000 in
/-- Aggregate interpolation for any jointly measurable endpoint vector on
an arbitrary fresh random tape. The complete preparation parameter remains
available to the endpoint generator. Only the original grid-point projection
is iid; no independence among generated endpoints is required. The local
fiber bound is a conditional sum of charges, and includes rejected proposals. -/
theorem endpoint_vector_interpolation_probability
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
      {p | BadRecordedUnion μ normalizer errorDomain
        (sorted (augmented permanent (samples p.1))) (points p) b} ≤
      ENNReal.ofReal (2 * ((Fintype.card Row : ℝ) - 1) * Λ * (1 + b) /
        (b * (sampleCount + 1 : ℕ))) := by
  let F := normalizedCumulative μ normalizer errorDomain
  let L := domainCumulative volume errorDomain
  let pointCharge : (Fin sampleCount → ℝ) → ℝ → ℝ≥0∞ := immutableCharge F L permanent
  let u : Parameter → ℝ → ℝ≥0∞ := fun p => pointCharge (samples p)
  let charge (p : Parameter × Draw) := ∑ j, u p.1 (points p j)
  have hF : ∀ i, Measurable (F i) := normalizedCumulative_measurable _ normalizer errorDomain
  have hL : Measurable L := domainCumulative_measurable volume errorDomain
  have hpoint : Measurable (Function.uncurry pointCharge) := immutableCharge_measurable F hF L hL permanent
  have hu : Measurable (Function.uncurry u) :=
    charge_pullback_measurable pointCharge hpoint samples hsamples.measurable
  have hcharge : Measurable charge := vector_charge_measurable u hu points hpoints
  have hvalidPoints : ∀ᵐ points ∂Measure.pi (fun _ : Fin sampleCount => sampleLaw), ValidSamples points := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin sampleCount => sampleLaw) i).quasiMeasurePreserving.ae hsupport
  have hvalid : ∀ᵐ p ∂parameterLaw, ValidSamples (samples p) := hsamples.quasiMeasurePreserving.ae hvalidPoints
  have hlocal : ∀ᵐ p ∂parameterLaw,
      (∫⁻ draw, charge (p, draw) ∂drawLaw) ≤ ENNReal.ofReal Λ * ∫⁻ z, u p z ∂sampleLaw := by
    filter_upwards [hfiber, hvalid] with p hp hv
    exact hp (u p) (charge_section_measurable u hu p)
      (immutable_charge_zero μ normalizer errorDomain permanent hpermanent (samples p) hv)
  have hproject : (∫⁻ p, ∫⁻ z, u p z ∂sampleLaw ∂parameterLaw) =
      ∫⁻ samples, ∫⁻ z, pointCharge samples z ∂sampleLaw
        ∂Measure.pi (fun _ : Fin sampleCount => sampleLaw) :=
    charge_lintegral_projection parameterLaw (Measure.pi (fun _ : Fin sampleCount => sampleLaw))
      sampleLaw samples hsamples pointCharge hpoint
  have hmean : (∫⁻ p, charge p ∂parameterLaw.prod drawLaw) ≤
      ENNReal.ofReal (Λ * (2 * ((Fintype.card Row : ℝ) - 1) / (sampleCount + 1 : ℕ))) := by
    rw [lintegral_prod charge hcharge.aemeasurable]
    calc
      _ ≤ ∫⁻ p, ENNReal.ofReal Λ * ∫⁻ z, u p z ∂sampleLaw ∂parameterLaw := lintegral_mono_ae hlocal
      _ = ENNReal.ofReal Λ * ∫⁻ p, ∫⁻ z, u p z ∂sampleLaw ∂parameterLaw :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal Λ * ∫⁻ samples, ∫⁻ z, pointCharge samples z ∂sampleLaw
          ∂Measure.pi (fun _ : Fin sampleCount => sampleLaw) := by rw [hproject]
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (2 * ((Fintype.card Row : ℝ) - 1) / (sampleCount + 1 : ℕ)) := by
        apply mul_le_mul' le_rfl
        exact immutableCharge_integrated_bound F hF L
          (domainCumulative_monotone volume errorDomain (domain_volume_finite errorDomain)) hL
          (normalizedCumulative_flat _ normalizer errorDomain) permanent sampleLaw hsupport
      _ = _ := (ENNReal.ofReal_mul hΛ).symm
  have hproductValid : ∀ᵐ p ∂parameterLaw.prod drawLaw, ValidSamples (samples p.1) :=
    measurePreserving_fst.quasiMeasurePreserving.ae hvalid
  have hbad : ∀ᵐ p ∂parameterLaw.prod drawLaw,
      BadRecordedUnion μ normalizer errorDomain
        (sorted (augmented permanent (samples p.1))) (points p) b →
      ENNReal.ofReal (b / (1 + b)) ≤ charge p := by
    filter_upwards [hproductValid] with p hp
    intro hbad
    have hzero : sorted (augmented permanent (samples p.1)) 0 = 0 :=
      first_eq_zero _ (augmented_nonneg permanent (samples p.1) hpermanent (fun i => (hp i).1))
        ⟨0, by simp [augmented]⟩
    have heq : (fun z => ENNReal.ofReal (physicalMaximum μ normalizer errorDomain
        (sorted (augmented permanent (samples p.1))) z)) = u p.1 := by
      funext z
      exact congrArg ENNReal.ofReal
        (linearMaximum_eq_physical μ normalizer errorDomain _ (sorted_monotone _) hzero z).symm
    have h := badRecordedUnion_implies_charge μ normalizer errorDomain
      (sorted (augmented permanent (samples p.1))) (sorted_monotone _) hzero (points p) b hb hbad
    change ENNReal.ofReal (b / (1 + b)) ≤ ∑ j,
      (fun z => ENNReal.ofReal (physicalMaximum μ normalizer errorDomain
        (sorted (augmented permanent (samples p.1))) z)) (points p j) at h
    rw [heq] at h
    exact h
  have h := common_lintegral_probability_ae (parameterLaw.prod drawLaw) charge hcharge.aemeasurable
    {p | BadRecordedUnion μ normalizer errorDomain
      (sorted (augmented permanent (samples p.1))) (points p) b}
    (Λ * (2 * ((Fintype.card Row : ℝ) - 1) / (sampleCount + 1 : ℕ))) b hb hmean hbad
  convert h using 1
  congr 1
  field_simp

end EnvyFreeResearch.Full.UpperSnapshotEndpointAggregate
