import EnvyFreeResearch.Full.UpperAggregateInterpolationLoopMeasurable
import EnvyFreeResearch.Full.UpperAggregateInterpolationStream
import EnvyFreeResearch.Full.UpperAggregateInterpolationNormalization

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

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperRecordedDomain UpperCircularStage UpperStageMeasurable UpperCorrectionExecution
  UpperCorrectionLoop UpperGridInterpolation UpperSortedGrid UpperGridSensitivity Chores

variable {n permanentCount sampleCount stageCount : ℕ}
  {Row Parameter : Type*} [Fintype Row] [Nonempty Row] [MeasurableSpace Parameter]

def ValidSamples (samples : Fin sampleCount → ℝ) : Prop := ∀ i, samples i ∈ Icc (0 : ℝ) 1

theorem charge_section_measurable {X : Type*} [MeasurableSpace X]
    (u : X → ℝ → ℝ≥0∞) (hu : Measurable (Function.uncurry u)) (x : X) : Measurable (u x) :=
  hu.comp (show Measurable (fun z : ℝ => (x, z)) from measurable_const.prodMk measurable_id)

theorem charge_pullback_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (u : Y → ℝ → ℝ≥0∞) (hu : Measurable (Function.uncurry u))
    (f : X → Y) (hf : Measurable f) :
    Measurable (fun p : X × ℝ => u (f p.1) p.2) :=
  hu.comp ((hf.comp measurable_fst).prodMk measurable_snd)

theorem charge_lintegral_projection {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (rho : Measure ℝ) [SFinite rho]
    (f : X → Y) (hf : MeasurePreserving f μ ν)
    (u : Y → ℝ → ℝ≥0∞) (hu : Measurable (Function.uncurry u)) :
    (∫⁻ x, ∫⁻ z, u (f x) z ∂rho ∂μ) = ∫⁻ y, ∫⁻ z, u y z ∂rho ∂ν :=
  hf.lintegral_comp hu.lintegral_prod_right'

set_option maxHeartbeats 800000 in
/-- The actual stopped-loop bound on a preparation-parameter × fresh-start
product. No reconstruction of history from sample points is assumed. The
error measures are restricted to `errorDomain`; the endpoint-law budget uses
`samplingBuffer`. Both domains are fixed before this iid point batch. -/
theorem actual_loop_interpolation_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Row → Fin n) (normalizer : Row → ℝ)
    (samplingBuffer errorDomain : List Component)
    (permanent : Fin permanentCount → ℝ) (hpermanent : ∀ i, 0 ≤ permanent i)
    (sampleLaw : Measure ℝ) [IsProbabilityMeasure sampleLaw] [NullSingletonClass sampleLaw]
    (hsupport : ∀ᵐ x ∂sampleLaw, x ∈ Icc (0 : ℝ) 1)
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw]
    (samples : Parameter → Fin sampleCount → ℝ)
    (hsamples : MeasurePreserving samples parameterLaw (Measure.pi (fun _ : Fin sampleCount => sampleLaw)))
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy) (hmeas : MeasurablePolicy policy)
    (jobs : Parameter → Fin stageCount → Job n) (hjobs : ∀ i, Measurable (fun p => jobs p i))
    (initial : Parameter → LoopState n) (hinitial : Measurable initial)
    (lower : Parameter → Fin stageCount → ℝ)
    (hlower : ∀ p, ValidSamples (samples p) → ∀ i, 0 < lower p i)
    (Safe : Parameter → Fin (stageCount + 1) → LoopState n → Prop)
    (hpreserve : ∀ p, ValidSamples (samples p) → ∀ i state start, Safe p i.castSucc state →
      Safe p i.succ (loopTransition policy (jobs p) i state start))
    (hsupply : ∀ p, ValidSamples (samples p) → ∀ i state, Safe p i.castSucc state →
      state.stopped = false → WellFormed μ state.current ∧ domain state.current.cells ⊆ domain samplingBuffer ∧
        lower p i ≤ (μ (jobs p i).owner).real (domain state.current.cells))
    (hinitial_safe : ∀ p, ValidSamples (samples p) → Safe p 0 (initial p))
    (Λ b : ℝ) (hΛ : 0 ≤ Λ) (hb : 0 < b)
    (hbudget : ∀ p, ValidSamples (samples p) →
      (∑ i, (2 * ENNReal.ofReal (1 / lower p i)) •
        (μ (jobs p i).owner).restrict (domain samplingBuffer)) ≤ ENNReal.ofReal Λ • sampleLaw) :
    (parameterLaw.prod (Measure.pi (fun _ : Fin stageCount => (volume : Measure Start))))
      {p | BadRecordedUnion (fun i => μ (active i)) normalizer errorDomain
        (sorted (augmented permanent (samples p.1))) (loopPoint policy (jobs p.1) (initial p.1) p.2) b} ≤
      ENNReal.ofReal (2 * ((Fintype.card Row : ℝ) - 1) * Λ * (1 + b) /
        (b * (sampleCount + 1 : ℕ))) := by
  let F := normalizedCumulative (fun i => μ (active i)) normalizer errorDomain
  let L := domainCumulative volume errorDomain
  let pointCharge : (Fin sampleCount → ℝ) → ℝ → ℝ≥0∞ := immutableCharge F L permanent
  let u : Parameter → ℝ → ℝ≥0∞ := fun p => pointCharge (samples p)
  let starts := Measure.pi (fun _ : Fin stageCount => (volume : Measure Start))
  let charge (p : Parameter × (Fin stageCount → Start)) :=
    tapeTotal (loopTransition policy (jobs p.1))
      (fun i => proposalCharge policy (jobs p.1 i) (u p.1)) (initial p.1) p.2
  have hF : ∀ i, Measurable (F i) := normalizedCumulative_measurable _ normalizer errorDomain
  have hL : Measurable L := domainCumulative_measurable volume errorDomain
  have hpoint : Measurable (Function.uncurry pointCharge) := immutableCharge_measurable F hF L hL permanent
  have hu : Measurable (Function.uncurry u) :=
    charge_pullback_measurable pointCharge hpoint samples hsamples.measurable
  have hcharge : Measurable charge := loop_charge_joint_measurable policy hmeas jobs hjobs u hu initial hinitial
  have hvalidPoints : ∀ᵐ points ∂Measure.pi (fun _ : Fin sampleCount => sampleLaw), ValidSamples points := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin sampleCount => sampleLaw) i).quasiMeasurePreserving.ae hsupport
  have hvalid : ∀ᵐ p ∂parameterLaw, ValidSamples (samples p) := hsamples.quasiMeasurePreserving.ae hvalidPoints
  have hfiber : ∀ᵐ p ∂parameterLaw,
      (∫⁻ tape, charge (p, tape) ∂starts) ≤ ENNReal.ofReal Λ * ∫⁻ z, u p z ∂sampleLaw := by
    filter_upwards [hvalid] with p hp
    have hpmeas : Measurable (u p) := charge_section_measurable u hu p
    exact loop_endpoint_expectation μ policy hpolicy hmeas (jobs p) (u p) hpmeas
      (domain samplingBuffer) (lower p) (hlower p hp) (Safe p) (hpreserve p hp)
      (hsupply p hp) (initial p) (hinitial_safe p hp) sampleLaw (ENNReal.ofReal Λ) (hbudget p hp)
  have hproject : (∫⁻ p, ∫⁻ z, u p z ∂sampleLaw ∂parameterLaw) =
      ∫⁻ points, ∫⁻ z, pointCharge points z ∂sampleLaw
        ∂Measure.pi (fun _ : Fin sampleCount => sampleLaw) :=
    charge_lintegral_projection parameterLaw (Measure.pi (fun _ : Fin sampleCount => sampleLaw))
      sampleLaw samples hsamples pointCharge hpoint
  have hmean : (∫⁻ p, charge p ∂parameterLaw.prod starts) ≤
      ENNReal.ofReal (Λ * (2 * ((Fintype.card Row : ℝ) - 1) / (sampleCount + 1 : ℕ))) := by
    rw [lintegral_prod charge hcharge.aemeasurable]
    calc
      _ ≤ ∫⁻ p, ENNReal.ofReal Λ * ∫⁻ z, u p z ∂sampleLaw ∂parameterLaw := lintegral_mono_ae hfiber
      _ = ENNReal.ofReal Λ * ∫⁻ p, ∫⁻ z, u p z ∂sampleLaw ∂parameterLaw :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal Λ * ∫⁻ points, ∫⁻ z, pointCharge points z ∂sampleLaw
          ∂Measure.pi (fun _ : Fin sampleCount => sampleLaw) := by rw [hproject]
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (2 * ((Fintype.card Row : ℝ) - 1) / (sampleCount + 1 : ℕ)) := by
        apply mul_le_mul' le_rfl
        exact immutableCharge_integrated_bound F hF L
          (domainCumulative_monotone volume errorDomain (domain_volume_finite errorDomain)) hL
          (normalizedCumulative_flat _ normalizer errorDomain) permanent sampleLaw hsupport
      _ = _ := (ENNReal.ofReal_mul hΛ).symm
  have hproductValid : ∀ᵐ p ∂parameterLaw.prod starts, ValidSamples (samples p.1) :=
    measurePreserving_fst.quasiMeasurePreserving.ae hvalid
  have hbad : ∀ᵐ p ∂parameterLaw.prod starts,
      BadRecordedUnion (fun i => μ (active i)) normalizer errorDomain
        (sorted (augmented permanent (samples p.1))) (loopPoint policy (jobs p.1) (initial p.1) p.2) b →
      ENNReal.ofReal (b / (1 + b)) ≤ charge p := by
    filter_upwards [hproductValid] with p hp
    intro hbad
    have hzero : sorted (augmented permanent (samples p.1)) 0 = 0 :=
      first_eq_zero _ (augmented_nonneg permanent (samples p.1) hpermanent (fun i => (hp i).1))
        ⟨0, by simp [augmented]⟩
    have heq : (fun z => ENNReal.ofReal (physicalMaximum (fun i => μ (active i)) normalizer errorDomain
        (sorted (augmented permanent (samples p.1))) z)) = u p.1 := by
      funext z
      exact congrArg ENNReal.ofReal
        (linearMaximum_eq_physical (fun i => μ (active i)) normalizer errorDomain _ (sorted_monotone _) hzero z).symm
    have h := loop_badRecordedUnion_implies_charge (fun i => μ (active i)) normalizer errorDomain
      (sorted (augmented permanent (samples p.1))) (sorted_monotone _) hzero policy (jobs p.1) (initial p.1)
      p.2 b hb hbad
    rw [heq] at h
    exact h
  have h := common_lintegral_probability_ae (parameterLaw.prod starts) charge hcharge.aemeasurable
    {p | BadRecordedUnion (fun i => μ (active i)) normalizer errorDomain
      (sorted (augmented permanent (samples p.1))) (loopPoint policy (jobs p.1) (initial p.1) p.2) b}
    (Λ * (2 * ((Fintype.card Row : ℝ) - 1) / (sampleCount + 1 : ℕ))) b hb hmean hbad
  convert h using 1
  congr 1
  field_simp

end EnvyFreeResearch.Full.UpperAggregateInterpolation
