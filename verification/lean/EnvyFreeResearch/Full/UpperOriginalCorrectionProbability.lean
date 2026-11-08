import EnvyFreeResearch.Full.UpperPreparedCorrectionProbability
import EnvyFreeResearch.Full.UpperCorrectionRejectionMeasurable

/-! Outer label averaging of the actual prepared correction program.
Each label fiber fixes its own analytic reserve before the original sample
parameter is integrated. The final Borel event is the real rejection bit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperOriginalCorrectionProbability

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperCorrectionSetup
  UpperCircularStage UpperStageMeasurable UpperPreparedEnvelopeMean UpperSortedGrid UpperGridInterpolation
  UpperCorrectionRejectionMeasurable

variable {n k permanentCount sampleCount : ℕ} [Nonempty (Fin k)]
  {Label X : Type*} [MeasurableSpace Label] [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
theorem probability_le (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (samplingBuffer : List Component) (errorDomain : Label → List Component)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain samplingBuffer))
    (permanent : Fin permanentCount → ℝ) (hpermanent : ∀ i, 0 ≤ permanent i)
    (sampleLaw : Measure ℝ) [IsProbabilityMeasure sampleLaw] [NullSingletonClass sampleLaw]
    (hsupport : ∀ᵐ x ∂sampleLaw, x ∈ Icc (0 : ℝ) 1)
    (hmixture : sampleLaw = UpperMixtureSampling.mixture μ active samplingBuffer)
    (labelLaw : Measure Label) [IsProbabilityMeasure labelLaw]
    (parameterLaw : Measure X) [IsProbabilityMeasure parameterLaw]
    (samples : X → Fin sampleCount → ℝ)
    (hsamples : MeasurePreserving samples parameterLaw (Measure.pi (fun _ : Fin sampleCount => sampleLaw)))
    (reserve : Label → X → State n) (hreserve : Measurable (Function.uncurry reserve))
    (hdomain : ∀ label x, domain (reserve label x).cells = domain (errorDomain label))
    (cuts : Label → X → Fin (permanentCount + sampleCount + 2) → ℝ)
    (hcuts : ∀ e, Measurable (fun p : Label × X => cuts p.1 p.2 e))
    (hgrid : ∀ label x, cuts label x = sorted (augmented permanent (samples x)))
    (t : Label → X → Fin k → ℝ) (ht : ∀ j, Measurable (fun p : Label × X => t p.1 p.2 j))
    (approved : Label → X → Bool) (happroved : Measurable (Function.uncurry approved))
    (eta lam N q b : ℝ) (heta : 0 ≤ eta) (hlam : 0 < lam) (hN : 0 ≤ N) (hq : 0 < q) (hb : 0 < b)
    (hsize : (k : ℝ)^2 ≤ lam / 2) (hquarter : b * N ≤ lam / 4)
    (hmargin : (k : ℝ) * lam * eta < 1 / 16)
    (selected : Label → X → Finset (Fin (permanentCount + sampleCount + 1)))
    (hchecks : ∀ label x, approved label x = true →
      Checks μ active (reserve label x) (cuts label x) (t label x) eta (selected label x) N)
    (hsubset : ∀ label x, approved label x = true → domain (reserve label x).cells ⊆ domain samplingBuffer)
    (hmass : ∀ label x, approved label x = true → ∀ i,
      q / 2 * (μ (active i)).real (domain samplingBuffer) ≤ (μ (active i)).real (domain (reserve label x).cells)) :
    (labelLaw.prod (parameterLaw.prod (Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle)))))
      {p | rejected policy active (reserve p.1 p.2.1) (cuts p.1 p.2.1) (t p.1 p.2.1)
        eta lam (approved p.1 p.2.1) p.2.2 = true} ≤
      ENNReal.ofReal (8 * ((k : ℝ) * eta) * N / lam) +
        ENNReal.ofReal (16 * (k : ℝ) * ((k : ℝ) - 1) * (1 + b) / (q * b * (sampleCount + 1 : ℕ))) := by
  let starts := Measure.pi (fun _ : Fin k => (volume : Measure UpperCircular.Circle))
  let failure (p : Label × (X × (Fin k → UpperCircular.Circle))) :=
    rejected policy active (reserve p.1 p.2.1) (cuts p.1 p.2.1) (t p.1 p.2.1)
      eta lam (approved p.1 p.2.1) p.2.2
  have hparam : Measurable (fun p : Label × (X × (Fin k → UpperCircular.Circle)) => (p.1, p.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hfailure : Measurable failure := rejected_measurable
    (X := Label × (X × (Fin k → UpperCircular.Circle))) policy hmeas active
    (fun p => reserve p.1 p.2.1) (fun p => cuts p.1 p.2.1) (fun p => t p.1 p.2.1) eta lam
    (fun p => approved p.1 p.2.1) (fun p => p.2.2) (hreserve.comp hparam)
    (fun e => (hcuts e).comp hparam) (fun j => (ht j).comp hparam) (happroved.comp hparam)
    (fun j => (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
  apply outer_average labelLaw (parameterLaw.prod starts) failure hfailure
  intro label
  have hsection : Measurable (fun x : X => (label, x)) := measurable_const.prodMk measurable_id
  have h := UpperPreparedCorrectionProbability.probability_le μ policy hpolicy hmeas active hinj
    samplingBuffer (errorDomain label) hpositive permanent hpermanent sampleLaw hsupport hmixture
    parameterLaw samples hsamples (reserve label) (hreserve.comp hsection) (hdomain label)
    (cuts label) (fun e => (hcuts e).comp hsection) (hgrid label) (t label) (fun j => (ht j).comp hsection)
    (approved label) (happroved.comp hsection) eta lam N q b heta hlam hN hq hb hsize hquarter hmargin
    (selected label) (hchecks label) (hsubset label) (hmass label)
  simpa only [failure, rejected_iff, starts] using h

end EnvyFreeResearch.Full.UpperOriginalCorrectionProbability
