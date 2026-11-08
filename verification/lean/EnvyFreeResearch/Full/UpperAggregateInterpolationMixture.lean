import EnvyFreeResearch.Full.UpperAggregateInterpolation
import EnvyFreeResearch.Full.UpperAggregateInterpolationHistory

/-! The exact manuscript correction-stage interpolation constant, with the
predictable measure budget derived from distinct recipients and raw supply. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperRecordedDomain UpperCircularStage UpperStageMeasurable UpperCorrectionExecution
  UpperCorrectionLoop UpperGridInterpolation UpperSortedGrid Chores

variable {n permanentCount sampleCount stageCount : ℕ}
  {Row Parameter : Type*} [Fintype Row] [Nonempty Row] [MeasurableSpace Parameter]

set_option maxHeartbeats 1600000 in
theorem actual_loop_mixture_interpolation_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Row → Fin n) (normalizer : Row → ℝ) (samplingBuffer errorDomain : List Component)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain samplingBuffer))
    (permanent : Fin permanentCount → ℝ) (hpermanent : ∀ i, 0 ≤ permanent i)
    (sampleLaw : Measure ℝ) [IsProbabilityMeasure sampleLaw] [NullSingletonClass sampleLaw]
    (hsupport : ∀ᵐ x ∂sampleLaw, x ∈ Icc (0 : ℝ) 1)
    (hmixture : sampleLaw = UpperMixtureSampling.mixture μ active samplingBuffer)
    (parameterLaw : Measure Parameter) [IsProbabilityMeasure parameterLaw]
    (samples : Parameter → Fin sampleCount → ℝ)
    (hsamples : MeasurePreserving samples parameterLaw (Measure.pi (fun _ : Fin sampleCount => sampleLaw)))
    (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy)
    (jobs : Parameter → Fin stageCount → Job n)
    (hjobs : ∀ i, Measurable (fun samples => jobs samples i))
    (recipient : Parameter → Fin stageCount → Row)
    (hinjective : ∀ parameter, ValidSamples (samples parameter) → Function.Injective (recipient parameter))
    (howner : ∀ parameter, ValidSamples (samples parameter) → ∀ i, (jobs parameter i).owner = active (recipient parameter i))
    (initial : Parameter → LoopState n) (hinitial : Measurable initial)
    (q b : ℝ) (hq : 0 < q) (hb : 0 < b)
    (Safe : Parameter → Fin (stageCount + 1) → LoopState n → Prop)
    (hpreserve : ∀ parameter, ValidSamples (samples parameter) → ∀ i state start, Safe parameter i.castSucc state →
      Safe parameter i.succ (loopTransition policy (jobs parameter) i state start))
    (hsupply : ∀ parameter, ValidSamples (samples parameter) → ∀ i state, Safe parameter i.castSucc state →
      state.stopped = false → WellFormed μ state.current ∧ domain state.current.cells ⊆ domain samplingBuffer ∧
        (q / 4) * (μ (jobs parameter i).owner).real (domain samplingBuffer) ≤
          (μ (jobs parameter i).owner).real (domain state.current.cells))
    (hinitial_safe : ∀ parameter, ValidSamples (samples parameter) → Safe parameter 0 (initial parameter)) :
    (parameterLaw.prod
      (Measure.pi (fun _ : Fin stageCount => (volume : Measure Start))))
      {p | BadRecordedUnion (fun i => μ (active i)) normalizer errorDomain
        (sorted (augmented permanent (samples p.1))) (loopPoint policy (jobs p.1) (initial p.1) p.2) b} ≤
      ENNReal.ofReal (16 * (Fintype.card Row : ℝ) * ((Fintype.card Row : ℝ) - 1) * (1 + b) /
        (q * b * (sampleCount + 1 : ℕ))) := by
  let lower (parameter : Parameter) (i : Fin stageCount) :=
    (q / 4) * (μ (jobs parameter i).owner).real (domain samplingBuffer)
  have hp (parameter : Parameter) (hs : ValidSamples (samples parameter)) (i : Fin stageCount) :
      0 < (μ (jobs parameter i).owner).real (domain samplingBuffer) := by
    rw [howner parameter hs i]
    exact hpositive _
  have hlower : ∀ parameter, ValidSamples (samples parameter) → ∀ i, 0 < lower parameter i :=
    fun parameter hs i => mul_pos (div_pos hq (by norm_num)) (hp parameter hs i)
  have hbudget (parameter : Parameter) (hs : ValidSamples (samples parameter)) :
      (∑ i, (2 * ENNReal.ofReal (1 / lower parameter i)) •
        (μ (jobs parameter i).owner).restrict (domain samplingBuffer)) ≤
      ENNReal.ofReal (8 * (Fintype.card Row : ℝ) / q) • sampleLaw := by
    calc
      _ = ∑ i, ENNReal.ofReal (8 / q) • cond (μ (jobs parameter i).owner) (domain samplingBuffer) := by
        apply Finset.sum_congr rfl
        intro i _
        exact two_endpoint_allowance_eq _ _ (hp parameter hs i) q hq
      _ = ∑ i, ENNReal.ofReal (8 / q) • cond (μ (active (recipient parameter i))) (domain samplingBuffer) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [howner parameter hs i]
      _ ≤ (ENNReal.ofReal (8 / q) * Fintype.card Row) • UpperMixtureSampling.mixture μ active samplingBuffer :=
        mixture_budget μ active samplingBuffer (recipient parameter) (hinjective parameter hs) q
      _ = _ := by
        rw [← hmixture]
        congr 1
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (div_nonneg (by norm_num) hq.le)]
        congr 1
        ring
  have h := actual_loop_interpolation_probability μ active normalizer samplingBuffer errorDomain permanent hpermanent
    sampleLaw hsupport parameterLaw samples hsamples policy hpolicy hmeas jobs hjobs initial hinitial lower hlower Safe
    hpreserve hsupply hinitial_safe (8 * (Fintype.card Row : ℝ) / q) b (by positivity) hb hbudget
  convert h using 1
  congr 1
  field_simp
  ring

end EnvyFreeResearch.Full.UpperAggregateInterpolation
