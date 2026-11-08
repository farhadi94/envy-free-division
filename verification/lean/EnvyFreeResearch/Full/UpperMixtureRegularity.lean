import EnvyFreeResearch.Full.UpperMixtureSampling

/-! Probability, atomlessness and physical support of the actual normalized
mixture used by the original finite-query sampler. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace EnvyFreeResearch.Full.UpperMixtureSampling

open UpperRecordedDomain

variable {n : ℕ} {Agent : Type*} [Fintype Agent] [Nonempty Agent]
  [MeasurableSpace Agent] [MeasurableSingletonClass Agent]

theorem mixture_probability (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    (active : Agent → Fin n) (cells : List Component)
    (hpositive : ∀ a, 0 < (μ (active a)).real (domain cells)) :
    IsProbabilityMeasure (mixture μ active cells) := by
  have hcond (a : Agent) : IsProbabilityMeasure (cond (μ (active a)) (domain cells)) :=
    cond_isProbabilityMeasure (by
      have h := hpositive a
      contrapose! h
      simp [measureReal_def, h])
  letI := hcond
  constructor
  simp only [mixture, Measure.smul_apply, Measure.finsetSum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

instance mixture_nullSingleton (μ : Fin n → Measure ℝ) [∀ i, NullSingletonClass (μ i)]
    (active : Agent → Fin n) (cells : List Component) : NullSingletonClass (mixture μ active cells) := by
  constructor
  intro x
  have hz (a : Agent) : (μ (active a)) ({x} ∩ domain cells) = 0 :=
    measure_mono_null inter_subset_left (measure_singleton x)
  simp [mixture, ProbabilityTheory.cond, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.restrict_apply (measurableSet_singleton x), hz]

theorem mixture_supported (μ : Fin n → Measure ℝ) (active : Agent → Fin n) (cells : List Component) :
    ∀ᵐ x ∂mixture μ active cells, x ∈ Icc (0 : ℝ) 1 := by
  have hc (a : Agent) : ∀ᵐ x ∂cond (μ (active a)) (domain cells), x ∈ Icc (0 : ℝ) 1 :=
    ae_cond_of_forall_mem (domain_measurable cells) (fun _ hx => domain_subset_unit cells hx)
  have hz (a : Agent) : cond (μ (active a)) (domain cells) {x | ¬x ∈ Icc (0 : ℝ) 1} = 0 :=
    ae_iff.mp (hc a)
  rw [ae_iff]
  simp only [mixture, Measure.smul_apply, Measure.finsetSum_apply, hz, Finset.sum_const_zero, smul_zero]

end EnvyFreeResearch.Full.UpperMixtureSampling
