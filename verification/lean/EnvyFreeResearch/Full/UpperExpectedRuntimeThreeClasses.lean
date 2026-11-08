import EnvyFreeResearch.Full.UpperExpectedRuntimeBudget

/-! Three paid primitive classes share two pathwise successful-call budgets.
All counts are unconditional extended integrals, including rejected attempts. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperExpectedRuntime
variable {Ω : Type*} [MeasurableSpace Ω]

theorem attempts_le_success_integral (μ : Measure Ω)
    (paid success : ℕ → Set Ω) (hp : ∀ t, MeasurableSet (paid t))
    (hs : ∀ t, MeasurableSet (success t)) (factor : ℝ≥0∞)
    (hmean : ∀ t, μ (paid t) ≤ factor * μ (success t)) :
    (∫⁻ ω, attempts paid ω ∂μ) ≤ factor * ∫⁻ ω, attempts success ω ∂μ := by
  unfold attempts
  rw [lintegral_tsum (fun t => (measurable_const.indicator (hp t)).aemeasurable),
    lintegral_tsum (fun t => (measurable_const.indicator (hs t)).aemeasurable)]
  simp only [lintegral_indicator_const (hp _),lintegral_indicator_const (hs _),one_mul]
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hmean

theorem three_class_attempt_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (paid0 paid1 paid2 success0 success1 success2 : ℕ → Set Ω)
    (hp0 : ∀ t, MeasurableSet (paid0 t)) (hp1 : ∀ t, MeasurableSet (paid1 t))
    (hp2 : ∀ t, MeasurableSet (paid2 t)) (hs0 : ∀ t, MeasurableSet (success0 t))
    (hs1 : ∀ t, MeasurableSet (success1 t)) (hs2 : ∀ t, MeasurableSet (success2 t))
    (K : ℝ≥0∞)
    (hm0 : ∀ t, μ (paid0 t) ≤ 4 * μ (success0 t))
    (hm1 : ∀ t, μ (paid1 t) ≤ (64/63 : ℝ≥0∞) * μ (success1 t))
    (hm2 : ∀ t, μ (paid2 t) ≤ (64/63 : ℝ≥0∞) * μ (success2 t))
    (hb0 : ∀ ω, attempts success0 ω ≤ K)
    (hb12 : ∀ ω, attempts success1 ω + attempts success2 ω ≤ 3*K) :
    (∫⁻ ω, attempts paid0 ω + attempts paid1 ω + attempts paid2 ω ∂μ) ≤ 8*K := by
  have h0 := attempts_le_success_integral μ paid0 success0 hp0 hs0 4 hm0
  have h1 := attempts_le_success_integral μ paid1 success1 hp1 hs1 (64/63) hm1
  have h2 := attempts_le_success_integral μ paid2 success2 hp2 hs2 (64/63) hm2
  have hi0 : (∫⁻ ω, attempts success0 ω ∂μ) ≤ K := by
    calc
      _ ≤ ∫⁻ _ω, K ∂μ := lintegral_mono hb0
      _ = K := by simp
  have hi12 : (∫⁻ ω, attempts success1 ω ∂μ) + (∫⁻ ω, attempts success2 ω ∂μ) ≤ 3*K := by
    rw [← lintegral_add_left (attempts_measurable success1 hs1)]
    calc
      _ ≤ ∫⁻ _ω, 3*K ∂μ := lintegral_mono hb12
      _ = 3*K := by simp
  rw [lintegral_add_left (f := fun ω => attempts paid0 ω + attempts paid1 ω)
      (g := attempts paid2) ((attempts_measurable paid0 hp0).add (attempts_measurable paid1 hp1)),
    lintegral_add_left (attempts_measurable paid0 hp0)]
  calc
    _ ≤ 4*(∫⁻ ω, attempts success0 ω ∂μ) +
        (64/63 : ℝ≥0∞)*(∫⁻ ω, attempts success1 ω ∂μ) +
        (64/63 : ℝ≥0∞)*(∫⁻ ω, attempts success2 ω ∂μ) := add_le_add (add_le_add h0 h1) h2
    _ = 4*(∫⁻ ω, attempts success0 ω ∂μ) + (64/63 : ℝ≥0∞)*
        ((∫⁻ ω, attempts success1 ω ∂μ)+(∫⁻ ω, attempts success2 ω ∂μ)) := by ring
    _ ≤ 4*K + (64/63 : ℝ≥0∞)*(3*K) := by gcongr
    _ = (4+(64/63 : ℝ≥0∞)*3)*K := by ring
    _ ≤ 8*K := by
      have hn : (4+(64/63 : ℝ≥0∞)*3) ≤ 8 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
        norm_num [ENNReal.toReal_mul,ENNReal.toReal_div]
      gcongr

end EnvyFreeResearch.Full.UpperExpectedRuntime
