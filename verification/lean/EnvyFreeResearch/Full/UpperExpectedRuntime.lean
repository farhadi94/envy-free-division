import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! Unconditional accounting for countably many adaptive attempts. Every
rejected attempt is charged. The protocol-specific hypotheses remain explicit. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace EnvyFreeResearch.Full.UpperExpectedRuntime
variable {Ω : Type*} [MeasurableSpace Ω]

def attempts (active : ℕ → Set Ω) (ω : Ω) : ℝ≥0∞ :=
  ∑' t, (active t).indicator (fun _ => (1 : ℝ≥0∞)) ω

theorem attempts_measurable (active : ℕ → Set Ω)
    (hactive : ∀ t, MeasurableSet (active t)) : Measurable (attempts active) :=
  Measurable.tsum (fun t => measurable_const.indicator (hactive t))

/-- Progress may depend on the entire preceding query history. No independence
between attempts or requests is assumed. -/
theorem attempts_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : ℕ → Set Ω) (hactive : ∀ t, MeasurableSet (active t))
    (progress : ℕ → Ω → ℝ≥0∞) (hprogress : ∀ t, Measurable (progress t))
    (factor budget : ℝ≥0∞)
    (hmean : ∀ t, μ (active t) ≤ factor * ∫⁻ ω, progress t ω ∂μ)
    (hbudget : ∀ ω, ∑' t, progress t ω ≤ budget) :
    (∫⁻ ω, attempts active ω ∂μ) ≤ factor * budget := by
  unfold attempts
  rw [lintegral_tsum (fun t => (measurable_const.indicator (hactive t)).aemeasurable)]
  simp only [lintegral_indicator_const (hactive _), one_mul]
  calc
    _ ≤ ∑' t, factor * ∫⁻ ω, progress t ω ∂μ := ENNReal.tsum_le_tsum hmean
    _ = factor * ∫⁻ ω, ∑' t, progress t ω ∂μ := by
      rw [ENNReal.tsum_mul_left, lintegral_tsum (fun t => (hprogress t).aemeasurable)]
    _ ≤ factor * budget := by
      gcongr
      calc
        _ ≤ ∫⁻ _ω, budget ∂μ := lintegral_mono hbudget
        _ = budget := by simp

/-- The bound is unconditional and does not presuppose integrability. -/
theorem total_cost_bound (μ : Measure Ω)
    (active : ℕ → Set Ω) (hactive : ∀ t, MeasurableSet (active t))
    (cost : Ω → ℝ≥0∞) (cap bound : ℝ≥0∞)
    (hcost : ∀ ω, cost ω ≤ cap * attempts active ω)
    (hcount : (∫⁻ ω, attempts active ω ∂μ) ≤ bound) :
    (∫⁻ ω, cost ω ∂μ) ≤ cap * bound := by
  calc
    _ ≤ ∫⁻ ω, cap * attempts active ω ∂μ := lintegral_mono hcost
    _ = cap * ∫⁻ ω, attempts active ω ∂μ :=
      lintegral_const_mul cap (attempts_measurable active hactive)
    _ ≤ cap * bound := by gcongr

theorem attempts_finite_ae (μ : Measure Ω)
    (active : ℕ → Set Ω) (hactive : ∀ t, MeasurableSet (active t))
    (bound : ℝ≥0∞) (hfinite : bound ≠ ∞)
    (hcount : (∫⁻ ω, attempts active ω ∂μ) ≤ bound) :
    ∀ᵐ ω ∂μ, attempts active ω < ∞ :=
  ae_lt_top (attempts_measurable active hactive) (ne_top_of_le_ne_top hfinite hcount)

/-- If an unfinished run always makes another trial, finite expected attempts
implies almost-sure termination. Exceptional zero-probability tapes are allowed. -/
theorem terminates_ae (μ : Measure Ω)
    (active : ℕ → Set Ω) (hactive : ∀ t, MeasurableSet (active t))
    (finished : Ω → Prop) (bound : ℝ≥0∞) (hfinite : bound ≠ ∞)
    (hcount : (∫⁻ ω, attempts active ω ∂μ) ≤ bound)
    (hcontinue : ∀ ω, ¬ finished ω → ∀ t, ω ∈ active t) :
    ∀ᵐ ω ∂μ, finished ω := by
  filter_upwards [attempts_finite_ae μ active hactive bound hfinite hcount] with ω hω
  by_contra hn
  have heq : attempts active ω = ∞ := by
    unfold attempts
    simp only [indicator_of_mem (hcontinue ω hn _)]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  exact (ne_of_lt hω) heq

end EnvyFreeResearch.Full.UpperExpectedRuntime
