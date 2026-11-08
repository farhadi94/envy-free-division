import EnvyFreeResearch.Full.UpperExpectedRuntimeConditional

/-! Separate Snapshot and Repair/Shrink acceptance bounds give fewer than eight
expected full trials per reached global iteration. Successful-call budgets
remain explicit until the concrete global driver supplies them. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace EnvyFreeResearch.Full.UpperExpectedRuntime
variable {Ω : Type*} [MeasurableSpace Ω]

theorem two_class_attempt_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (snapshot other snapshotSuccess otherSuccess : ℕ → Set Ω)
    (hs : ∀ t, MeasurableSet (snapshot t)) (ho : ∀ t, MeasurableSet (other t))
    (hss : ∀ t, MeasurableSet (snapshotSuccess t))
    (hos : ∀ t, MeasurableSet (otherSuccess t)) (K : ℝ≥0∞)
    (hsmean : ∀ t, μ (snapshot t) ≤ 4 * μ (snapshotSuccess t))
    (homean : ∀ t, μ (other t) ≤ (64/63 : ℝ≥0∞) * μ (otherSuccess t))
    (hsbudget : ∀ ω, attempts snapshotSuccess ω ≤ K)
    (hobudget : ∀ ω, attempts otherSuccess ω ≤ 3*K) :
    (∫⁻ ω, attempts snapshot ω + attempts other ω ∂μ) ≤ 8*K := by
  have hb1 := attempts_bound μ snapshot hs
    (fun t => (snapshotSuccess t).indicator (fun _ => (1 : ℝ≥0∞)))
    (fun t => measurable_const.indicator (hss t)) 4 K
    (by simpa only [lintegral_indicator_const (hss _),one_mul] using hsmean) hsbudget
  have hb2 := attempts_bound μ other ho
    (fun t => (otherSuccess t).indicator (fun _ => (1 : ℝ≥0∞)))
    (fun t => measurable_const.indicator (hos t)) (64/63) (3*K)
    (by simpa only [lintegral_indicator_const (hos _),one_mul] using homean) hobudget
  rw [lintegral_add_left (attempts_measurable snapshot hs)]
  calc
    _ ≤ 4*K + (64/63 : ℝ≥0∞)*(3*K) := add_le_add hb1 hb2
    _ = (4+(64/63 : ℝ≥0∞)*3)*K := by ring
    _ ≤ 8*K := by
      have h : (4+(64/63 : ℝ≥0∞)*3) ≤ 8 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
      gcongr

/-- Both coordinate costs are capped on all trials, not merely accepted ones. -/
theorem query_cut_caps (μ : Measure Ω)
    (count : Ω → ℝ≥0∞) (hc : Measurable count)
    (queries cuts : Ω → ℝ≥0∞) (n m : ℕ)
    (hcount : (∫⁻ ω, count ω ∂μ) ≤ 8*(n : ℝ≥0∞)*(n-1 : ℕ))
    (hq : ∀ ω, queries ω ≤ (12 : ℝ≥0∞)*n*m*count ω)
    (hcuts : ∀ ω, cuts ω ≤ (6 : ℝ≥0∞)*m*count ω) :
    (∫⁻ ω, queries ω ∂μ) ≤ (96 : ℝ≥0∞)*n*n*(n-1 : ℕ)*m ∧
    (∫⁻ ω, cuts ω ∂μ) ≤ (48 : ℝ≥0∞)*n*(n-1 : ℕ)*m := by
  constructor
  · calc
      _ ≤ ∫⁻ ω, (12 : ℝ≥0∞)*n*m*count ω ∂μ := lintegral_mono hq
      _ = (12 : ℝ≥0∞)*n*m*∫⁻ ω, count ω ∂μ := lintegral_const_mul _ hc
      _ ≤ (12 : ℝ≥0∞)*n*m*(8*n*(n-1 : ℕ)) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ ∫⁻ ω, (6 : ℝ≥0∞)*m*count ω ∂μ := lintegral_mono hcuts
      _ = (6 : ℝ≥0∞)*m*∫⁻ ω, count ω ∂μ := lintegral_const_mul _ hc
      _ ≤ (6 : ℝ≥0∞)*m*(8*n*(n-1 : ℕ)) := by gcongr
      _ = _ := by ring

end EnvyFreeResearch.Full.UpperExpectedRuntime
