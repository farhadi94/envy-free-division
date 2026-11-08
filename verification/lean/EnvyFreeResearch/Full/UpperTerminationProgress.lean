import EnvyFreeResearch.Full.UpperExpectedRuntime

/-! Termination from infinite paid activity on unfinished runs. Query-free
normalization steps may occupy arbitrary stream indices. Their finite-progress
proof must supply the infinite-activity premise, not an every-step charge. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperExpectedRuntime
variable {Ω : Type*} [MeasurableSpace Ω]

theorem terminates_of_infinite_paid (μ : Measure Ω) (paid : Ω → ℝ≥0∞)
    (hpaid : Measurable paid) (finished : Ω → Prop)
    (bound : ℝ≥0∞) (hfinite : bound ≠ ∞)
    (hmean : (∫⁻ ω, paid ω ∂μ) ≤ bound)
    (hcontinue : ∀ ω, ¬ finished ω → paid ω = ∞) :
    ∀ᵐ ω ∂μ, finished ω := by
  have hfin := ae_lt_top hpaid (ne_top_of_le_ne_top hfinite hmean)
  filter_upwards [hfin] with ω hω
  by_contra hn
  exact (ne_of_lt hω) (hcontinue ω hn)

theorem two_class_infinite_paid_terminates (μ : Measure Ω)
    (a b : ℕ → Set Ω) (ha : ∀ t, MeasurableSet (a t))
    (hb : ∀ t, MeasurableSet (b t)) (finished : Ω → Prop)
    (bound : ℝ≥0∞) (hfinite : bound ≠ ∞)
    (hmean : (∫⁻ ω, attempts a ω + attempts b ω ∂μ) ≤ bound)
    (hcontinue : ∀ ω, ¬ finished ω → attempts a ω + attempts b ω = ∞) :
    ∀ᵐ ω ∂μ, finished ω :=
  terminates_of_infinite_paid μ _ ((attempts_measurable a ha).add (attempts_measurable b hb))
    finished bound hfinite hmean hcontinue

end EnvyFreeResearch.Full.UpperExpectedRuntime
