import EnvyFreeResearch.Full.RefinedUpperEndpointExceptions
import EnvyFreeResearch.Full.RefinedUpperPreparationMixture

/-! Conversion from original-mixture bad mass to actual retained-domain
endpoint mass, including zero-cost exceptional endpoints. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperBadMass
open UpperRecordedDomain

theorem retained_augmented_mass {n k : ℕ} {Index : Type*} [Finite Index]
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (active : Fin k → Fin n) (origin : List Component) (T bad : Set ℝ) (grid : Index → ℝ)
    (hT : MeasurableSet T) (hsub : T ⊆ domain origin)
    (δ : ℝ≥0∞) (hbad : UpperMixtureSampling.mixture μ active origin bad ≤ δ) (j : Fin k) :
    ((μ (active j)).restrict T) (RefinedUpperEndpointExceptions.augment bad T grid) ≤
      ENNReal.ofReal ((μ (active j)).real (domain origin) * (k : ℝ)) * δ := by
  have hrow := RefinedUpperPreparation.row_event_le_card_mixture μ active origin j bad
  have hres : ((μ (active j)).restrict (domain origin)) bad =
      cond (μ (active j)) (domain origin) bad * (μ (active j)) (domain origin) := by
    rw [cond_mul_eq_inter (domain_measurable origin), Measure.restrict_apply' (domain_measurable origin)]
    rw [inter_comm]
  calc
    _ ≤ ((μ (active j)).restrict (domain origin)) bad :=
      RefinedUpperEndpointExceptions.restricted_bad_mass_le _ bad T (domain origin) grid hT hsub
    _ ≤ ((k : ℝ≥0∞) * δ) * (μ (active j)) (domain origin) := by
      rw [hres]
      gcongr
      apply hrow.trans
      simpa only [Fintype.card_fin] using (show (Fintype.card (Fin k) : ℝ≥0∞) * UpperMixtureSampling.mixture μ active origin bad ≤ (k : ℝ≥0∞) * δ by simp only [Fintype.card_fin]; gcongr)
    _ = _ := by
      rw [ENNReal.ofReal_mul (measureReal_nonneg), ofReal_measureReal]
      simp only [ENNReal.ofReal_natCast]
      ring

end EnvyFreeResearch.Full.RefinedUpperBadMass
