import EnvyFreeResearch.Full.UpperMixtureRegularity

/-! Each original normalized row is dominated by the actual sampling mixture. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open MeasureTheory ProbabilityTheory UpperRecordedDomain
open scoped BigOperators ENNReal
variable {n : ℕ} {Agent : Type*} [Fintype Agent]

/-- Domination is a measure inequality, so no measurability premise on the
exceptional event is necessary. Normalization uses the original buffer. -/
theorem row_le_card_mixture (μ : Fin n → Measure ℝ) (active : Agent → Fin n)
    (cells : List Component) (a : Agent) :
    cond (μ (active a)) (domain cells) ≤
      (Fintype.card Agent : ℝ≥0∞) • UpperMixtureSampling.mixture μ active cells := by
  letI : Nonempty Agent := ⟨a⟩
  have hc : (Fintype.card Agent : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [UpperMixtureSampling.mixture, smul_smul, ENNReal.mul_inv_cancel hc (ENNReal.natCast_ne_top _), one_smul]
  exact Finset.single_le_sum (f := fun b => cond (μ (active b)) (domain cells)) (fun b _ => by intro E; change (0 : ℝ≥0∞) ≤ _; exact bot_le) (Finset.mem_univ a)

theorem row_event_le_card_mixture (μ : Fin n → Measure ℝ) (active : Agent → Fin n)
    (cells : List Component) (a : Agent) (E : Set ℝ) :
    cond (μ (active a)) (domain cells) E ≤
      (Fintype.card Agent : ℝ≥0∞) * UpperMixtureSampling.mixture μ active cells E := by
  simpa only [Measure.smul_apply, smul_eq_mul] using row_le_card_mixture μ active cells a E

end EnvyFreeResearch.Full.RefinedUpperPreparation
