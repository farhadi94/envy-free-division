import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolPublic

/-! Explicit polynomial-logarithmic public bounds for the actual randomized
exact EF protocol. The same theorem applies to cake and chores. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape UpperStageMeasurable IntervalOracle
variable {n : ℕ}

theorem randomized_exact_envy_free_polynomial (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (hmeas : MeasurablePolicy (AdaptiveOracle.answer oracle)) (fallback : Fin n) (chores : Bool) :
    (∀ᵐ omega ∂streamLaw (universalLaw n),
      UnitOutputCorrect μ (AdaptiveOracle.answer oracle) fallback chores omega) ∧
    (∫⁻ omega, unitQueries (AdaptiveOracle.answer oracle) fallback chores omega ∂streamLaw (universalLaw n)) ≤
      ENNReal.ofReal ((100*RefinedUpperGlobalBounds.sampleConstant)*(n:ℝ)^12*
        (Real.log (2*(n:ℝ))/Real.log 2)) ∧
    (∫⁻ omega, unitCuts (AdaptiveOracle.answer oracle) fallback chores omega ∂streamLaw (universalLaw n)) ≤
      ENNReal.ofReal ((49*RefinedUpperGlobalBounds.sampleConstant)*(n:ℝ)^11*
        (Real.log (2*(n:ℝ))/Real.log 2)) := by
  have h := randomized_exact_envy_free μ oracle horacle hmeas fallback chores
  have hn : 1 ≤ n := by have := fallback.isLt; omega
  refine ⟨h.1,h.2.1.trans ?_,h.2.2.trans ?_⟩
  · simpa only [ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal (RefinedUpperGlobalBounds.query_polynomial n hn)
  · simpa only [ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal (RefinedUpperGlobalBounds.cut_polynomial n hn)

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
