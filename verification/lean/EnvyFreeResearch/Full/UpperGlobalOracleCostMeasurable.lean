import EnvyFreeResearch.Full.UpperGlobalOraclePublic
import EnvyFreeResearch.Full.AdaptiveOracleReturnedCostTotalized

/-! The exact actual costs in the single-protocol main theorem are ordinary
random variables up to null sets under the existing answer-only Borel oracle
assumption. No measurable Option-policy or globally legal totalization is assumed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperGlobalTape UpperStageMeasurable OracleProtocol
open UpperGlobalRun.OracleNext
variable {n : ℕ}
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (hmeas : MeasurablePolicy (AdaptiveOracle.answer oracle)) (fallback : Fin n) (chores : Bool)
include horacle hmeas

theorem single_protocol_actual_costs_aemeasurable :
    AEMeasurable (fun omega => AdaptiveOracle.queryCost (next fallback chores) oracle omega [])
      (streamLaw (universalLaw n)) ∧
    AEMeasurable (fun omega => AdaptiveOracle.markedCost isCut (next fallback chores) oracle omega [])
      (streamLaw (universalLaw n)) := by
  have hreturn : ∀ᵐ omega ∂streamLaw (universalLaw n), ∃ fuel trace out,
      AdaptiveOracle.run (next fallback chores) oracle omega fuel []=⟨trace,.returned out⟩ := by
    filter_upwards [single_protocol_output_almost_sure μ oracle horacle hmeas fallback chores] with omega h
    obtain ⟨trace,a,hrun,_,_,_⟩ := h
    exact ⟨trace.length,trace,.done a,hrun⟩
  exact AdaptiveOracle.returned_costs_aemeasurable (next fallback chores) oracle 0 []
    (streamLaw (universalLaw n)) hreturn (next_measurable fallback chores) hmeas isCut isCut_measurable

theorem single_protocol_actual_costs_totalized_expectations :
    (∫⁻ omega, AdaptiveOracle.queryCost (next fallback chores) oracle omega [] ∂streamLaw (universalLaw n))=
      (∫⁻ omega, AdaptiveOracle.queryCost (next fallback chores)
        (AdaptiveOracle.totalizedPolicy 0 oracle) omega [] ∂streamLaw (universalLaw n)) ∧
    (∫⁻ omega, AdaptiveOracle.markedCost isCut (next fallback chores) oracle omega [] ∂streamLaw (universalLaw n))=
      ∫⁻ omega, AdaptiveOracle.markedCost isCut (next fallback chores)
        (AdaptiveOracle.totalizedPolicy 0 oracle) omega [] ∂streamLaw (universalLaw n) := by
  have hreturn : ∀ᵐ omega ∂streamLaw (universalLaw n), ∃ fuel trace out,
      AdaptiveOracle.run (next fallback chores) oracle omega fuel []=⟨trace,.returned out⟩ := by
    filter_upwards [single_protocol_output_almost_sure μ oracle horacle hmeas fallback chores] with omega h
    obtain ⟨trace,a,hrun,_,_,_⟩ := h
    exact ⟨trace.length,trace,.done a,hrun⟩
  exact AdaptiveOracle.returned_costs_lintegral_totalized (next fallback chores) oracle 0 []
    (streamLaw (universalLaw n)) hreturn isCut

end EnvyFreeResearch.Full.UpperGlobalPhysical
