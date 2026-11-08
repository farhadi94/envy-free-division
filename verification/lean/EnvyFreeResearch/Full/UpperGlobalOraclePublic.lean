import EnvyFreeResearch.Full.UpperGlobalOracleExecutionUnit
import EnvyFreeResearch.Full.UpperGlobalOracleNextMeasurable
import EnvyFreeResearch.Full.AdaptiveOracleReturnedCostSup
import EnvyFreeResearch.Full.UpperGlobalProtocolCostMeasurable

/-! The randomized exact EF theorem for one Borel ordinary-query protocol.
Its costs are the actual suprema of answered-query counts over all fuel bounds,
not bounds on a family of independent finite-prefix executions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperGlobalTape UpperStageMeasurable OracleProtocol
open UpperGlobalRun.OracleNext
variable {n : ℕ}

def SingleProtocolOutputCorrect (μ : Fin n → Measure ℝ)
    (oracle : AdaptiveOracle.Policy (Query n) ℝ) (fallback : Fin n) (chores : Bool)
    (omega : Stream (Universal n)) : Prop :=
  ∃ trace a, AdaptiveOracle.run (next fallback chores) oracle omega trace.length []=⟨trace,.returned (.done a)⟩ ∧
    Pairwise (fun i j => Disjoint (UpperGlobalUnit.share (UpperGlobalUnit.output a) i)
      (UpperGlobalUnit.share (UpperGlobalUnit.output a) j)) ∧
    (⋃j,UpperGlobalUnit.share (UpperGlobalUnit.output a) j)=Icc 0 1 ∧
    GlobalCompletion.EnvyFree (if chores then .chore else .cake)
      (fun i j => (μ i).real (UpperGlobalUnit.share (UpperGlobalUnit.output a) j))

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (hmeas : MeasurablePolicy (AdaptiveOracle.answer oracle)) (fallback : Fin n) (chores : Bool)
include horacle hmeas

theorem single_protocol_actual_costs_ae :
    ∀ᵐ omega ∂streamLaw (universalLaw n),
      AdaptiveOracle.queryCost (next fallback chores) oracle omega [] ≤
        unitQueries (AdaptiveOracle.answer oracle) fallback chores omega ∧
      AdaptiveOracle.markedCost isCut (next fallback chores) oracle omega [] ≤
        unitCuts (AdaptiveOracle.answer oracle) fallback chores omega := by
  filter_upwards [single_protocol_output_almost_sure μ oracle horacle hmeas fallback chores] with omega h
  obtain ⟨trace,a,hrun,hq,hc,_⟩ := h
  rw [AdaptiveOracle.returned_queryCost _ _ _ _ _ _ _ hrun,
    AdaptiveOracle.returned_markedCost isCut _ _ _ _ _ _ _ hrun]
  exact ⟨hq,hc⟩

theorem randomized_exact_envy_free_oracle :
    Measurable (Function.uncurry (next fallback chores)) ∧
    (∀ᵐ omega ∂streamLaw (universalLaw n), SingleProtocolOutputCorrect μ oracle fallback chores omega) ∧
    (∫⁻ omega, AdaptiveOracle.queryCost (next fallback chores) oracle omega [] ∂streamLaw (universalLaw n)) ≤
      ENNReal.ofReal ((100*UpperGlobalBounds.sampleConstant)*(n:ℝ)^21*
        (Real.log (2*(n:ℝ))/Real.log 2)^2) ∧
    (∫⁻ omega, AdaptiveOracle.markedCost isCut (next fallback chores) oracle omega [] ∂streamLaw (universalLaw n)) ≤
      ENNReal.ofReal ((49*UpperGlobalBounds.sampleConstant)*(n:ℝ)^20*
        (Real.log (2*(n:ℝ))/Real.log 2)^2) := by
  have hmacro := randomized_exact_envy_free_polynomial μ oracle horacle hmeas fallback chores
  have hcost := single_protocol_actual_costs_ae μ oracle horacle hmeas fallback chores
  refine ⟨next_measurable fallback chores,?_,?_,?_⟩
  · filter_upwards [single_protocol_output_almost_sure μ oracle horacle hmeas fallback chores] with omega h
    obtain ⟨trace,a,hrun,_,_,hEF⟩ := h
    exact ⟨trace,a,hrun,hEF⟩
  · exact (lintegral_mono_ae (hcost.mono (fun _ h => h.1))).trans hmacro.2.1
  · exact (lintegral_mono_ae (hcost.mono (fun _ h => h.2))).trans hmacro.2.2

end EnvyFreeResearch.Full.UpperGlobalPhysical
