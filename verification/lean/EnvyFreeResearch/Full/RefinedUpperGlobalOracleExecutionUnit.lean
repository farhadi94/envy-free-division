import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalOracleExecution
import EnvyFreeResearch.Full.RefinedUpperGlobalOracleStabilityNext

/-! Operational linkage from the actual macroexecution to one fixed ordinary
next-query protocol on the complete transcript and original random tape. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape UpperQueryPrograms Chores.QueryProgram OracleProtocol
open RefinedUpperGlobalRun.OracleNext
variable {n : ℕ}

theorem unit_prefix_next_run (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n)) (t : ℕ) (a : Anchor n)
    (hdone : Phase.run (AdaptiveOracle.answer oracle) fallback chores
      (unitInitial (AdaptiveOracle.answer oracle)) t omega=.done a) :
    ∃ trace, AdaptiveOracle.run (next fallback chores) oracle omega trace.length []=⟨trace,.returned (.done a)⟩ ∧
      (trace.length : ℝ≥0∞) ≤ unitQueries (AdaptiveOracle.answer oracle) fallback chores omega ∧
      ((trace.map Prod.fst).countP isCut : ℝ≥0∞) ≤ unitCuts (AdaptiveOracle.answer oracle) fallback chores omega := by
  obtain ⟨tr,he,hh,_,_⟩ := unitPrefix_executes μ oracle horacle fallback chores omega t
  rw [hdone] at he hh
  have hrun := executes_observable_run (next fallback chores) omega he
    (unitPrefixProgram fallback chores omega t) (by simp [Program.after]) rfl
    (fun history ho => next_eq_prefixAction fallback chores omega history t ho) tr.length le_rfl
  refine ⟨tr,hrun,?_,?_⟩
  · have hq := unit_history_query_bound μ oracle horacle fallback chores omega t
    rw [hdone,hh] at hq
    exact hq
  · have hc := unit_history_cut_bound μ oracle horacle fallback chores omega t
    rw [hdone,hh] at hc
    exact hc

theorem single_protocol_output_almost_sure (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (hmeas : UpperStageMeasurable.MeasurablePolicy (AdaptiveOracle.answer oracle))
    (fallback : Fin n) (chores : Bool) :
    ∀ᵐ omega ∂streamLaw (universalLaw n), ∃ trace a,
      AdaptiveOracle.run (next fallback chores) oracle omega trace.length []=⟨trace,.returned (.done a)⟩ ∧
      (trace.length : ℝ≥0∞) ≤ unitQueries (AdaptiveOracle.answer oracle) fallback chores omega ∧
      ((trace.map Prod.fst).countP isCut : ℝ≥0∞) ≤ unitCuts (AdaptiveOracle.answer oracle) fallback chores omega ∧
      Pairwise (fun i j => Disjoint (RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) i)
        (RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) j)) ∧
      (⋃j,RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) j)=Icc 0 1 ∧
      GlobalCompletion.EnvyFree (if chores then .chore else .cake)
        (fun i j => (μ i).real (RefinedUpperGlobalUnit.share (RefinedUpperGlobalUnit.output a) j)) := by
  filter_upwards [unit_output_almost_sure μ oracle horacle hmeas fallback chores] with omega hout
  obtain ⟨t,a,hdone,hEF⟩ := hout
  obtain ⟨tr,hrun,hq,hc⟩ := unit_prefix_next_run μ oracle horacle fallback chores omega t a hdone
  exact ⟨tr,a,hrun,hq,hc,hEF⟩

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
