import EnvyFreeResearch.Full.UpperGlobalProtocolPublic

/-! Every actual finite complete history is bounded by the public measurable
query/Cut totals, including the initial endpoint recordings. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperGlobalTape IntervalOracle
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]
  (oracle : AdaptiveOracle.Policy (Query n) ℝ)
  (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
  (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n)) (t : ℕ)
include horacle

theorem unit_history_query_bound :
    ((Phase.run (AdaptiveOracle.answer oracle) fallback chores
      (unitInitial (AdaptiveOracle.answer oracle)) t omega).history.length : ℝ≥0∞) ≤
      unitQueries (AdaptiveOracle.answer oracle) fallback chores omega := by
  have hp := UpperQueryLegality.answer_admissible _ oracle horacle
  obtain ⟨tail,_,hh,_,_,_⟩ := prefix_option_executes μ (Icc 0 1) chores _
    (unitInitial_valid μ (AdaptiveOracle.answer oracle) hp fallback chores) oracle horacle fallback omega t
  obtain ⟨boot,_,hb,hqb,_⟩ := UpperGlobalUnit.program_executes (AdaptiveOracle.answer oracle)
  have hi : (unitInitial (AdaptiveOracle.answer oracle)).history.length=2*n := by
    simpa only [unitInitial,Phase.history,hb] using hqb
  have hs := le_iSup (fun s => (runQueries (AdaptiveOracle.answer oracle) fallback chores
    (unitInitial (AdaptiveOracle.answer oracle)) omega s : ℝ≥0∞)) t
  change _ ≤ totalQueries _ _ _ _ _ at hs
  have hr : runQueries (AdaptiveOracle.answer oracle) fallback chores
      (unitInitial (AdaptiveOracle.answer oracle)) omega t=tail.length := by
    unfold runQueries
    rw [hh,List.length_append]
    omega
  rw [hr] at hs
  unfold unitQueries
  rw [hh,List.length_append,hi,Nat.cast_add]
  exact add_le_add le_rfl hs

theorem unit_history_cut_bound :
    (((Phase.run (AdaptiveOracle.answer oracle) fallback chores
      (unitInitial (AdaptiveOracle.answer oracle)) t omega).history.map Prod.fst).countP isCut : ℝ≥0∞) ≤
      unitCuts (AdaptiveOracle.answer oracle) fallback chores omega := by
  obtain ⟨boot,_,hb,_,hcb⟩ := UpperGlobalUnit.program_executes (AdaptiveOracle.answer oracle)
  have hi : ((unitInitial (AdaptiveOracle.answer oracle)).history.map Prod.fst).countP isCut=0 := by
    simpa only [unitInitial,Phase.history,hb] using hcb
  have hs := le_iSup (fun s => (runCuts (AdaptiveOracle.answer oracle) fallback chores
    (unitInitial (AdaptiveOracle.answer oracle)) omega s : ℝ≥0∞)) t
  simpa only [unitCuts,totalCuts,runCuts,hi,Nat.sub_zero] using hs

end EnvyFreeResearch.Full.UpperGlobalPhysical
