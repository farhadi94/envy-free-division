import EnvyFreeResearch.Full.UpperGlobalProtocolRunExecution
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Actual issued query counts, read from the full execution history. Their
unbounded totals are dominated by the attempted-stage accounting series. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperGlobalTape IntervalOracle
variable {n : ℕ}

def runQueries (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) (t : ℕ) : ℕ :=
  (Phase.run policy fallback chores initial t omega).history.length-initial.history.length

def runCuts (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) (t : ℕ) : ℕ :=
  ((Phase.run policy fallback chores initial t omega).history.map Prod.fst).countP isCut-
    (initial.history.map Prod.fst).countP isCut

def totalQueries (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) : ℝ≥0∞ := ⨆ t, (runQueries policy fallback chores initial omega t : ℝ≥0∞)

def totalCuts (policy : Policy n) (fallback : Fin n) (chores : Bool) (initial : Phase n)
    (omega : Stream (Universal n)) : ℝ≥0∞ := ⨆ t, (runCuts policy fallback chores initial omega t : ℝ≥0∞)

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
    (initial : Phase n) (hinit : initial.Valid μ chores whole)
    (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (fallback : Fin n) (omega : Stream (Universal n))
include hinit horacle

theorem actual_prefix_counts (t : ℕ) :
    runQueries (AdaptiveOracle.answer oracle) fallback chores initial omega t ≤
      ∑ s ∈ Finset.range t, (Phase.run (AdaptiveOracle.answer oracle) fallback chores initial s omega).queryCap ∧
    runCuts (AdaptiveOracle.answer oracle) fallback chores initial omega t ≤
      ∑ s ∈ Finset.range t, (Phase.run (AdaptiveOracle.answer oracle) fallback chores initial s omega).cutCap := by
  obtain ⟨tr,_,hh,hq,hc,_⟩ := prefix_option_executes μ whole chores initial hinit oracle horacle fallback omega t
  unfold runQueries runCuts
  rw [hh,List.length_append,List.map_append,List.countP_append]
  simpa using And.intro hq hc

theorem actual_total_queries_le :
    totalQueries (AdaptiveOracle.answer oracle) fallback chores initial omega ≤
      ∑' s, ((Phase.run (AdaptiveOracle.answer oracle) fallback chores initial s omega).queryCap : ℝ≥0∞) := by
  apply iSup_le
  intro t
  have h := (actual_prefix_counts μ whole chores initial hinit oracle horacle fallback omega t).1
  calc
    (runQueries (AdaptiveOracle.answer oracle) fallback chores initial omega t : ℝ≥0∞) ≤
      ∑ s ∈ Finset.range t, ((Phase.run (AdaptiveOracle.answer oracle) fallback chores initial s omega).queryCap : ℝ≥0∞) := by exact_mod_cast h
    _ ≤ _ := ENNReal.sum_le_tsum _

theorem actual_total_cuts_le :
    totalCuts (AdaptiveOracle.answer oracle) fallback chores initial omega ≤
      ∑' s, ((Phase.run (AdaptiveOracle.answer oracle) fallback chores initial s omega).cutCap : ℝ≥0∞) := by
  apply iSup_le
  intro t
  have h := (actual_prefix_counts μ whole chores initial hinit oracle horacle fallback omega t).2
  calc
    (runCuts (AdaptiveOracle.answer oracle) fallback chores initial omega t : ℝ≥0∞) ≤
      ∑ s ∈ Finset.range t, ((Phase.run (AdaptiveOracle.answer oracle) fallback chores initial s omega).cutCap : ℝ≥0∞) := by exact_mod_cast h
    _ ≤ _ := ENNReal.sum_le_tsum _

end EnvyFreeResearch.Full.UpperGlobalPhysical
