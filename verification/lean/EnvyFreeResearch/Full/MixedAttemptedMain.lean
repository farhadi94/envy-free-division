import EnvyFreeResearch.Full.MixedPhysicalMain
import EnvyFreeResearch.Full.AttemptedQueries

/-! Public mixed lower bounds for attempted calls, including illegal calls
and all unsuccessful or nonreturning executions in the expectation. -/

noncomputable section
namespace EnvyFreeResearch.Full.MixedAttemptedMain
open Set MeasureTheory OracleProtocol AttemptedQueries MixedPhysicalMain IntervalAllocation
open scoped ENNReal

variable {Agent Ω : Type*}

def expectedAttempts [MeasurableSpace Ω] (μ : Measure Ω) (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent)) (I : Input Agent) : ℝ≥0∞ :=
  ∫⁻ ω, (attemptedCost next (oracle rule I) ω [] : ℝ≥0∞) ∂μ

theorem expectedCost_le_expectedAttempts [MeasurableSpace Ω] (μ : Measure Ω) (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent)) (I : Input Agent) :
    expectedCost μ rule next I ≤ expectedAttempts μ rule next I :=
  lintegral_mono (fun ω => ENat.toENNReal_mono (queryCost_le_attemptedCost next (oracle rule I) ω []))

theorem attempted_expectations_unbounded
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (rule : RootRule) (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (base : Agent) (α ε p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hε : ε < α) (hp : 0 < p)
    (hruns : ∀ I : Input Agent, ∀ fuel,
      Measurable (fun ω => run next (oracle rule I) ω fuel []))
    (hsuccess : ∀ I : Input Agent, ENNReal.ofReal p ≤ μ (success rule next I α ε)) :
    (⨆ I : Input Agent, expectedAttempts μ rule next I) = ∞ := by
  apply top_unique
  rw [← expected_queries_unbounded rule next base α ε p hn hα hε hp hruns hsuccess]
  exact iSup_mono (expectedCost_le_expectedAttempts μ rule next)

theorem relative_attempted_expectations_unbounded
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (rule : RootRule) (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (Allocation Agent))
    (base : Agent) (α p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hα1 : α ≤ 1) (hp : 0 < p)
    (hruns : ∀ I : Input Agent, ∀ fuel,
      Measurable (fun ω => run next (oracle rule I) ω fuel []))
    (hsuccess : ∀ I : Input Agent, ENNReal.ofReal p ≤ μ (relativeSuccess rule next I α)) :
    (⨆ I : Input Agent, expectedAttempts μ rule next I) = ∞ := by
  apply top_unique
  rw [← relative_expected_queries_unbounded rule next base α p hn hα hα1 hp hruns hsuccess]
  exact iSup_mono (expectedCost_le_expectedAttempts μ rule next)

end EnvyFreeResearch.Full.MixedAttemptedMain
