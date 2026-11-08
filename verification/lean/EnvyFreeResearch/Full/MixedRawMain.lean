import EnvyFreeResearch.Full.MixedAttemptedMain
import EnvyFreeResearch.Full.RawPartition
import EnvyFreeResearch.Full.OutputPostprocess

/-! The mixed lower bound for raw finite-cut output records, including
malformed returns, with the exact unconditional attempted-query count. -/

noncomputable section
namespace EnvyFreeResearch.Full.MixedRawMain
open Set MeasureTheory OracleProtocol AttemptedQueries MixedPhysicalMain MixedAttemptedMain
open IntervalAllocation
open scoped ENNReal Classical

variable {Agent Ω : Type*}

def success (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawPartition.Raw Agent))
    (I : Input Agent) (α ε : ℝ) : Set Ω :=
  {ω | ∃ fuel raw A, (run next (oracle rule I) ω fuel []).stop = .returned raw ∧
    RawPartition.decode raw = some A ∧ Fair I A α ε}

def expectedAttempts [MeasurableSpace Ω] (μ : Measure Ω) (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawPartition.Raw Agent))
    (I : Input Agent) : ℝ≥0∞ :=
  ∫⁻ ω, (attemptedCost next (oracle rule I) ω [] : ℝ≥0∞) ∂μ

theorem normalized_success (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawPartition.Raw Agent))
    (I : Input Agent) (α ε : ℝ) :
    MixedPhysicalMain.success rule (OutputPostprocess.normalized RawPartition.decode next) I α ε =
      success rule next I α ε := by
  ext ω
  constructor
  · rintro ⟨fuel,A,hret,hfair⟩
    obtain ⟨raw,hraw,hdecode⟩ := (OutputPostprocess.returned_normalized_iff
      RawPartition.decode next (oracle rule I) ω fuel [] A).mp hret
    exact ⟨fuel,raw,A,hraw,hdecode,hfair⟩
  · rintro ⟨fuel,raw,A,hraw,hdecode,hfair⟩
    exact ⟨fuel,A,(OutputPostprocess.returned_normalized_iff
      RawPartition.decode next (oracle rule I) ω fuel [] A).mpr ⟨raw,hraw,hdecode⟩,hfair⟩

theorem oracle_measurable [Fintype Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] (rule : RootRule) (I : Input Agent) :
    Measurable (oracle rule I) := by
  cases rule with
  | leftmost => exact MixedViews.actual_oracle_measurable _
  | rightmost => exact RightmostOracle.actual_oracle_measurable _

theorem attempted_expectations_unbounded
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawPartition.Raw Agent))
    (base : Agent) (α ε p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hε : ε < α) (hp : 0 < p)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (hsuccess : ∀ I : Input Agent, ENNReal.ofReal p ≤ μ (success rule next I α ε)) :
    (⨆ I : Input Agent, expectedAttempts μ rule next I) = ∞ := by
  let next' := OutputPostprocess.normalized RawPartition.decode next
  have hm := OutputPostprocess.normalized_measurable
    RawPartition.decode RawPartition.decode_measurable next hnext
  have hruns (I : Input Agent) (fuel : ℕ) :
      Measurable (fun ω => run next' (oracle rule I) ω fuel []) :=
    ProtocolMeasurable.measurable_run_at_history next' (oracle rule I) hm
      (oracle_measurable rule I) fuel []
  have hs (I : Input Agent) :
      ENNReal.ofReal p ≤ μ (MixedPhysicalMain.success rule next' I α ε) := by
    simpa only [next',normalized_success] using hsuccess I
  have h := MixedAttemptedMain.attempted_expectations_unbounded
    rule next' base α ε p hn hα hε hp hruns hs
  simpa only [MixedAttemptedMain.expectedAttempts,expectedAttempts,next',
    OutputPostprocess.attemptedCost_normalized] using h

def relativeSuccess (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawPartition.Raw Agent))
    (I : Input Agent) (α : ℝ) : Set Ω :=
  {ω | ∃ fuel raw A, (run next (oracle rule I) ω fuel []).stop = .returned raw ∧
    RawPartition.decode raw = some A ∧ MixedCorrespondence.RelativeEF I.rows A α}

theorem relative_success_eq [Fintype Agent] (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawPartition.Raw Agent))
    (I : Input Agent) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    relativeSuccess rule next I α = success rule next I α 0 := by
  ext ω
  simp only [relativeSuccess,success,mem_ofPred_eq,
    MixedPhysicalMain.relative_iff_fair I _ α hα hα1]

theorem relative_attempted_expectations_unbounded
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawPartition.Raw Agent))
    (base : Agent) (α p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hα1 : α ≤ 1) (hp : 0 < p)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (hsuccess : ∀ I : Input Agent, ENNReal.ofReal p ≤ μ (relativeSuccess rule next I α)) :
    (⨆ I : Input Agent, expectedAttempts μ rule next I) = ∞ := by
  apply attempted_expectations_unbounded rule next base α 0 p hn hα hα hp hnext
  intro I
  simpa only [relative_success_eq rule next I α hα hα1] using hsuccess I

end EnvyFreeResearch.Full.MixedRawMain
