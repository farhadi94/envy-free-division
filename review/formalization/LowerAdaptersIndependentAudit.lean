import EnvyFreeResearch.Full.NonnegativeRawMain
import EnvyFreeResearch.Full.MixedIntervalMain

/-! Reviewer-owned checks for the lower-bound adapters.  No production
proof source is modified by this file. -/

noncomputable section
namespace LowerAdaptersIndependentAudit

open Set MeasureTheory
open EnvyFreeResearch.Full
open OracleProtocol ProtocolMeasurable AttemptedQueries
open scoped Classical ENNReal

theorem zero_record_count_invalid {Agent : Type*}
    (r : RawIntervalPartition.Raw Agent) (h : r.count = 0) :
    ¬ RawIntervalPartition.Valid r := by
  intro hv
  obtain ⟨k, hk, _, _⟩ := hv.2.2 (1 : ℚ) (by norm_num) (by norm_num)
  omega

theorem attempts_eq_determining_length {Q R O : Type*} (e : Execution Q R O) :
    attempts e = (determiningRequests e).length := by
  rw [determiningRequests_length]
  rfl

theorem attempts_measurable {Q R O : Type*}
    [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace O] :
    Measurable (attempts (Query := Q) (Reply := R) (Output := O)) := by
  convert (measurable_list_length.comp
    (NonnegativeMeasurableDetection.measurable_determiningRequests
      (Query := Q) (Reply := R) (Output := O))) using 1
  funext e
  exact attempts_eq_determining_length e

theorem attemptedCost_measurable_of_runs {T Q R O : Type*}
    [MeasurableSpace T] [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace O]
    (next : Protocol T Q R O) (oracle : Q → Option R) (history : History Q R)
    (hruns : ∀ fuel, Measurable (fun t => run next oracle t fuel history)) :
    Measurable (fun t => attemptedCost next oracle t history) := by
  have hlen (fuel : ℕ) : Measurable (fun t => attempts (run next oracle t fuel history)) :=
    attempts_measurable.comp (hruns fuel)
  have hle (n : ℕ) : MeasurableSet {t | attemptedCost next oracle t history ≤ (n : ℕ∞)} := by
    have heq : {t | attemptedCost next oracle t history ≤ (n : ℕ∞)} =
        ⋂ fuel, {t | attempts (run next oracle t fuel history) ≤ n} := by
      ext t
      simp [attemptedCost, iSup_le_iff]
    rw [heq]
    exact MeasurableSet.iInter (fun fuel => measurableSet_le (hlen fuel) measurable_const)
  apply ENat.measurable_iff.mpr
  intro n
  cases n with
  | zero =>
    change MeasurableSet {t | attemptedCost next oracle t history = (0 : ℕ∞)}
    simpa only [Nat.cast_zero, le_zero_iff] using hle 0
  | succ n =>
    have heq : (fun t => attemptedCost next oracle t history) ⁻¹' {(↑(n + 1) : ℕ∞)} =
        {t | attemptedCost next oracle t history ≤ ((n + 1 : ℕ) : ℕ∞)} ∩
          {t | attemptedCost next oracle t history ≤ (n : ℕ∞)}ᶜ := by
      ext t
      change attemptedCost next oracle t history = (↑(n + 1) : ℕ∞) ↔
        attemptedCost next oracle t history ≤ (↑(n + 1) : ℕ∞) ∧
          ¬ attemptedCost next oracle t history ≤ (↑n : ℕ∞)
      generalize attemptedCost next oracle t history = v
      induction v using ENat.recTopCoe with
      | top => simp only [ENat.top_ne_natCast, top_le_iff, ENat.natCast_ne_top, false_and]
      | coe k => simp only [ENat.natCast_inj, ENat.natCast_le_natCast]; omega
    rw [heq]
    exact (hle (n + 1)).inter (hle n).compl

theorem public_mixed_oracle_measurable {Agent : Type*}
    [Fintype Agent] [MeasurableSpace Agent] [MeasurableSingletonClass Agent]
    (rule : MixedPhysicalMain.RootRule) (I : MixedPhysicalMain.Input Agent) :
    Measurable (MixedPhysicalMain.oracle rule I) := by
  cases rule with
  | leftmost => exact MixedViews.actual_oracle_measurable _
  | rightmost => exact RightmostOracle.actual_oracle_measurable _

theorem public_raw_attemptedCost_measurable {Agent T : Type*}
    [Fintype Agent] [MeasurableSpace Agent] [MeasurableSingletonClass Agent]
    [MeasurableSpace T]
    (rule : MixedPhysicalMain.RootRule)
    (next : Protocol T (IntervalOracle.Query Agent) ℝ (RawIntervalPartition.Raw Agent))
    (hnext : Measurable (fun z : T × History (IntervalOracle.Query Agent) ℝ => next z.1 z.2))
    (I : MixedPhysicalMain.Input Agent) :
    Measurable (fun t => attemptedCost next (MixedPhysicalMain.oracle rule I) t []) :=
  attemptedCost_measurable_of_runs next (MixedPhysicalMain.oracle rule I) []
    (fun fuel => measurable_run_at_history next _ hnext
      (public_mixed_oracle_measurable rule I) fuel [])

theorem public_fair_measurable {Agent : Type*}
    [Fintype Agent] [MeasurableSpace Agent] [MeasurableSingletonClass Agent]
    (I : MixedPhysicalMain.Input Agent) (α ε : ℝ) :
    MeasurableSet {A : IntervalAllocation.Allocation Agent | MixedPhysicalMain.Fair I A α ε} := by
  have heq : {A : IntervalAllocation.Allocation Agent | MixedPhysicalMain.Fair I A α ε} =
      ⋂ i, ⋂ j, {A | α * MixedObstruction.value (I.rows i) (A.share j) -
        MixedObstruction.value (I.rows i) (A.share i) ≤ ε} := by
    ext A
    simp [MixedPhysicalMain.Fair]
  rw [heq]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    measurableSet_le (((MixedSuccess.physical_value_measurable (I.rows i) j).const_mul α).sub
      (MixedSuccess.physical_value_measurable (I.rows i) i)) measurable_const))

theorem public_raw_success_measurable {Agent T : Type*}
    [Fintype Agent] [MeasurableSpace Agent] [MeasurableSingletonClass Agent]
    [MeasurableSpace T]
    (rule : MixedPhysicalMain.RootRule)
    (next : Protocol T (IntervalOracle.Query Agent) ℝ (RawIntervalPartition.Raw Agent))
    (hnext : Measurable (fun z : T × History (IntervalOracle.Query Agent) ℝ => next z.1 z.2))
    (I : MixedPhysicalMain.Input Agent) (α ε : ℝ) :
    MeasurableSet (MixedIntervalMain.success rule next I α ε) := by
  rw [← MixedIntervalMain.normalized_success]
  let next' := OutputPostprocess.normalized RawIntervalPartition.decode next
  have hnext' : Measurable (fun z : T × History (IntervalOracle.Query Agent) ℝ => next' z.1 z.2) :=
    OutputPostprocess.normalized_measurable RawIntervalPartition.decode
      RawIntervalPartition.decode_measurable next hnext
  change MeasurableSet (NonnegativeSuccess.eventualSuccess next'
    (MixedPhysicalMain.oracle rule I) [] {A | MixedPhysicalMain.Fair I A α ε})
  exact NonnegativeSuccess.measurable_eventualSuccess next' _ hnext'
    (public_mixed_oracle_measurable rule I) [] _ (public_fair_measurable I α ε)

theorem additive_finite_step_unbounded {Agent T : Type*}
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace T]
    {μ : Measure T} [IsProbabilityMeasure μ]
    (rule : MixedPhysicalMain.RootRule)
    (next : Protocol T (IntervalOracle.Query Agent) ℝ (RawIntervalPartition.Raw Agent))
    (base : Agent) (ε p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hε : ε < 1) (hp : 0 < p)
    (hnext : Measurable (fun z : T × History (IntervalOracle.Query Agent) ℝ => next z.1 z.2))
    (hsuccess : ∀ I : MixedFiniteStepMain.StepInput Agent,
      ENNReal.ofReal p ≤ μ (MixedIntervalMain.success rule next I.val 1 ε)) :
    (⨆ I : MixedFiniteStepMain.StepInput Agent,
      MixedIntervalMain.expectedAttempts μ rule next I.val) = ∞ :=
  MixedIntervalMain.finite_step_attempted_expectations_unbounded
    rule next base 1 ε p hn (by norm_num) hε hp hnext hsuccess

end LowerAdaptersIndependentAudit

#print axioms EnvyFreeResearch.Full.AttemptedQueries.attemptedCost_of_terminal
#print axioms EnvyFreeResearch.Full.OutputPostprocess.run_normalized
#print axioms EnvyFreeResearch.Full.OutputPostprocess.queryCost_normalized
#print axioms EnvyFreeResearch.Full.OutputPostprocess.attemptedCost_normalized
#print axioms EnvyFreeResearch.Full.OutputPostprocess.returned_normalized_iff
#print axioms EnvyFreeResearch.Full.OutputPostprocess.normalized_measurable
#print axioms EnvyFreeResearch.Full.RawPartition.decode_measurable
#print axioms EnvyFreeResearch.Full.RawIntervalPartition.valid_iff_geometry
#print axioms EnvyFreeResearch.Full.RawIntervalPartition.decode_measurable
#print axioms EnvyFreeResearch.Full.RawIntervalPartition.decode_ofAllocation
#print axioms EnvyFreeResearch.Full.RawIntervalPartition.ofAllocation_measurable
#print axioms EnvyFreeResearch.Full.RawIntervalPartition.decoded_value
#print axioms EnvyFreeResearch.Full.RawIntervalPartition.value_eq_of_endpoint_change
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.normalized_success
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.malformed_return_failure
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.all_windows
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.optimized_attempted
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.quadratic
#print axioms EnvyFreeResearch.Full.NonnegativeRawMain.two_thirds
#print axioms EnvyFreeResearch.Full.FiniteStepDensity.reflectRow_finiteStep
#print axioms EnvyFreeResearch.Full.MixedFiniteStep.advance_allStep
#print axioms EnvyFreeResearch.Full.MixedExecution.advance_extends
#print axioms EnvyFreeResearch.Full.RightmostExecution.advance_extends
#print axioms EnvyFreeResearch.Full.MixedAmplification.capture_rounds
#print axioms EnvyFreeResearch.Full.RightmostAmplification.capture_rounds
#print axioms EnvyFreeResearch.Full.MixedFiniteStepMain.left_finite_horizon
#print axioms EnvyFreeResearch.Full.MixedFiniteStepMain.right_finite_horizon
#print axioms EnvyFreeResearch.Full.MixedFiniteStepMain.attempted_expectations_unbounded
#print axioms EnvyFreeResearch.Full.MixedPhysicalMain.expected_queries_unbounded
#print axioms EnvyFreeResearch.Full.MixedAttemptedMain.attempted_expectations_unbounded
#print axioms EnvyFreeResearch.Full.MixedIntervalMain.normalized_success
#print axioms EnvyFreeResearch.Full.MixedIntervalMain.finite_step_attempted_expectations_unbounded
#print axioms EnvyFreeResearch.Full.MixedIntervalMain.relative_attempted_expectations_unbounded
#print axioms LowerAdaptersIndependentAudit.attemptedCost_measurable_of_runs
#print axioms LowerAdaptersIndependentAudit.public_raw_attemptedCost_measurable
#print axioms LowerAdaptersIndependentAudit.public_raw_success_measurable
#print axioms LowerAdaptersIndependentAudit.additive_finite_step_unbounded
