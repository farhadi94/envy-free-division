import EnvyFreeResearch.Full.MixedFiniteStepMain
import EnvyFreeResearch.Full.RawIntervalPartition

/-! Public mixed impossibility for arbitrary unsorted finite interval
records. Invalid or incomplete returns are failures. Validation is a proved
measurable geometric operation and makes no oracle calls. -/

noncomputable section
namespace EnvyFreeResearch.Full.MixedIntervalMain
open Set MeasureTheory OracleProtocol AttemptedQueries MixedPhysicalMain MixedObstruction
open MixedFiniteStepMain IntervalAllocation
open scoped ENNReal Classical

variable {Agent Ω : Type*}

def Fair (I : Input Agent) (r : RawIntervalPartition.Raw Agent) (α ε : ℝ) : Prop :=
  ∀ i j, α * value (I.rows i) (RawIntervalPartition.share r j) -
    value (I.rows i) (RawIntervalPartition.share r i) ≤ ε

def success (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawIntervalPartition.Raw Agent))
    (I : Input Agent) (α ε : ℝ) : Set Ω :=
  {ω | ∃ fuel r, (run next (oracle rule I) ω fuel []).stop = .returned r ∧
    RawIntervalPartition.Valid r ∧ Fair I r α ε}

def expectedAttempts [MeasurableSpace Ω] (μ : Measure Ω) (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawIntervalPartition.Raw Agent))
    (I : Input Agent) : ℝ≥0∞ :=
  ∫⁻ ω, (attemptedCost next (oracle rule I) ω [] : ℝ≥0∞) ∂μ

theorem normalized_success (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawIntervalPartition.Raw Agent))
    (I : Input Agent) (α ε : ℝ) :
    MixedPhysicalMain.success rule
      (OutputPostprocess.normalized RawIntervalPartition.decode next) I α ε =
      success rule next I α ε := by
  ext ω
  constructor
  · rintro ⟨fuel,A,hret,hfair⟩
    obtain ⟨r,hr,hd⟩ := (OutputPostprocess.returned_normalized_iff
      RawIntervalPartition.decode next (oracle rule I) ω fuel [] A).mp hret
    obtain ⟨hv,heq⟩ := (RawIntervalPartition.decode_some_iff r A).mp hd
    refine ⟨fuel,r,hr,hv,?_⟩
    intro i j
    simpa only [RawIntervalPartition.decoded_share r A hd] using hfair i j
  · rintro ⟨fuel,r,hr,hv,hfair⟩
    let A := RawIntervalPartition.allocation r hv
    have hd : RawIntervalPartition.decode r = some A :=
      (RawIntervalPartition.decode_some_iff r A).mpr ⟨hv,rfl⟩
    refine ⟨fuel,A,(OutputPostprocess.returned_normalized_iff
      RawIntervalPartition.decode next (oracle rule I) ω fuel [] A).mpr ⟨r,hr,hd⟩,?_⟩
    intro i j
    simpa only [RawIntervalPartition.decoded_share r A hd] using hfair i j

/-- Strong form: it suffices to require success only on normalized finite
piecewise-constant signed densities. Output sizes need only be finite on
each returned run, with no uniform or expected size bound. -/
theorem finite_step_attempted_expectations_unbounded
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawIntervalPartition.Raw Agent))
    (base : Agent) (α ε p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hε : ε < α) (hp : 0 < p)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (hsuccess : ∀ I : StepInput Agent, ENNReal.ofReal p ≤ μ (success rule next I.val α ε)) :
    (⨆ I : StepInput Agent, expectedAttempts μ rule next I.val) = ∞ := by
  let next' := OutputPostprocess.normalized RawIntervalPartition.decode next
  have hm := OutputPostprocess.normalized_measurable
    RawIntervalPartition.decode RawIntervalPartition.decode_measurable next hnext
  have hs (I : StepInput Agent) :
      ENNReal.ofReal p ≤ μ (MixedPhysicalMain.success rule next' I.val α ε) := by
    simpa only [next',normalized_success] using hsuccess I
  have h := MixedFiniteStepMain.attempted_expectations_unbounded
    rule next' base α ε p hn hα hε hp hm hs
  simpa only [MixedAttemptedMain.expectedAttempts,expectedAttempts,next',
    OutputPostprocess.attemptedCost_normalized] using h

theorem attempted_expectations_unbounded
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawIntervalPartition.Raw Agent))
    (base : Agent) (α ε p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hε : ε < α) (hp : 0 < p)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (hsuccess : ∀ I : Input Agent, ENNReal.ofReal p ≤ μ (success rule next I α ε)) :
    (⨆ I : Input Agent, expectedAttempts μ rule next I) = ∞ := by
  have h := finite_step_attempted_expectations_unbounded rule next base α ε p
    hn hα hε hp hnext (fun I => hsuccess I.val)
  apply top_unique
  rw [← h]
  apply iSup_le
  intro I
  exact le_iSup_of_le I.val le_rfl

def RelativeFair (I : Input Agent) (r : RawIntervalPartition.Raw Agent) (α : ℝ) : Prop :=
  MixedApproximation.RelativeEF (fun i j => value (I.rows i) (RawIntervalPartition.share r j)) α

def relativeSuccess (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawIntervalPartition.Raw Agent))
    (I : Input Agent) (α : ℝ) : Set Ω :=
  {ω | ∃ fuel r, (run next (oracle rule I) ω fuel []).stop = .returned r ∧
    RawIntervalPartition.Valid r ∧ RelativeFair I r α}

theorem relative_iff_fair [Fintype Agent] (I : Input Agent)
    (r : RawIntervalPartition.Raw Agent) (hv : RawIntervalPartition.Valid r)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) : RelativeFair I r α ↔ Fair I r α 0 := by
  exact MixedPhysicalMain.relative_iff_fair I (RawIntervalPartition.allocation r hv) α hα hα1

theorem relative_success_eq [Fintype Agent] (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawIntervalPartition.Raw Agent))
    (I : Input Agent) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    relativeSuccess rule next I α = success rule next I α 0 := by
  ext ω
  constructor <;> rintro ⟨fuel,r,hr,hv,hfair⟩
  · exact ⟨fuel,r,hr,hv,(relative_iff_fair I r hv α hα hα1).mp hfair⟩
  · exact ⟨fuel,r,hr,hv,(relative_iff_fair I r hv α hα hα1).mpr hfair⟩

theorem relative_attempted_expectations_unbounded
    [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
    [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (rule : RootRule)
    (next : Protocol Ω (IntervalOracle.Query Agent) ℝ (RawIntervalPartition.Raw Agent))
    (base : Agent) (α p : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hα1 : α ≤ 1) (hp : 0 < p)
    (hnext : Measurable (fun p : Ω × History (IntervalOracle.Query Agent) ℝ => next p.1 p.2))
    (hsuccess : ∀ I : StepInput Agent, ENNReal.ofReal p ≤ μ (relativeSuccess rule next I.val α)) :
    (⨆ I : StepInput Agent, expectedAttempts μ rule next I.val) = ∞ := by
  apply finite_step_attempted_expectations_unbounded rule next base α 0 p hn hα hα hp hnext
  intro I
  simpa only [relative_success_eq rule next I.val α hα hα1] using hsuccess I

end EnvyFreeResearch.Full.MixedIntervalMain
