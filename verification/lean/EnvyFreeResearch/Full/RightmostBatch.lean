import EnvyFreeResearch.Full.RightmostCaptureStep
import EnvyFreeResearch.Full.NonnegativeOutputMeasurable

/-! Positive-mass capture for arbitrary tape spaces. The measurable-view
hypotheses refer to concrete recursively computed traces and outputs; they
are instantiated separately from the protocol's standard Borel coding. -/

noncomputable section
namespace EnvyFreeResearch.Full.RightmostBatch
open Set MeasureTheory OracleProtocol RightmostOracle RightmostReplay
open IntervalOracle (Profile Query)
open MixedFrontier RightmostExecution MixedCoordinates RightmostCaptureStep OracleStep IntervalAllocation
open NonnegativeOutputMeasurable
open scoped Classical

variable {Agent Ω : Type*} [Fintype Agent] [Nonempty Agent]
  [MeasurableSpace Agent] [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {α : ℝ}

def outputMaximum (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (tape : Ω) (fuel : ℕ) : ℝ :=
  match (run next (oracle (profile S)) tape fuel []).stop with
  | .returned A => RightmostFailure.outputMaximum A
  | _ => 0

omit [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
  [MeasurableSingletonClass Agent] [MeasurableSpace Ω] in
theorem outputMaximum_lt_one (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (tape : Ω) (fuel : ℕ) : outputMaximum next S tape fuel < 1 := by
  unfold outputMaximum
  split
  · exact RightmostFailure.outputMaximum_lt_one _
  all_goals norm_num

structure MeasurableViews (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (base : Agent) : Prop where
  row : ∀ (S : State Agent α) fuel,
    Measurable (fun ω => (descriptor next S ω fuel base).agent)
  coordinate : ∀ (S : State Agent α) fuel,
    Measurable (fun ω => coordinateMaximum (profile S) (descriptor next S ω fuel base))
  output : ∀ (S : State Agent α) fuel, Measurable (fun ω => outputMaximum next S ω fuel)

omit [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
  [MeasurableSingletonClass Agent] [MeasurableSpace Ω] in
theorem output_frozen (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (tape : Ω) (fuel : ℕ) (A : Allocation Agent) (r : ℝ)
    (hret : (run next (oracle (profile S)) tape fuel []).stop = .returned A)
    (hm : outputMaximum next S tape fuel ≤ r) :
    (∀ k, FrozenCoordinate r (A.left k)) ∧ (∀ k, FrozenCoordinate r (A.right k)) := by
  have hm' : RightmostFailure.outputMaximum A ≤ r := by
    simpa [outputMaximum, hret] using hm
  exact RightmostFailure.outputMaximum_frozen A r hm'

omit [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent]
  [MeasurableSingletonClass Agent] [MeasurableSpace Ω] in
theorem trace_of_extends
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    {S T : State Agent α} (hst : Extends S T) (tape : Ω) (fuel : ℕ)
    (hf : FrozenTrace next S tape fuel) : FrozenTrace next T tape fuel := by
  have he := replay_of_extends next hst tape fuel hf
  constructor
  · intro q x hx
    rw [he] at hx
    exact frozen_answer_mono hst.frontier q x (hf.1 q x hx)
  · intro q hq hg
    rw [he] at hq
    have h := hf.2 q hq hg
    exact ⟨frozen_mono hst.frontier h.1, frozen_mono hst.frontier h.2⟩

/-- Selecting a row and then a coordinate quantile protects one additional
actual query while retaining at least a 1/(2n) fraction of the tape set. -/
theorem exists_query_capture
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (views : MeasurableViews (α := α) next base)
    (S : State Agent α) (H : Set Ω) (fuel : ℕ) (hα : 0 < α)
    (hH : MeasurableSet H) (hf : ∀ ω ∈ H, FrozenTrace next S ω fuel) :
    ∃ T : State Agent α, ∃ G : Set Ω, Extends S T ∧ MeasurableSet G ∧ G ⊆ H ∧
      μ.real H / (2 * Fintype.card Agent) ≤ μ.real G ∧
      ∀ ω ∈ G, FrozenTrace next T ω (fuel + 1) := by
  obtain ⟨j, r, hlr, hr, hG, hmass⟩ := FiniteCapture.exists_row_coordinate_capture
    (μ := μ) H (fun ω => (descriptor next S ω fuel base).agent)
    (fun ω => coordinateMaximum (profile S) (descriptor next S ω fuel base)) S.frontier
    hH (views.row S fuel) (views.coordinate S fuel) S.proper
    (fun ω _ => coordinateMaximum_lt_one _ _)
  let G := H ∩ {ω | (descriptor next S ω fuel base).agent = j} ∩
    {ω | coordinateMaximum (profile S) (descriptor next S ω fuel base) ≤ r}
  refine ⟨advance S hα j r hlr hr, G, advance_extends S hα j r hlr hr,
    hG, (fun ω hω => hω.1.1), hmass, ?_⟩
  intro ω hω
  exact (advance_protects_next next S ω fuel base j hα r hlr hr
    (hf ω hω.1.1) hω.1.2 hω.2).2

/-- Finite repetition protects every actual request up to the cap. -/
theorem exists_frozen_trace
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (views : MeasurableViews (α := α) next base)
    (S : State Agent α) (H : Set Ω) (fuel : ℕ) (hα : 0 < α) (hH : MeasurableSet H) :
    ∃ T : State Agent α, ∃ G : Set Ω, Extends S T ∧ MeasurableSet G ∧ G ⊆ H ∧
      μ.real H / (2 * Fintype.card Agent : ℝ) ^ fuel ≤ μ.real G ∧
      ∀ ω ∈ G, FrozenTrace next T ω fuel := by
  induction fuel with
  | zero =>
    refine ⟨S, H, Extends.refl S, hH, subset_rfl, by simp, ?_⟩
    intro ω hω
    constructor
    · intro q x hx
      rw [zero_answers] at hx
      simp at hx
    · intro q hq hg
      exact False.elim (zero_not_illegal next (oracle (profile S)) ω [] q hq)
  | succ fuel ih =>
    obtain ⟨T, G, hst, hG, hGH, hmass, hf⟩ := ih
    obtain ⟨U, J, htu, hJ, hJG, hgain, hfu⟩ :=
      exists_query_capture (μ := μ) next base views T G fuel hα hG hf
    refine ⟨U, J, hst.trans htu, hJ, hJG.trans hGH, ?_, hfu⟩
    calc
      μ.real H / (2 * Fintype.card Agent : ℝ) ^ (fuel + 1) =
        (μ.real H / (2 * Fintype.card Agent : ℝ) ^ fuel) / (2 * Fintype.card Agent) := by
          rw [div_div, pow_succ]
      _ ≤ μ.real G / (2 * Fintype.card Agent) :=
        div_le_div_of_nonneg_right hmass (by positivity)
      _ ≤ μ.real J := hgain

/-- Output endpoint protection loses only one further factor of two. -/
theorem exists_output_capture
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (views : MeasurableViews (α := α) next base)
    (S : State Agent α) (H : Set Ω) (fuel : ℕ) (hα : 0 < α)
    (hH : MeasurableSet H) (hf : ∀ ω ∈ H, FrozenTrace next S ω fuel) :
    ∃ T : State Agent α, ∃ G : Set Ω, Extends S T ∧ MeasurableSet G ∧ G ⊆ H ∧
      μ.real H / 2 ≤ μ.real G ∧ ∀ ω ∈ G, Protected next T ω fuel := by
  obtain ⟨r, hlr, hr, hmass⟩ := FiniteCapture.exists_coordinate_quantile (μ := μ)
    H (fun ω => outputMaximum next S ω fuel) S.frontier S.proper
    (fun ω _ => outputMaximum_lt_one next S ω fuel)
  let G := H ∩ {ω | outputMaximum next S ω fuel ≤ r}
  let T := advance S hα base r hlr hr
  have hst : Extends S T := advance_extends S hα base r hlr hr
  refine ⟨T, G, hst, hH.inter (measurableSet_le (views.output S fuel) measurable_const),
    (fun ω hω => hω.1), hmass, ?_⟩
  intro ω hω
  have htrace := hf ω hω.1
  have he := replay_of_extends next hst ω fuel htrace
  refine ⟨trace_of_extends next hst ω fuel htrace, ?_⟩
  intro A hret
  rw [he] at hret
  exact output_frozen next S ω fuel A r hret hω.2

/-- A concrete finite batch captures a positive fraction of any measurable
set of tapes, on one fixed resulting signed profile. -/
theorem exists_batch
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (views : MeasurableViews (α := α) next base)
    (S : State Agent α) (H : Set Ω) (fuel : ℕ) (hα : 0 < α) (hH : MeasurableSet H) :
    ∃ T : State Agent α, ∃ G : Set Ω, Extends S T ∧ MeasurableSet G ∧ G ⊆ H ∧
      μ.real H / (2 * (2 * Fintype.card Agent : ℝ) ^ fuel) ≤ μ.real G ∧
      ∀ ω ∈ G, Protected next T ω fuel := by
  obtain ⟨T, G, hst, hG, hGH, hmass, hf⟩ := exists_frozen_trace (μ := μ)
    next base views S H fuel hα hH
  obtain ⟨U, J, htu, hJ, hJG, hgain, hp⟩ := exists_output_capture (μ := μ)
    next base views T G fuel hα hG hf
  refine ⟨U, J, hst.trans htu, hJ, hJG.trans hGH, ?_, hp⟩
  calc
    μ.real H / (2 * (2 * Fintype.card Agent : ℝ) ^ fuel) =
      (μ.real H / (2 * Fintype.card Agent : ℝ) ^ fuel) / 2 := by ring
    _ ≤ μ.real G / 2 := div_le_div_of_nonneg_right hmass (by norm_num)
    _ ≤ μ.real J := hgain

end EnvyFreeResearch.Full.RightmostBatch
