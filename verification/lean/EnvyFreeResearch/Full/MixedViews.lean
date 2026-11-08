import EnvyFreeResearch.Full.MixedBatch
import EnvyFreeResearch.Full.MixedMeasurableOracle

/-! The capture views are derived from the standard measurable next-action
rule and the proved Borel least-root oracle. No transcript-measurability
hypothesis is added to the randomized protocol model. -/

namespace EnvyFreeResearch.Full.MixedViews
open Set MeasureTheory IntervalOracle OracleProtocol MixedReplay MixedFrontier MixedExecution
open MixedCoordinates MixedCaptureStep MixedBatch IntervalAllocation NonnegativeOutputMeasurable
open MixedMeasurableOracle ProtocolMeasurable
open scoped Classical

variable {Agent Ω : Type*} [Fintype Agent] [Nonempty Agent]
  [MeasurableSpace Agent] [MeasurableSingletonClass Agent] [MeasurableSpace Ω] {α : ℝ}

omit [Fintype Agent] [Nonempty Agent] [MeasurableSpace Agent] [MeasurableSingletonClass Agent] in
theorem eval_oracle_measurable (P : Profile Agent) (i : Agent) :
    Measurable (fun p : ℝ × ℝ => oracle P (.eval i p.1 p.2)) := by
  have hlegal : MeasurableSet {p : ℝ × ℝ | Legal P (.eval i p.1 p.2)} :=
    ((measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)))
  have hval : Measurable (fun p : ℝ × ℝ => P.cumulative i p.2 - P.cumulative i p.1) :=
    ((P.continuous i).measurable.comp measurable_snd).sub
      ((P.continuous i).measurable.comp measurable_fst)
  exact (measurable_some.comp hval).ite hlegal measurable_const

omit [Nonempty Agent] in
theorem actual_oracle_measurable (P : Profile Agent) : Measurable (oracle P) := by
  apply measurable_query_cases
  · exact measurable_from_prod_countable_right (fun i => eval_oracle_measurable P i)
  · exact measurable_from_prod_countable_right (fun i => cut_oracle_measurable P i)

omit [Fintype Agent] [Nonempty Agent] [MeasurableSingletonClass Agent] in
theorem query_agent_measurable : Measurable (Query.agent (Agent := Agent)) := by
  apply measurable_query_cases <;> exact measurable_fst

omit [Fintype Agent] [Nonempty Agent] [MeasurableSingletonClass Agent] in
theorem query_left_measurable : Measurable (Query.left (Agent := Agent)) := by
  apply measurable_query_cases <;> exact measurable_fst.comp measurable_snd

omit [Fintype Agent] [Nonempty Agent] [MeasurableSingletonClass Agent] in
theorem query_right_measurable : Measurable (Query.right (Agent := Agent)) := by
  apply measurable_query_cases
  · exact measurable_snd.comp measurable_snd
  · exact measurable_fst.comp (measurable_snd.comp measurable_snd)

omit [Fintype Agent] [Nonempty Agent] [MeasurableSingletonClass Agent] in
theorem query_geometry_measurable : MeasurableSet {q : Query Agent | Geometry q} :=
  (measurableSet_le measurable_const query_left_measurable).inter
    ((measurableSet_le query_left_measurable query_right_measurable).inter
      (measurableSet_le query_right_measurable measurable_const))

theorem cutPoint_measurable (P : Profile Agent) : Measurable (cutPoint P) := by
  apply measurable_query_cases
  · exact measurable_const
  · have ho := (actual_oracle_measurable P).comp measurable_query_cut
    have h := measurable_option_cases (present := fun _ (r : ℝ) => r)
      (absent := fun _ => (0 : ℝ)) ho measurable_snd measurable_const
    convert h using 1
    funext p
    simp only [cutPoint, Function.comp_apply]
    cases oracle P (.cut p.1 p.2.1 p.2.2.1 p.2.2.2) <;> rfl

theorem coordinate_measurable (P : Profile Agent) (k : ℕ) :
    Measurable (fun q => coordinate P q k) := by
  apply Measurable.ite query_geometry_measurable
  · by_cases h0 : k = 0
    · simpa only [ite_eq_left h0] using query_left_measurable (Agent := Agent)
    · by_cases h1 : k = 1
      · simpa only [ite_eq_right h0, ite_eq_left h1] using query_right_measurable (Agent := Agent)
      · by_cases h2 : k = 2
        · simpa only [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2] using cutPoint_measurable P
        · simp only [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]
          exact measurable_const
  · exact measurable_const

theorem coordinateMaximum_measurable (P : Profile Agent) : Measurable (coordinateMaximum P) :=
  measurable_properMaximum 3 (coordinate P) (coordinate_measurable P)

/-- Case analysis through the actual finite disjoint-union stop encoding. -/
theorem stop_cases_measurable {Q O X : Type*}
    [MeasurableSpace Q] [MeasurableSpace O] [MeasurableSpace X]
    {returned : O → X} {illegal exhausted : Q → X} (diverged : X)
    (hr : Measurable returned) (hi : Measurable illegal) (he : Measurable exhausted) :
    Measurable (fun s : Stop Q O => match s with
      | .returned out => returned out
      | .diverged => diverged
      | .illegal q => illegal q
      | .exhausted q => exhausted q) := by
  have hd : Measurable (fun _ : Unit => diverged) := measurable_const
  have h := hr.sumElim (hd.sumElim (hi.sumElim he))
  convert h.comp (comap_measurable (stopCode (α := Q) (β := O))) using 1
  funext s
  cases s <;> rfl

def MeasurableRuns (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) : Prop :=
  ∀ (S : State Agent α) (fuel : ℕ),
    Measurable (fun ω => run next (oracle (profile S)) ω fuel [])

theorem measurable_runs_of_next
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (hnext : Measurable (fun p : Ω × History (Query Agent) ℝ => next p.1 p.2)) :
    MeasurableRuns (α := α) next :=
  fun S fuel => measurable_run_at_history next (oracle (profile S)) hnext
    (actual_oracle_measurable (profile S)) fuel []

theorem descriptor_measurable_of_run
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (fuel : ℕ) (base : Agent)
    (hrun : Measurable (fun ω => run next (oracle (profile S)) ω fuel [])) :
    Measurable (fun ω => descriptor next S ω fuel base) := by
  have hs := measurable_execution_stop.comp hrun
  convert (stop_cases_measurable (returned := fun _ : Allocation Agent => Query.eval base 0 0)
    (illegal := fun _ : Query Agent => Query.eval base 0 0) (exhausted := id)
    (.eval base 0 0) measurable_const measurable_const measurable_id).comp hs using 1
  funext ω
  dsimp only [descriptor, Function.comp_apply]
  cases (run next (oracle (profile S)) ω fuel []).stop <;> rfl

theorem outputMaximum_measurable_of_run
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : State Agent α) (fuel : ℕ)
    (hrun : Measurable (fun ω => run next (oracle (profile S)) ω fuel [])) :
    Measurable (fun ω => outputMaximum next S ω fuel) := by
  have hs := measurable_execution_stop.comp hrun
  have hr : Measurable (fun A : Allocation Agent => properMaximum (endpointCount A) (endpoint A)) :=
    measurable_variableMaximum endpointCount endpoint measurable_endpointCount measurable_endpoint
  convert (stop_cases_measurable (illegal := fun _ : Query Agent => (0 : ℝ))
    (exhausted := fun _ : Query Agent => (0 : ℝ)) (0 : ℝ) hr measurable_const measurable_const).comp hs using 1
  funext ω
  dsimp only [outputMaximum, Function.comp_apply]
  cases (run next (oracle (profile S)) ω fuel []).stop <;> rfl

/-- Only the measurability of executions on each fixed input is needed.
No measurability in the valuation profile is assumed. -/
theorem concrete_measurable_views_of_runs
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hruns : MeasurableRuns (α := α) next) :
    MeasurableViews (α := α) next base := by
  refine ⟨?_, ?_, ?_⟩
  · intro S fuel
    exact query_agent_measurable.comp (descriptor_measurable_of_run next S fuel base (hruns S fuel))
  · intro S fuel
    exact (coordinateMaximum_measurable (profile S)).comp
      (descriptor_measurable_of_run next S fuel base (hruns S fuel))
  · exact fun S fuel => outputMaximum_measurable_of_run next S fuel (hruns S fuel)

/-- Every ordinary measurable next-action protocol supplies all hypotheses
used by the concrete positive-mass capture construction. -/
theorem concrete_measurable_views
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hnext : Measurable (fun p : Ω × History (Query Agent) ℝ => next p.1 p.2)) :
    MeasurableViews (α := α) next base :=
  concrete_measurable_views_of_runs next base (measurable_runs_of_next next hnext)

end EnvyFreeResearch.Full.MixedViews
