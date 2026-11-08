import EnvyFreeResearch.Full.RightmostBatch
import EnvyFreeResearch.Full.RightmostOracleMeasurable

/-! Measurable capture coordinates for the actual greatest-root executions.
Only measurability on each fixed input is required. -/

namespace EnvyFreeResearch.Full.RightmostViews
open Set MeasureTheory OracleProtocol RightmostOracle RightmostExecution RightmostCaptureStep
open RightmostBatch MixedCoordinates ProtocolMeasurable IntervalAllocation
open IntervalOracle (Profile Query)
open scoped Classical

variable {Agent Ω : Type*} [Fintype Agent] [Nonempty Agent]
  [MeasurableSpace Agent] [MeasurableSingletonClass Agent] [MeasurableSpace Ω] {α : ℝ}

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
  have hone : Measurable (fun _ : Query Agent => (1 : ℝ)) := measurable_const
  apply Measurable.ite MixedViews.query_geometry_measurable
  · by_cases h0 : k = 0
    · convert hone.sub (MixedViews.query_left_measurable (Agent := Agent)) using 1
      funext q
      simp only [ite_eq_left h0, Pi.sub_apply]
    · by_cases h1 : k = 1
      · convert hone.sub (MixedViews.query_right_measurable (Agent := Agent)) using 1
        funext q
        simp only [ite_eq_right h0, ite_eq_left h1, Pi.sub_apply]
      · by_cases h2 : k = 2
        · convert hone.sub (cutPoint_measurable P) using 1
          funext q
          simp only [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2, Pi.sub_apply]
        · simp only [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]
          exact measurable_const
  · exact measurable_const

theorem coordinateMaximum_measurable (P : Profile Agent) : Measurable (coordinateMaximum P) :=
  measurable_properMaximum 3 (coordinate P) (coordinate_measurable P)

def MeasurableRuns (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) : Prop :=
  ∀ (S : MixedFrontier.State Agent α) (fuel : ℕ),
    Measurable (fun ω => run next (oracle (profile S)) ω fuel [])

theorem measurable_runs_of_next
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (hnext : Measurable (fun p : Ω × History (Query Agent) ℝ => next p.1 p.2)) :
    MeasurableRuns (α := α) next :=
  fun S fuel => measurable_run_at_history next (oracle (profile S)) hnext
    (actual_oracle_measurable (profile S)) fuel []

theorem descriptor_measurable_of_run
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : MixedFrontier.State Agent α) (fuel : ℕ) (base : Agent)
    (hrun : Measurable (fun ω => run next (oracle (profile S)) ω fuel [])) :
    Measurable (fun ω => descriptor next S ω fuel base) := by
  have hs := measurable_execution_stop.comp hrun
  convert (MixedViews.stop_cases_measurable (returned := fun _ : Allocation Agent => Query.eval base 0 0)
    (illegal := fun _ : Query Agent => Query.eval base 0 0) (exhausted := id)
    (.eval base 0 0) measurable_const measurable_const measurable_id).comp hs using 1
  funext ω
  dsimp only [descriptor, Function.comp_apply]
  cases (run next (oracle (profile S)) ω fuel []).stop <;> rfl

theorem outputMaximum_measurable_of_run
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent))
    (S : MixedFrontier.State Agent α) (fuel : ℕ)
    (hrun : Measurable (fun ω => run next (oracle (profile S)) ω fuel [])) :
    Measurable (fun ω => outputMaximum next S ω fuel) := by
  have hs := measurable_execution_stop.comp hrun
  convert (MixedViews.stop_cases_measurable (illegal := fun _ : Query Agent => (0 : ℝ))
    (exhausted := fun _ : Query Agent => (0 : ℝ)) (0 : ℝ)
    RightmostFailure.outputMaximum_measurable measurable_const measurable_const).comp hs using 1
  funext ω
  dsimp only [outputMaximum, Function.comp_apply]
  cases (run next (oracle (profile S)) ω fuel []).stop <;> rfl

theorem concrete_measurable_views_of_runs
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hruns : MeasurableRuns (α := α) next) : MeasurableViews (α := α) next base := by
  refine ⟨?_, ?_, ?_⟩
  · intro S fuel
    exact MixedViews.query_agent_measurable.comp
      (descriptor_measurable_of_run next S fuel base (hruns S fuel))
  · intro S fuel
    exact (coordinateMaximum_measurable (profile S)).comp
      (descriptor_measurable_of_run next S fuel base (hruns S fuel))
  · exact fun S fuel => outputMaximum_measurable_of_run next S fuel (hruns S fuel)

theorem concrete_measurable_views
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hnext : Measurable (fun p : Ω × History (Query Agent) ℝ => next p.1 p.2)) :
    MeasurableViews (α := α) next base :=
  concrete_measurable_views_of_runs next base (measurable_runs_of_next next hnext)

end EnvyFreeResearch.Full.RightmostViews
