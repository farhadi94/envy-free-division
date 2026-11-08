import EnvyFreeResearch.Full.RightmostSuccess
import EnvyFreeResearch.QueryProbability

/-!
Unbounded unconditional expected query cost for the concrete always-rightmost
signed oracle. The capture construction, physical failure certificate,
measurable protocol semantics, success event, and actual query cost are all
connected here. The profile argument indexes the reflected physical signed-density family;
its approximation correspondence is supplied separately.
-/

noncomputable section
namespace EnvyFreeResearch.Full.RightmostMain
open Set MeasureTheory OracleProtocol RightmostOracle
open IntervalOracle (Profile Query)
open MixedFrontier RightmostExecution
open RightmostBatch RightmostViews RightmostAmplification RightmostSuccess IntervalAllocation
open scoped ENNReal Classical

variable {Agent Ω : Type*} [Fintype Agent] [Nonempty Agent]
  [MeasurableSpace Agent] [MeasurableSingletonClass Agent] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {α : ℝ}

/-- A single fixed signed profile makes the actual successful cap-q event
arbitrarily small for every measurable randomized protocol. -/
theorem finite_horizon_hard_input_of_runs
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hruns : MeasurableRuns (α := α) next)
    (fuel : ℕ) (ε δ : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hε : ε < α) (hδ : 0 < δ) :
    ∃ S : State Agent α, μ (capSuccess next S fuel ε) ≤ ENNReal.ofReal δ := by
  obtain ⟨S, hS⟩ := exists_hard_cap (μ := μ) next base
    (concrete_measurable_views_of_runs next base hruns) fuel ε δ hn hα hε hδ
  refine ⟨S, ?_⟩
  rw [← ofReal_measureReal (μ := μ) (s := capSuccess next S fuel ε)]
  exact ENNReal.ofReal_le_ofReal hS.le

/-- Actual all-outcome query costs have no uniform finite expectation when
the protocol must return a fair physical allocation with probability p>0
on every member of the constructed signed-density family. -/
theorem expected_queries_unbounded_of_runs
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hruns : MeasurableRuns (α := α) next)
    (ε p : ℝ) (hn : 3 ≤ Fintype.card Agent) (hα : 0 < α) (hε : ε < α) (hp : 0 < p)
    (hsuccess : ∀ S : State Agent α, ENNReal.ofReal p ≤ μ (success next S ε)) :
    (⨆ S : State Agent α,
      ∫⁻ ω, (queryCost next (oracle (profile S)) ω [] : ℝ≥0∞) ∂μ) = ∞ := by
  apply QueryProbability.supremum_expectations_eq_top
    (fun S : State Agent α => fun ω => queryCost next (oracle (profile S)) ω [])
    (fun S => success next S ε)
    (fun S => actual_cost_measurable_of_runs next S (hruns S))
    (fun S => success_measurable_of_runs next S ε (hruns S))
    (δ := ENNReal.ofReal (p / 2))
  · exact (ENNReal.ofReal_lt_ofReal_iff hp).mpr (by linarith)
  · exact hsuccess
  · intro fuel
    obtain ⟨S, hS⟩ := finite_horizon_hard_input_of_runs (μ := μ) next base hruns fuel ε (p / 2)
      hn hα hε (by linarith)
    refine ⟨S, ?_⟩
    rw [success_below_cap]
    exact hS

theorem finite_horizon_hard_input
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hnext : Measurable (fun p : Ω × History (Query Agent) ℝ => next p.1 p.2))
    (fuel : ℕ) (ε δ : ℝ) (hn : 3 ≤ Fintype.card Agent)
    (hα : 0 < α) (hε : ε < α) (hδ : 0 < δ) :
    ∃ S : State Agent α, μ (capSuccess next S fuel ε) ≤ ENNReal.ofReal δ :=
  finite_horizon_hard_input_of_runs next base (measurable_runs_of_next next hnext)
    fuel ε δ hn hα hε hδ

theorem expected_queries_unbounded
    (next : Protocol Ω (Query Agent) ℝ (Allocation Agent)) (base : Agent)
    (hnext : Measurable (fun p : Ω × History (Query Agent) ℝ => next p.1 p.2))
    (ε p : ℝ) (hn : 3 ≤ Fintype.card Agent) (hα : 0 < α) (hε : ε < α) (hp : 0 < p)
    (hsuccess : ∀ S : State Agent α, ENNReal.ofReal p ≤ μ (success next S ε)) :
    (⨆ S : State Agent α,
      ∫⁻ ω, (queryCost next (oracle (profile S)) ω [] : ℝ≥0∞) ∂μ) = ∞ :=
  expected_queries_unbounded_of_runs next base (measurable_runs_of_next next hnext)
    ε p hn hα hε hp hsuccess

end EnvyFreeResearch.Full.RightmostMain
