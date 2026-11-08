import EnvyFreeResearch.Full.UpperAggregateInterpolationTape

/-!
# Reached invariants and predictable measure budgets

Only reached states need satisfy the fresh-draw estimate. The final measure
budget is a pathwise statement about the actual reached states, and is
converted into a charge budget by monotonicity of the lower integral.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

variable {State Draw Endpoint : Type*}
  [MeasurableSpace State] [MeasurableSpace Draw] [MeasurableSpace Endpoint]

/-- Conditional charging on an invariant of actual reached states. The last
state is indexed separately so the rejecting transition is still included. -/
theorem expected_tapeTotal_le_invariant {m : ℕ} (rho : Fin m → Measure Draw)
    [∀ i, IsProbabilityMeasure (rho i)]
    (step : Fin m → State → Draw → State) (cost : Fin m → State → Draw → ℝ≥0∞)
    (allowance : Fin m → State → ℝ≥0∞)
    (hstep : ∀ i, Measurable (Function.uncurry (step i)))
    (hcost : ∀ i, Measurable (Function.uncurry (cost i)))
    (hallowance : ∀ i, Measurable (allowance i))
    (Safe : Fin (m + 1) → State → Prop)
    (hpreserve : ∀ i state draw, Safe i.castSucc state → Safe i.succ (step i state draw))
    (hfresh : ∀ i state, Safe i.castSucc state →
      (∫⁻ draw, cost i state draw ∂rho i) ≤ allowance i state)
    (state : State) (hstate : Safe 0 state) :
    (∫⁻ draw, tapeTotal step cost state draw ∂Measure.pi rho) ≤
      ∫⁻ draw, tapeTotal step (fun i state _ => allowance i state) state draw ∂Measure.pi rho := by
  induction m generalizing state with
  | zero => simp [tapeTotal]
  | succ m ih =>
    have hmeas : Measurable (fun draw => tapeTotal step cost state draw) :=
      (tapeTotal_measurable step cost hstep hcost).comp (measurable_const.prodMk measurable_id)
    have hameas : Measurable (fun draw => tapeTotal step (fun i state _ => allowance i state) state draw) :=
      (tapeTotal_measurable step (fun i state _ => allowance i state)
        hstep (fun i => (hallowance i).comp measurable_fst)).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_pi_succ rho _ hmeas, lintegral_pi_succ rho _ hameas]
    simp only [tapeTotal, Fin.cons_zero, Fin.cons_succ]
    simp_rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    have hheadcost : Measurable (fun draw : Draw => cost 0 state draw) :=
      (hcost 0).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_add_left hheadcost]
    apply add_le_add (hfresh 0 state hstate)
    apply lintegral_mono
    intro draw
    exact ih (fun i => rho i.succ) (fun i => step i.succ) (fun i => cost i.succ)
      (fun i => allowance i.succ) (fun i => hstep i.succ) (fun i => hcost i.succ)
      (fun i => hallowance i.succ) (fun i => Safe i.succ)
      (fun i state draw hs => hpreserve i.succ state draw hs)
      (fun i state hs => hfresh i.succ state hs) (step 0 state draw)
      (hpreserve 0 state draw hstate)

/-- The predictable measure sum is evaluated on the real reached-state
trace. This step does not discard a rejecting group's endpoint allowance. -/
theorem predictable_budget {m : ℕ} (step : Fin m → State → Draw → State)
    (K : Fin m → State → Measure Endpoint) (u : Endpoint → ℝ≥0∞)
    (state : State) (draw : Fin m → Draw) (base : Measure Endpoint) (Λ : ℝ≥0∞)
    (hbudget : (∑ i, K i (reached step state draw i)) ≤ Λ • base) :
    tapeTotal step (fun i state _ => ∫⁻ z, u z ∂K i state) state draw ≤
      Λ * ∫⁻ z, u z ∂base := by
  rw [tapeTotal_eq_sum]
  rw [← lintegral_finsetSum_measure Finset.univ u (fun i => K i (reached step state draw i))]
  exact (lintegral_mono' hbudget le_rfl).trans_eq (lintegral_smul_measure Λ u)

/-- Aggregate endpoint expectation, derived from fresh-coordinate fibers
and the pathwise predictable measure budget on every complete original tape. -/
theorem aggregate_lintegral_bound {m : ℕ} (rho : Fin m → Measure Draw)
    [∀ i, IsProbabilityMeasure (rho i)]
    (step : Fin m → State → Draw → State) (cost : Fin m → State → Draw → ℝ≥0∞)
    (K : Fin m → State → Measure Endpoint) (u : Endpoint → ℝ≥0∞)
    (hstep : ∀ i, Measurable (Function.uncurry (step i)))
    (hcost : ∀ i, Measurable (Function.uncurry (cost i)))
    (hK : ∀ i, Measurable (fun state => ∫⁻ z, u z ∂K i state))
    (Safe : Fin (m + 1) → State → Prop)
    (hpreserve : ∀ i state draw, Safe i.castSucc state → Safe i.succ (step i state draw))
    (hfresh : ∀ i state, Safe i.castSucc state →
      (∫⁻ draw, cost i state draw ∂rho i) ≤ ∫⁻ z, u z ∂K i state)
    (state : State) (hstate : Safe 0 state) (base : Measure Endpoint) (Λ : ℝ≥0∞)
    (hbudget : ∀ draw, (∑ i, K i (reached step state draw i)) ≤ Λ • base) :
    (∫⁻ draw, tapeTotal step cost state draw ∂Measure.pi rho) ≤ Λ * ∫⁻ z, u z ∂base := by
  calc
    _ ≤ ∫⁻ draw, tapeTotal step (fun i state _ => ∫⁻ z, u z ∂K i state) state draw
        ∂Measure.pi rho :=
      expected_tapeTotal_le_invariant rho step cost (fun i state => ∫⁻ z, u z ∂K i state)
        hstep hcost hK Safe hpreserve hfresh state hstate
    _ ≤ ∫⁻ _draw, Λ * ∫⁻ z, u z ∂base ∂Measure.pi rho :=
      lintegral_mono (fun draw => predictable_budget step K u state draw base Λ (hbudget draw))
    _ = _ := by simp

end EnvyFreeResearch.Full.UpperAggregateInterpolation
