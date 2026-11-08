import EnvyFreeResearch.Full.UpperAggregateInterpolationMean

/-! Joint Borel charging when the independently sampled immutable grid fixes
the initial state, job schedule, and all later adaptive computations. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

variable {Parameter State Draw : Type*}

theorem tapeTotal_frozen_parameter {m : ℕ}
    (step : Parameter → Fin m → State → Draw → State)
    (cost : Parameter → Fin m → State → Draw → ℝ≥0∞)
    (p : Parameter) (state : State) (draw : Fin m → Draw) :
    tapeTotal (fun i p draw => (p.1, step p.1 i p.2 draw))
      (fun i p draw => cost p.1 i p.2 draw) (p, state) draw =
      tapeTotal (step p) (cost p) state draw := by
  induction m generalizing state with
  | zero => rfl
  | succ m ih =>
    simp only [tapeTotal]
    exact congrArg (fun x => cost p 0 state (draw 0) + x)
      (ih (fun p i => step p i.succ) (fun p i => cost p i.succ)
        (step p 0 state (draw 0)) (fun i => draw i.succ))

variable [MeasurableSpace Parameter] [MeasurableSpace State] [MeasurableSpace Draw]

theorem parameterized_tapeTotal_measurable {m : ℕ}
    (step : Parameter → Fin m → State → Draw → State)
    (cost : Parameter → Fin m → State → Draw → ℝ≥0∞)
    (hstep : ∀ i, Measurable (fun p : (Parameter × State) × Draw => step p.1.1 i p.1.2 p.2))
    (hcost : ∀ i, Measurable (fun p : (Parameter × State) × Draw => cost p.1.1 i p.1.2 p.2))
    (initial : Parameter → State) (hinitial : Measurable initial) :
    Measurable (fun p : Parameter × (Fin m → Draw) => tapeTotal (step p.1) (cost p.1) (initial p.1) p.2) := by
  have hfrozen := tapeTotal_measurable
    (fun i (p : Parameter × State) draw => (p.1, step p.1 i p.2 draw))
    (fun i (p : Parameter × State) draw => cost p.1 i p.2 draw)
    (fun i => (measurable_fst.comp measurable_fst).prodMk (hstep i)) hcost
  have h := hfrozen.comp ((measurable_fst.prodMk (hinitial.comp measurable_fst)).prodMk measurable_snd)
  convert h using 1
  funext p
  exact (tapeTotal_frozen_parameter step cost p.1 (initial p.1) p.2).symm

/-- Average derived per-grid tape bounds over the independent original sample
batch. The hypothesis is a local tape theorem for almost every grid; it may
be supplied by the reached-state/endpoint-law construction. -/
theorem average_tapeTotal_bound {m : ℕ} (gridLaw : Measure Parameter)
    (rho : Fin m → Measure Draw) [∀ i, IsProbabilityMeasure (rho i)]
    (step : Parameter → Fin m → State → Draw → State)
    (cost : Parameter → Fin m → State → Draw → ℝ≥0∞)
    (hstep : ∀ i, Measurable (fun p : (Parameter × State) × Draw => step p.1.1 i p.1.2 p.2))
    (hcost : ∀ i, Measurable (fun p : (Parameter × State) × Draw => cost p.1.1 i p.1.2 p.2))
    (initial : Parameter → State) (hinitial : Measurable initial)
    (bound : Parameter → ℝ≥0∞)
    (hfiber : ∀ᵐ grid ∂gridLaw,
      (∫⁻ tape, tapeTotal (step grid) (cost grid) (initial grid) tape ∂Measure.pi rho) ≤ bound grid) :
    (∫⁻ p, tapeTotal (step p.1) (cost p.1) (initial p.1) p.2 ∂gridLaw.prod (Measure.pi rho)) ≤
      ∫⁻ grid, bound grid ∂gridLaw := by
  rw [lintegral_prod _ (parameterized_tapeTotal_measurable step cost hstep hcost initial hinitial).aemeasurable]
  exact lintegral_mono_ae hfiber

end EnvyFreeResearch.Full.UpperAggregateInterpolation
