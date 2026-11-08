import EnvyFreeResearch.Full.UpperAggregateInterpolationCharge
import EnvyFreeResearch.Full.UpperFreshSamples

/-!
# Predictable charging on an actual finite fresh tape

The state is updated after each fresh coordinate. The allowance at a step
uses the state before that coordinate is drawn. Product decomposition and
Tonelli derive the comparison of total charge and total predictable allowance.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

variable {State Draw : Type*}

def tapeTotal : {m : ℕ} → (Fin m → State → Draw → State) →
    (Fin m → State → Draw → ℝ≥0∞) → State → (Fin m → Draw) → ℝ≥0∞
  | 0, _, _, _, _ => 0
  | m + 1, step, cost, state, draw => cost 0 state (draw 0) +
      tapeTotal (fun i => step i.succ) (fun i => cost i.succ)
        (step 0 state (draw 0)) (fun i => draw i.succ)

/-- The reached state, before each fresh coordinate. -/
def reached : {m : ℕ} → (Fin m → State → Draw → State) →
    State → (Fin m → Draw) → Fin m → State
  | 0, _, _, _ => Fin.elim0
  | m + 1, step, state, draw => Fin.cons state
      (reached (fun i => step i.succ) (step 0 state (draw 0)) (fun i => draw i.succ))

theorem tapeTotal_eq_sum {m : ℕ} (step : Fin m → State → Draw → State)
    (cost : Fin m → State → Draw → ℝ≥0∞) (state : State) (draw : Fin m → Draw) :
    tapeTotal step cost state draw = ∑ i, cost i (reached step state draw i) (draw i) := by
  induction m generalizing state with
  | zero => simp [tapeTotal]
  | succ m ih => simp [tapeTotal, reached, Fin.sum_univ_succ, ih]

section Measurability

variable [MeasurableSpace State] [MeasurableSpace Draw]

theorem tapeTotal_measurable {m : ℕ} (step : Fin m → State → Draw → State)
    (cost : Fin m → State → Draw → ℝ≥0∞)
    (hstep : ∀ i, Measurable (Function.uncurry (step i)))
    (hcost : ∀ i, Measurable (Function.uncurry (cost i))) :
    Measurable (fun p : State × (Fin m → Draw) => tapeTotal step cost p.1 p.2) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    have hhead : Measurable (fun p : State × (Fin (m + 1) → Draw) => (p.1, p.2 0)) :=
      measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
    have htail : Measurable (fun p : State × (Fin (m + 1) → Draw) => fun i : Fin m => p.2 i.succ) :=
      Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp measurable_snd)
    exact ((hcost 0).comp hhead).add
      ((ih (fun i => step i.succ) (fun i => cost i.succ)
        (fun i => hstep i.succ) (fun i => hcost i.succ)).comp
          (((hstep 0).comp hhead).prodMk htail))

theorem reached_measurable {m : ℕ} (step : Fin m → State → Draw → State)
    (hstep : ∀ i, Measurable (Function.uncurry (step i))) :
    Measurable (fun p : State × (Fin m → Draw) => reached step p.1 p.2) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    apply Measurable.of_eval
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst
    · have hhead : Measurable (fun p : State × (Fin (m + 1) → Draw) => step 0 p.1 (p.2 0)) :=
        (hstep 0).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      have htail : Measurable (fun p : State × (Fin (m + 1) → Draw) => fun i : Fin m => p.2 i.succ) :=
        Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp measurable_snd)
      exact (measurable_pi_apply j).comp
        ((ih (fun i => step i.succ) (fun i => hstep i.succ)).comp (hhead.prodMk htail))

/-- The first independent coordinate is separated from the unused tail. -/
theorem lintegral_pi_succ {m : ℕ} (rho : Fin (m + 1) → Measure Draw)
    [∀ i, IsProbabilityMeasure (rho i)] (f : (Fin (m + 1) → Draw) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ draw, f draw ∂Measure.pi rho) =
      ∫⁻ head, ∫⁻ tail, f (Fin.cons head tail) ∂Measure.pi (fun i => rho i.succ) ∂rho 0 := by
  have hp := (measurePreserving_piFinSuccAbove rho 0).symm
  rw [← hp.lintegral_comp hf]
  rw [lintegral_prod (fun p => f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Draw) 0).symm p))
    (hf.comp hp.measurable).aemeasurable]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.succAbove_zero, Fin.insertNth_zero]
  rfl

/-- Derived finite conditional-expectation comparison, without conditioning
on reaching, passing, or accepting a stage. Stopped states may have zero cost
and allowance; the same transition still runs on the full original tape. -/
theorem expected_tapeTotal_le {m : ℕ} (rho : Fin m → Measure Draw)
    [∀ i, IsProbabilityMeasure (rho i)]
    (step : Fin m → State → Draw → State) (cost : Fin m → State → Draw → ℝ≥0∞)
    (allowance : Fin m → State → ℝ≥0∞)
    (hstep : ∀ i, Measurable (Function.uncurry (step i)))
    (hcost : ∀ i, Measurable (Function.uncurry (cost i)))
    (hallowance : ∀ i, Measurable (allowance i))
    (hfresh : ∀ i state, (∫⁻ draw, cost i state draw ∂rho i) ≤ allowance i state)
    (state : State) :
    (∫⁻ draw, tapeTotal step cost state draw ∂Measure.pi rho) ≤
      ∫⁻ draw, tapeTotal step (fun i state _ => allowance i state) state draw ∂Measure.pi rho := by
  induction m generalizing state with
  | zero => simp [tapeTotal]
  | succ m ih =>
    have hmeas : Measurable (fun draw => tapeTotal step cost state draw) :=
      (tapeTotal_measurable step cost hstep hcost).comp
      (measurable_const.prodMk measurable_id)
    have hameas : Measurable (fun draw => tapeTotal step (fun i state _ => allowance i state) state draw) :=
      (tapeTotal_measurable step (fun i state _ => allowance i state)
      hstep (fun i => (hallowance i).comp measurable_fst)).comp
        (measurable_const.prodMk measurable_id)
    rw [lintegral_pi_succ rho _ hmeas, lintegral_pi_succ rho _ hameas]
    simp only [tapeTotal, Fin.cons_zero, Fin.cons_succ]
    simp_rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    have hheadcost : Measurable (fun draw : Draw => cost 0 state draw) :=
      (hcost 0).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_add_left hheadcost]
    apply add_le_add (hfresh 0 state)
    apply lintegral_mono
    intro draw
    exact ih (fun i => rho i.succ) (fun i => step i.succ) (fun i => cost i.succ)
      (fun i => allowance i.succ) (fun i => hstep i.succ) (fun i => hcost i.succ)
      (fun i => hallowance i.succ) (fun i => hfresh i.succ) (step 0 state draw)

/-- The pathwise predictable budget is used only after the genuine fresh
coordinate calculation above. -/
theorem expected_tapeTotal_bound {m : ℕ} (rho : Fin m → Measure Draw)
    [∀ i, IsProbabilityMeasure (rho i)]
    (step : Fin m → State → Draw → State) (cost : Fin m → State → Draw → ℝ≥0∞)
    (allowance : Fin m → State → ℝ≥0∞)
    (hstep : ∀ i, Measurable (Function.uncurry (step i)))
    (hcost : ∀ i, Measurable (Function.uncurry (cost i)))
    (hallowance : ∀ i, Measurable (allowance i))
    (hfresh : ∀ i state, (∫⁻ draw, cost i state draw ∂rho i) ≤ allowance i state)
    (state : State) (bound : ℝ≥0∞)
    (hbudget : ∀ draw, tapeTotal step (fun i state _ => allowance i state) state draw ≤ bound) :
    (∫⁻ draw, tapeTotal step cost state draw ∂Measure.pi rho) ≤ bound := by
  calc
    _ ≤ ∫⁻ draw, tapeTotal step (fun i state _ => allowance i state) state draw ∂Measure.pi rho :=
      expected_tapeTotal_le rho step cost allowance hstep hcost hallowance hfresh state
    _ ≤ ∫⁻ _draw, bound ∂Measure.pi rho := lintegral_mono hbudget
    _ = _ := by simp

end Measurability

end EnvyFreeResearch.Full.UpperAggregateInterpolation
