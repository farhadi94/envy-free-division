import EnvyFreeResearch.Full.UpperAdaptiveProduct

/-!
# Independent samples from an adaptive stateful executor

A fresh primitive can update an arbitrary state and expose it to later
queries. If its returned sample has the same proved law at every preceding
state, iterating the actual primitive on independent draws gives the full
product sample law. The state updates need not be independent of samples.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace EnvyFreeResearch.Full.UpperFreshSamples

open UpperAdaptiveProduct

variable {State Draw Sample : Type*}

def run (step : State → Draw → Sample × State) :
    (m : ℕ) → State → (Fin m → Draw) → (Fin m → Sample) × State
  | 0, state, _ => (Fin.elim0, state)
  | m + 1, state, draw =>
      let first := step state (draw 0)
      let rest := run step m first.2 (fun i => draw i.succ)
      (Fin.cons first.1 rest.1, rest.2)

section Measurability

variable [MeasurableSpace State] [MeasurableSpace Draw] [MeasurableSpace Sample]

theorem run_measurable (step : State → Draw → Sample × State)
    (hstep : Measurable (Function.uncurry step)) (m : ℕ) :
    Measurable (fun p : State × (Fin m → Draw) => run step m p.1 p.2) := by
  induction m with
  | zero => exact measurable_const.prodMk measurable_fst
  | succ m ih =>
    let first (p : State × (Fin (m + 1) → Draw)) := step p.1 (p.2 0)
    have hfirst : Measurable first := hstep.comp
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    let rest (p : State × (Fin (m + 1) → Draw)) := run step m (first p).2 (fun i => p.2 i.succ)
    have htail : Measurable (fun p : State × (Fin (m + 1) → Draw) => fun i : Fin m => p.2 i.succ) :=
      Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp measurable_snd)
    have hrest : Measurable rest := ih.comp ((measurable_snd.comp hfirst).prodMk htail)
    have hvalues : Measurable (fun p => Fin.cons (α := fun _ : Fin (m + 1) => Sample)
        (first p).1 (rest p).1) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact measurable_fst.comp hfirst
      · exact (measurable_pi_apply j).comp (measurable_fst.comp hrest)
    exact hvalues.prodMk (measurable_snd.comp hrest)

/-- Full joint product law, derived from the actual state transition and
its per-state sample law by the measure-preserving skew-product theorem. -/
theorem independent_samples (step : State → Draw → Sample × State)
    (hstep : Measurable (Function.uncurry step))
    (rho : Measure Draw) (sigma : Measure Sample)
    [IsProbabilityMeasure rho] [IsProbabilityMeasure sigma]
    (hlaw : ∀ state, rho.map (fun draw => (step state draw).1) = sigma)
    (m : ℕ) (state : State) :
    MeasurePreserving (fun draw => (run step m state draw).1) (tapeLaw rho m) (tapeLaw sigma m) := by
  have hrun (m : ℕ) := run_measurable step hstep m
  induction m generalizing state with
  | zero =>
    refine ⟨measurable_const, ?_⟩
    simp only [run, Measure.map_const, measure_univ, one_smul]
    exact (Measure.pi_of_empty (fun _ : Fin 0 => sigma) Fin.elim0).symm
  | succ m ih =>
    have hfirst : Measurable (fun draw => step state draw) :=
      hstep.comp (measurable_const.prodMk measurable_id)
    have hf : MeasurePreserving (fun draw => (step state draw).1) rho sigma :=
      ⟨measurable_fst.comp hfirst, hlaw state⟩
    have hrest : Measurable (fun p : Draw × (Fin m → Draw) =>
        (run step m (step state p.1).2 p.2).1) :=
      measurable_fst.comp ((hrun m).comp
        (((measurable_snd.comp hfirst).comp measurable_fst).prodMk measurable_snd))
    have hskew := hf.skew_product hrest (ae_of_all rho (fun draw => (ih (step state draw).2).map_eq))
    have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => rho) 0
    have hjoin := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => sigma) 0).symm
    have hfull := hjoin.comp (hskew.comp hsplit)
    convert hfull using 1
    · funext draw i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [run, MeasurableEquiv.piFinSuccAbove_apply,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
      rfl
    · rfl
    · rfl

end Measurability

/-- Deterministic attempted-work accounting for every draw vector. This is
independent of the sample-law proof and includes all adaptive state updates. -/
theorem cost_bound (step : State → Draw → Sample × State) (cost : State → ℕ) (budget : ℕ)
    (hstep : ∀ state draw, cost (step state draw).2 ≤ cost state + budget)
    (m : ℕ) (state : State) (draw : Fin m → Draw) :
    cost (run step m state draw).2 ≤ cost state + m * budget := by
  induction m generalizing state with
  | zero => simp [run]
  | succ m ih =>
    have htail := ih (step state (draw 0)).2 (fun i => draw i.succ)
    have hhead := hstep state (draw 0)
    simp only [run, Nat.add_mul, Nat.one_mul]
    omega

end EnvyFreeResearch.Full.UpperFreshSamples
