import EnvyFreeResearch.Full.UpperGlobalTape
import EnvyFreeResearch.Full.UpperExpectedRuntimeConditional

/-! Actual finite-horizon execution on the original infinite stream.
The state law and fresh-coordinate product law are derived from the run,
not supplied as success-conditioned distribution assumptions. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalRun
open MeasureTheory
open scoped ENNReal
open UpperGlobalTape

variable {State Draw : Type*} [MeasurableSpace State] [MeasurableSpace Draw]

def finiteRun (step : State → Draw → State) (initial : State) :
    (t : ℕ) → (Fin t → Draw) → State
  | 0,_ => initial
  | t+1,draws => step (finiteRun step initial t (fun i => draws i.castSucc)) (draws (Fin.last t))

def run (step : State → Draw → State) (initial : State) (t : ℕ) (omega : Stream Draw) : State :=
  finiteRun step initial t (readPrefix t omega)

theorem run_zero (step : State → Draw → State) (initial : State) (omega : Stream Draw) :
    run step initial 0 omega=initial := rfl

theorem run_succ (step : State → Draw → State) (initial : State) (t : ℕ) (omega : Stream Draw) :
    run step initial (t+1) omega=step (run step initial t omega) (omega t) := rfl

theorem finiteRun_measurable (step : State → Draw → State)
    (hstep : Measurable (Function.uncurry step)) (initial : State) (t : ℕ) :
    Measurable (finiteRun step initial t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact hstep.comp ((ih.comp (Measurable.of_eval (fun i => measurable_pi_apply i.castSucc))).prodMk
      (measurable_pi_apply (Fin.last t)))

theorem run_measurable (step : State → Draw → State)
    (hstep : Measurable (Function.uncurry step)) (initial : State) (t : ℕ) :
    Measurable (run step initial t) :=
  (finiteRun_measurable step hstep initial t).comp (prefix_measurable t)

def stateLaw (nu : Measure Draw) (step : State → Draw → State) (initial : State) (t : ℕ) :
    Measure State := (prefixLaw nu t).map (finiteRun step initial t)

theorem state_preserves (nu : Measure Draw) [IsProbabilityMeasure nu]
    (step : State → Draw → State) (hstep : Measurable (Function.uncurry step))
    (initial : State) (t : ℕ) :
    MeasurePreserving (run step initial t) (streamLaw nu) (stateLaw nu step initial t) :=
  (show MeasurePreserving (finiteRun step initial t) (prefixLaw nu t) (stateLaw nu step initial t)
    from ⟨finiteRun_measurable step hstep initial t,rfl⟩).comp (prefix_preserves nu t)

theorem state_fresh_preserves (nu : Measure Draw) [IsProbabilityMeasure nu]
    (step : State → Draw → State) (hstep : Measurable (Function.uncurry step))
    (initial : State) (t : ℕ) :
    MeasurePreserving (fun omega : Stream Draw => (run step initial t omega,omega t))
      (streamLaw nu) ((stateLaw nu step initial t).prod nu) := by
  have hs : MeasurePreserving (finiteRun step initial t) (prefixLaw nu t) (stateLaw nu step initial t) :=
    ⟨finiteRun_measurable step hstep initial t,rfl⟩
  exact (hs.prod (MeasurePreserving.id nu)).comp (prefix_fresh_preserves nu t)

/-- Uniform conditional success at every complete state implies the actual
unconditional paid-attempt inequality on the original execution stream. -/
theorem attempt_bound (nu : Measure Draw) [IsProbabilityMeasure nu]
    (step : State → Draw → State) (hstep : Measurable (Function.uncurry step))
    (initial : State) (t : ℕ) (active : Set State) (ha : MeasurableSet active)
    (success : Set (State × Draw)) (hs : MeasurableSet success)
    (factor : ℝ≥0∞) (hf : factor ≠ ∞)
    (hchance : ∀ s ∈ active, 1 ≤ factor*nu {d | (s,d) ∈ success}) :
    streamLaw nu ((run step initial t) ⁻¹' active) ≤
      factor*streamLaw nu {omega | (run step initial t omega,omega t) ∈ success} := by
  rw [(state_preserves nu step hstep initial t).measure_preimage ha.nullMeasurableSet]
  exact UpperExpectedRuntime.original_tape_attempt_bound (streamLaw nu)
    (stateLaw nu step initial t) nu _ (state_fresh_preserves nu step hstep initial t)
    active ha success hs factor hf hchance

end EnvyFreeResearch.Full.UpperGlobalRun
