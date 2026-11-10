import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.Prod

/-! The original infinite stream and its exact finite-readPrefix/fresh-draw law.
No independence of accepted outcomes or adaptive requests is assumed. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobalTape
open MeasureTheory ProbabilityTheory

variable {Draw : Type*} [MeasurableSpace Draw]

abbrev Stream (Draw : Type*) := ℕ → Draw

def streamLaw (nu : Measure Draw) : Measure (Stream Draw) :=
  Measure.infinitePi (fun _ : ℕ => nu)

def readPrefix (t : ℕ) (omega : Stream Draw) : Fin t → Draw := fun i => omega i.val

def prefixLaw (nu : Measure Draw) (t : ℕ) : Measure (Fin t → Draw) :=
  Measure.pi (fun _ => nu)

instance streamLaw_probability (nu : Measure Draw) [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (streamLaw nu) := by unfold streamLaw; infer_instance

instance prefixLaw_probability (nu : Measure Draw) [IsProbabilityMeasure nu] (t : ℕ) :
    IsProbabilityMeasure (prefixLaw nu t) := by unfold prefixLaw; infer_instance

theorem prefix_measurable (t : ℕ) : Measurable (readPrefix (Draw := Draw) t) := by
  unfold readPrefix
  fun_prop

theorem prefix_preserves (nu : Measure Draw) [IsProbabilityMeasure nu] (t : ℕ) :
    MeasurePreserving (readPrefix t) (streamLaw nu) (prefixLaw nu t) := by
  refine ⟨prefix_measurable t,?_⟩
  have h := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => nu) (f := fun i : Fin t => i.val) Fin.val_injective
  change (Measure.infinitePi (fun _ : ℕ => nu)).map (fun omega (i : Fin t) => omega i.val) =
    Measure.pi (fun _ : Fin t => nu)
  simpa only [Measure.infinitePi_eq_pi] using h

/-- The complete previous random readPrefix and next draw have product law. -/
theorem prefix_fresh_preserves (nu : Measure Draw) [IsProbabilityMeasure nu] (t : ℕ) :
    MeasurePreserving (fun omega : Stream Draw => (readPrefix t omega,omega t))
      (streamLaw nu) ((prefixLaw nu t).prod nu) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (t+1) => nu) (Fin.last t)).comp
    (prefix_preserves nu (t+1))
  have hs := (Measure.measurePreserving_swap (μ := nu) (ν := prefixLaw nu t)).comp hp
  convert hs using 1
  ext omega
  all_goals simp [readPrefix,MeasurableEquiv.piFinSuccAbove,Function.comp_def] <;> rfl

end EnvyFreeResearch.Full.RefinedUpperGlobalTape
