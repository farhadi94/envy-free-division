import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import Mathlib

/-! A measurable Boolean rejection event with probability below 1/64
gives the inverse-success factor used for every full paid attempt. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRunChance
variable {X : Type*} [MeasurableSpace X]

theorem success_factor_of_rejection (μ : Measure X) [IsProbabilityMeasure μ]
    (reject : X → Bool) (hr : Measurable reject)
    (hfail : μ {x | reject x=true} < 1/64) :
    1 ≤ (64/63 : ℝ≥0∞) * μ {x | reject x=false} := by
  have hs : MeasurableSet {x | reject x=true} := hr (measurableSet_singleton true)
  have hcomp : {x | reject x=true}ᶜ = {x | reject x=false} := by
    ext x
    cases hx : reject x <;> simp [hx]
  have hadd := (measure_add_measure_compl hs).trans (measure_univ (μ := μ))
  rw [hcomp] at hadd
  have hsum := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hsum
  have hf := ENNReal.toReal_mono (by finiteness) hfail.le
  norm_num [ENNReal.toReal_div] at hsum hf
  apply (ENNReal.toReal_le_toReal (by norm_num)
    (ENNReal.mul_ne_top (by finiteness) (measure_ne_top _ _))).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_div]
  linarith

end EnvyFreeResearch.Full.RefinedUpperGlobalRunChance
