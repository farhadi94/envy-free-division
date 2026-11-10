import Mathlib

/-! Averaging conditional failure without conditioning the input law.
Exceptional preparation parameters are charged at their original mass. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperTrialUnion
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem exceptional_product_bound (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (failed : Set (X × Y)) (hf : MeasurableSet failed)
    (bad : Set X) (hb : MeasurableSet bad) (e : ℝ≥0∞)
    (hbound : ∀ x, x ∉ bad → ν {y | (x,y) ∈ failed} ≤ e) :
    (μ.prod ν) failed ≤ μ bad + e := by
  rw [Measure.prod_apply hf]
  calc
    _ ≤ ∫⁻ x, bad.indicator (fun _ => (1 : ℝ≥0∞)) x + e ∂μ := by
      apply lintegral_mono
      intro x
      change ν {y | (x,y) ∈ failed} ≤ bad.indicator (fun _ => (1 : ℝ≥0∞)) x + e
      by_cases hx : x ∈ bad
      · rw [indicator_of_mem hx]
        exact (prob_le_one).trans (le_add_right le_rfl)
      · rw [indicator_of_notMem hx,zero_add]
        exact hbound x hx
    _ = μ bad + e := by
      rw [lintegral_add_left (measurable_const.indicator hb),lintegral_indicator_const hb]
      simp

theorem two_exception_product_bound (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (failed : Set (X × Y)) (hf : MeasurableSet failed)
    (badGrid badCycle : Set X) (hg : MeasurableSet badGrid) (hc : MeasurableSet badCycle)
    (g c e : ℝ≥0∞) (hgrid : μ badGrid ≤ g) (hcycle : μ badCycle ≤ c)
    (hbound : ∀ x, x ∉ badGrid → x ∉ badCycle → ν {y | (x,y) ∈ failed} ≤ e) :
    (μ.prod ν) failed ≤ g+c+e := by
  have h := exceptional_product_bound μ ν failed hf (badGrid ∪ badCycle) (hg.union hc) e
    (fun x hx => hbound x (fun hg => hx (Or.inl hg)) (fun hc => hx (Or.inr hc)))
  exact h.trans (add_le_add ((measure_union_le _ _).trans (add_le_add hgrid hcycle)) le_rfl)

end EnvyFreeResearch.Full.RefinedUpperTrialUnion
