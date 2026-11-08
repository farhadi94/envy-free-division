import Mathlib

/-! An original-tape product bound using three exceptional events. The good
set is defined by the measurable actual fresh-trial probability, so the
exceptional supported-union event need not itself be proved measurable. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem three_exception_product_bound (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (success : Set (X × Y)) (hs : MeasurableSet success)
    (badZero badCandidates badInterpolation : Set X)
    (hz : μ badZero ≤ ENNReal.ofReal ((1:ℝ)/64))
    (hc : μ badCandidates ≤ ENNReal.ofReal ((1:ℝ)/4))
    (hi : μ badInterpolation ≤ ENNReal.ofReal ((1:ℝ)/64))
    (hfiber : ∀ x, x ∉ badZero → x ∉ badCandidates → x ∉ badInterpolation →
      ENNReal.ofReal ((3:ℝ)/8) ≤ ν {y | (x,y) ∈ success}) :
    (1:ℝ)/4 < (μ.prod ν).real success := by
  let good : Set X := {x | ENNReal.ofReal ((3:ℝ)/8) ≤ ν {y | (x,y) ∈ success}}
  have hgood : MeasurableSet good :=
    measurableSet_le measurable_const (measurable_measure_prodMk_left hs)
  have hcover : goodᶜ ⊆ (badZero ∪ badCandidates) ∪ badInterpolation := by
    intro x hx
    by_contra hn
    have hnot := not_or.mp hn
    have hfirst := not_or.mp hnot.1
    exact hx (hfiber x hfirst.1 hfirst.2 hnot.2)
  have hbad : μ goodᶜ ≤ ENNReal.ofReal ((9:ℝ)/32) := by
    calc
      μ goodᶜ ≤ μ ((badZero ∪ badCandidates) ∪ badInterpolation) := measure_mono hcover
      _ ≤ (μ badZero + μ badCandidates) + μ badInterpolation :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal ((1:ℝ)/64)+ENNReal.ofReal ((1:ℝ)/4)+ENNReal.ofReal ((1:ℝ)/64) :=
        add_le_add (add_le_add hz hc) hi
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
  have hmass : (23:ℝ)/32 ≤ μ.real good := by
    have hbr := ENNReal.toReal_mono (by simp) hbad
    have hsum := congrArg ENNReal.toReal ((measure_add_measure_compl hgood).trans (measure_univ (μ:=μ)))
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hsum
    norm_num at hsum hbr
    change 23/32 ≤ (μ good).toReal
    linarith
  have hlower : ENNReal.ofReal ((3:ℝ)/8) * μ good ≤ (μ.prod ν) success := by
    rw [← lintegral_indicator_const hgood,Measure.prod_apply hs]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ good
    · rw [indicator_of_mem hx]
      change ENNReal.ofReal ((3:ℝ)/8) ≤ ν {y | (x,y) ∈ success}
      exact hx
    · simp only [indicator_of_notMem hx]
      exact zero_le
  have hlowerR := ENNReal.toReal_mono (measure_ne_top _ _) hlower
  rw [ENNReal.toReal_mul] at hlowerR
  norm_num at hlowerR
  change 1/4 < ((μ.prod ν) success).toReal
  change 23/32 ≤ (μ good).toReal at hmass
  nlinarith
end EnvyFreeResearch.Full.UpperSnapshotProtocol
