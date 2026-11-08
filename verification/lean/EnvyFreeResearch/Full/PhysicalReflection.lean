import EnvyFreeResearch.Full.IntervalValues

/-! Reflection of actual integrable signed densities. Interval endpoints
have zero value, so the physical reflection preserves all bundle values. -/

noncomputable section
namespace EnvyFreeResearch.Full.PhysicalReflection
open Set MeasureTheory MixedDensity MixedObstruction

def reflectPoint (x : ℝ) : ℝ := 1 - x

@[simp] theorem reflectPoint_involutive (x : ℝ) :
    reflectPoint (reflectPoint x) = x := by simp [reflectPoint]

theorem measurable_reflectPoint : Measurable reflectPoint :=
  measurable_const.sub measurable_id

def reflectionEquiv : ℝ ≃ᵐ ℝ where
  toFun := reflectPoint
  invFun := reflectPoint
  left_inv := reflectPoint_involutive
  right_inv := reflectPoint_involutive
  measurable_toFun := measurable_reflectPoint
  measurable_invFun := measurable_reflectPoint

def reflectRow (R : Row) : Row where
  density := fun x => R.density (reflectPoint x)
  integrable := R.integrable.comp_sub_left 1

@[simp] theorem reflectRow_cumulative (R : Row) (x : ℝ) :
    (reflectRow R).cumulative x = R.cumulative 1 - R.cumulative (1 - x) := by
  change (∫ t in (0 : ℝ)..x, R.density (1 - t)) = _
  rw [intervalIntegral.integral_comp_sub_left, sub_zero]
  have h := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := 1 - x) (c := 1)
    R.integrable.intervalIntegrable R.integrable.intervalIntegrable
  unfold Row.cumulative
  linarith

theorem reflectPoint_domain : reflectPoint ⁻¹' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
  ext x
  simp only [mem_preimage, mem_Icc, reflectPoint]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem reflectPoint_preserves_domain :
    MeasurePreserving reflectPoint domainMeasure domainMeasure := by
  have h : MeasurePreserving reflectPoint volume volume := volume.measurePreserving_sub_left 1
  have hr := h.restrict_preimage (s := Icc (0 : ℝ) 1) measurableSet_Icc
  rw [reflectPoint_domain] at hr
  simpa only [domainMeasure, restrict_Ioc_eq_restrict_Icc] using hr

/-- Reflection transports the value of every measurable physical set. -/
theorem reflected_value (R : Row) (A : Set ℝ) (hA : MeasurableSet A) :
    value (reflectRow R) A = value R (reflectPoint ⁻¹' A) := by
  have h := reflectPoint_preserves_domain.integral_comp
    reflectionEquiv.measurableEmbedding
    (A.indicator (reflectRow R).density)
  rw [integral_indicator hA] at h
  unfold value
  rw [← h, ← integral_indicator (hA.preimage measurable_reflectPoint)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : reflectPoint x ∈ A
  · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ reflectPoint ⁻¹' A from hx)]
    simp only [reflectRow, reflectPoint_involutive]
  · rw [indicator_of_notMem hx,
      indicator_of_notMem (show x ∉ reflectPoint ⁻¹' A from hx)]

end EnvyFreeResearch.Full.PhysicalReflection
