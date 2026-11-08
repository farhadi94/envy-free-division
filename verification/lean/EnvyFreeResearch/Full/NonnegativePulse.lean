import EnvyFreeResearch.Full.NonnegativeCircle
import EnvyFreeResearch.Full.MixedDensity

/-!
# Actual normalized bounded pulse densities

The pulse row is an integrable real density supported on the physical cake
`[0,1]`, with values in `[1/2,3/2]` there. Its circular pulse supports have an
explicit representation by three ordinary intervals after restriction to
the cake; hence the construction is a finite-step density, including wrapped
arcs and overlapping opposite pulses.
-/

namespace EnvyFreeResearch.Full.NonnegativePulse

open MeasureTheory Set Metric
open scoped ENNReal

abbrev Circle := NonnegativeCircle.Circle
open MixedDensity

noncomputable def circleDensity (h : ℝ) (positive negative : Circle) (x : Circle) : ℝ :=
  1 + (closedBall positive (h / 2)).indicator (fun _ => (1 / 2 : ℝ)) x -
    (closedBall negative (h / 2)).indicator (fun _ => (1 / 2 : ℝ)) x

theorem circleDensity_measurable (h : ℝ) (positive negative : Circle) :
    Measurable (circleDensity h positive negative) :=
  (measurable_const.add (measurable_const.indicator measurableSet_closedBall)).sub
    (measurable_const.indicator measurableSet_closedBall)

theorem circleDensity_integrable (h : ℝ) (positive negative : Circle) :
    Integrable (circleDensity h positive negative) volume :=
  ((integrable_const 1).add ((integrable_const (1 / 2 : ℝ)).indicator measurableSet_closedBall)).sub
    ((integrable_const (1 / 2 : ℝ)).indicator measurableSet_closedBall)

theorem circleDensity_bounds (h : ℝ) (positive negative x : Circle) :
    1 / 2 ≤ circleDensity h positive negative x ∧
      circleDensity h positive negative x ≤ 3 / 2 := by
  classical
  by_cases hp : x ∈ closedBall positive (h / 2) <;>
    by_cases hn : x ∈ closedBall negative (h / 2) <;>
    norm_num [circleDensity, hp, hn]

theorem circleDensity_total (h : ℝ) (positive negative : Circle) :
    (∫ x : Circle, circleDensity h positive negative x) = 1 := by
  have hp : Integrable ((closedBall positive (h / 2)).indicator (fun _ => (1 / 2 : ℝ))) volume :=
    (integrable_const _).indicator measurableSet_closedBall
  have hn : Integrable ((closedBall negative (h / 2)).indicator (fun _ => (1 / 2 : ℝ))) volume :=
    (integrable_const _).indicator measurableSet_closedBall
  have hsub := integral_sub ((integrable_const (1 : ℝ)).add hp) hn
  have hadd := integral_add (integrable_const (1 : ℝ)) hp
  simp only [Pi.add_apply] at hsub hadd
  unfold circleDensity
  rw [hsub, hadd, integral_indicator_const _ measurableSet_closedBall,
    integral_indicator_const _ measurableSet_closedBall]
  simp [Measure.real, AddCircle.volume_closedBall]

noncomputable def row (h : ℝ) (positive negative : Circle) : Row where
  density := (Icc (0 : ℝ) 1).indicator (fun t => circleDensity h positive negative (t : Circle))
  integrable := by
    have hmeas : Measurable (fun t : ℝ => circleDensity h positive negative (t : Circle)) :=
      (circleDensity_measurable h positive negative).comp AddCircle.measurable_mk'
    have hint : IntegrableOn (fun _ : ℝ => (3 / 2 : ℝ)) (Icc (0 : ℝ) 1) volume :=
      integrableOn_const (by simp : volume (Icc (0 : ℝ) 1) ≠ ∞)
    have hint' : IntegrableOn (fun t : ℝ => circleDensity h positive negative (t : Circle))
        (Icc (0 : ℝ) 1) volume := by
      apply hint.mono' hmeas.aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro t
      have hb := circleDensity_bounds h positive negative (t : Circle)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hb.1])]
      exact hb.2
    exact hint'.integrable_indicator measurableSet_Icc

theorem row_bounds (h : ℝ) (positive negative : Circle) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    1 / 2 ≤ (row h positive negative).density t ∧
      (row h positive negative).density t ≤ 3 / 2 := by
  simpa only [row, indicator_of_mem ht] using circleDensity_bounds h positive negative (t : Circle)

theorem row_total (h : ℝ) (positive negative : Circle) :
    (row h positive negative).cumulative 1 = 1 := by
  have hmap := integral_map_of_stronglyMeasurable
    (μ := volume.restrict (Ioc (0 : ℝ) 1)) AddCircle.measurable_mk'
    (circleDensity_measurable h positive negative).stronglyMeasurable
  have hpreserve := (AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq
  have hmap' : (∫ t in Ioc (0 : ℝ) 1, circleDensity h positive negative (t : Circle)) = 1 := by
    have hpreserve' : Measure.map ((↑) : ℝ → Circle) (volume.restrict (Ioc (0 : ℝ) 1)) = volume := by
      simpa using hpreserve
    rw [hpreserve', circleDensity_total] at hmap
    exact hmap.symm
  unfold Row.cumulative row
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    setIntegral_indicator measurableSet_Icc]
  rw [Set.inter_eq_left.mpr Ioc_subset_Icc_self]
  exact hmap'

/-- Quantitative strict positivity, stated for the actual cumulative oracle
function, supplies uniqueness of every legal root-only Cut answer. -/
theorem row_increment_lower (h : ℝ) (positive negative : Circle)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a) / 2 ≤ (row h positive negative).cumulative b -
      (row h positive negative).cumulative a := by
  rw [Row.interval_value _ hab, Row.signedMeasure_apply _ _ measurableSet_Ioc]
  have hconst : IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ)) (Ioc a b) volume :=
    integrableOn_const (by simp : volume (Ioc a b) ≠ ∞)
  have hmono := setIntegral_mono_on hconst (row h positive negative).integrable.integrableOn
    measurableSet_Ioc (fun t ht => (row_bounds h positive negative t
      ⟨ha.trans ht.1.le, ht.2.trans hb⟩).1)
  simpa [setIntegral_const, Real.volume_real_Ioc, max_eq_left (sub_nonneg.mpr hab),
    smul_eq_mul, div_eq_mul_inv, mul_comm] using hmono

theorem row_cumulative_strictMonoOn (h : ℝ) (positive negative : Circle) :
    StrictMonoOn (row h positive negative).cumulative (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hbound := row_increment_lower h positive negative a b ha.1 hab.le hb.2
  linarith

/-- Literal values under the actual pulse density, for every measurable
physical bundle. This is the measure-theoretic utility identity underlying
both oracle replay and the cake/chore envy decoder. -/
theorem row_bundle_value (h : ℝ) (positive negative : Circle)
    (A : Set ℝ) (hA : MeasurableSet A) (hphysical : A ⊆ Icc (0 : ℝ) 1) :
    (row h positive negative).signedMeasure A = volume.real A +
      volume.real ((((↑) : ℝ → Circle) ⁻¹' closedBall positive (h / 2)) ∩ A) / 2 -
      volume.real ((((↑) : ℝ → Circle) ⁻¹' closedBall negative (h / 2)) ∩ A) / 2 := by
  let P := ((↑) : ℝ → Circle) ⁻¹' closedBall positive (h / 2)
  let N := ((↑) : ℝ → Circle) ⁻¹' closedBall negative (h / 2)
  have hP : MeasurableSet P := measurableSet_closedBall.preimage AddCircle.measurable_mk'
  have hN : MeasurableSet N := measurableSet_closedBall.preimage AddCircle.measurable_mk'
  have hfinite : volume A ≠ ∞ := measure_ne_top_of_subset hphysical (by simp)
  have hbase : IntegrableOn (fun _ : ℝ => (1 : ℝ)) A volume := integrableOn_const hfinite
  have hhalf : IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ)) A volume := integrableOn_const hfinite
  have hp := hhalf.indicator hP
  have hn := hhalf.indicator hN
  have hsub := integral_sub (hbase.add hp) hn
  have hadd := integral_add hbase hp
  simp only [Pi.add_apply] at hsub hadd
  rw [Row.signedMeasure_apply _ _ hA]
  change (∫ t in A, (Icc (0 : ℝ) 1).indicator
    (fun t => circleDensity h positive negative (t : Circle)) t) = _
  rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_left.mpr hphysical]
  change (∫ t in A, 1 + P.indicator (fun _ => (1 / 2 : ℝ)) t -
    N.indicator (fun _ => (1 / 2 : ℝ)) t) = _
  rw [hsub, hadd, integral_indicator_const _ hP, integral_indicator_const _ hN]
  rw [measureReal_restrict_apply hP, measureReal_restrict_apply hN]
  simp only [setIntegral_const, smul_eq_mul, mul_one, one_mul, P, N, div_eq_mul_inv]

/-- On the physical interval, every circular pulse is exactly a union of at
most three ordinary interval pieces. This is an explicit finite-step support
description, valid even for a pulse crossing the identified endpoint. -/
theorem pulse_support_three_intervals (center radius : ℝ)
    (hc : center ∈ Icc (0 : ℝ) 1) (hr : radius < 1) :
    (((↑) : ℝ → Circle) ⁻¹' closedBall (center : Circle) radius) ∩ Icc (0 : ℝ) 1 =
      ⋃ k ∈ ({-1, 0, 1} : Finset ℤ),
        (Icc (center + (k : ℝ) - radius) (center + (k : ℝ) + radius) ∩ Icc (0 : ℝ) 1) := by
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion]
  ext t
  simp only [mem_inter_iff, mem_iUnion, Real.closedBall_eq_Icc, zsmul_eq_mul, mul_one]
  constructor
  · rintro ⟨⟨k, hk⟩, ht⟩
    have hklo : (-2 : ℝ) < (k : ℝ) := by linarith [hk.2, ht.1, hc.2]
    have hkhi : (k : ℝ) < 2 := by linarith [hk.1, ht.2, hc.1]
    have hlo : (-2 : ℤ) < k := by exact_mod_cast hklo
    have hhi : k < (2 : ℤ) := by exact_mod_cast hkhi
    have hkfinite : k = -1 ∨ k = 0 ∨ k = 1 := by omega
    exact ⟨k, by simp [hkfinite], hk, ht⟩
  · rintro ⟨k, _, hk, ht⟩
    exact ⟨⟨k, hk⟩, ht⟩

end EnvyFreeResearch.Full.NonnegativePulse

#print axioms EnvyFreeResearch.Full.NonnegativePulse.row_bounds
#print axioms EnvyFreeResearch.Full.NonnegativePulse.row_total
#print axioms EnvyFreeResearch.Full.NonnegativePulse.row_cumulative_strictMonoOn
#print axioms EnvyFreeResearch.Full.NonnegativePulse.row_bundle_value
#print axioms EnvyFreeResearch.Full.NonnegativePulse.pulse_support_three_intervals
