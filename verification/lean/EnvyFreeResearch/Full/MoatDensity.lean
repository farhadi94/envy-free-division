import EnvyFreeResearch.Full.NonnegativeInputClass

/-! Concrete integrable moat densities. The protocol lower bound is separate. -/
noncomputable section
namespace EnvyFreeResearch.Full.MoatDensity
open Set MeasureTheory Metric MixedDensity NonnegativeCircle
open scoped ENNReal Classical
abbrev Circle := NonnegativeCircle.Circle

def deviation (w h : ℝ) (c x : Circle) : ℝ :=
  (closedBall c (h/2)).indicator (fun _ => (1/2:ℝ)) x -
    (closedBall c (w/2)).indicator (fun _ => h/(2*w)) x

def density (chores : Bool) (w h : ℝ) (c x : Circle) : ℝ :=
  if chores then 1 - deviation w h c x else 1 + deviation w h c x

theorem deviation_measurable (w h : ℝ) (c : Circle) : Measurable (deviation w h c) :=
  (measurable_const.indicator measurableSet_closedBall).sub
    (measurable_const.indicator measurableSet_closedBall)

theorem density_measurable (chores : Bool) (w h : ℝ) (c : Circle) :
    Measurable (density chores w h c) := by
  cases chores
  · exact measurable_const.add (deviation_measurable w h c)
  · exact measurable_const.sub (deviation_measurable w h c)

theorem deviation_integrable (w h : ℝ) (c : Circle) : Integrable (deviation w h c) volume :=
  ((integrable_const _).indicator measurableSet_closedBall).sub
    ((integrable_const _).indicator measurableSet_closedBall)

theorem density_integrable (chores : Bool) (w h : ℝ) (c : Circle) :
    Integrable (density chores w h c) volume := by
  cases chores
  · exact (integrable_const _).add (deviation_integrable w h c)
  · exact (integrable_const _).sub (deviation_integrable w h c)

theorem coefficient_bounds {w h : ℝ} (hw : 0 < w) (hh : 0 ≤ h) (hhw : h ≤ w) :
    0 ≤ h/(2*w) ∧ h/(2*w) ≤ 1/2 := by
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < 2*w)).mpr
    linarith

theorem deviation_bounds {w h : ℝ} (hw : 0 < w) (hh : 0 ≤ h) (hhw : h ≤ w)
    (c x : Circle) : -(1/2:ℝ) ≤ deviation w h c x ∧ deviation w h c x ≤ 1/2 := by
  obtain ⟨hd0, hd1⟩ := coefficient_bounds hw hh hhw
  by_cases hb : x ∈ closedBall c (h/2) <;>
    by_cases hm : x ∈ closedBall c (w/2) <;>
    simp [deviation, hb, hm] <;> constructor <;> linarith

theorem density_bounds (chores : Bool) {w h : ℝ} (hw : 0 < w) (hh : 0 ≤ h) (hhw : h ≤ w)
    (c x : Circle) : 1/2 ≤ density chores w h c x ∧ density chores w h c x ≤ 3/2 := by
  have hd := deviation_bounds hw hh hhw c x
  cases chores <;> simp only [density, Bool.false_eq_true, ite_false, ite_true] <;> constructor <;> linarith

theorem arc_mass (c : Circle) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    volume.real (closedBall c (v/2)) = v := by
  rw [Measure.real, circle_ball_mass c (v/2) (by linarith)]
  rw [ENNReal.toReal_ofReal (by linarith)]
  ring

theorem deviation_total {w h : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hh : 0 ≤ h) (hhw : h ≤ w) (c : Circle) :
    (∫ x, deviation w h c x) = 0 := by
  simp only [deviation]
  rw [integral_sub
    ((integrable_const _).indicator measurableSet_closedBall)
    ((integrable_const _).indicator measurableSet_closedBall),
    integral_indicator_const _ measurableSet_closedBall,
    integral_indicator_const _ measurableSet_closedBall]
  change volume.real (closedBall c (h/2)) * (1/2) -
    volume.real (closedBall c (w/2)) * (h/(2*w)) = 0
  rw [arc_mass c hh (hhw.trans hw1), arc_mass c hw.le hw1]
  field_simp [hw.ne']
  ring

theorem density_total (chores : Bool) {w h : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hh : 0 ≤ h) (hhw : h ≤ w) (c : Circle) :
    (∫ x, density chores w h c x) = 1 := by
  have hd := deviation_total hw hw1 hh hhw c
  cases chores
  · change (∫ x, 1 + deviation w h c x) = 1
    rw [integral_add (integrable_const _) (deviation_integrable w h c), hd]
    simp
  · change (∫ x, 1 - deviation w h c x) = 1
    rw [integral_sub (integrable_const _) (deviation_integrable w h c), hd]
    simp

/-- Wrapped moat fragments remain physical pieces of the unit interval. -/
def row (chores : Bool) (w h : ℝ) (c : Circle) : Row where
  density := (Icc (0:ℝ) 1).indicator (fun t => density chores w h c (t : Circle))
  integrable := by
    have hmeas := (density_measurable chores w h c).comp AddCircle.measurable_mk'
    have hdom : ∀ t : ℝ, ‖density chores w h c (t : Circle)‖ ≤ 2 + |h/(2*w)| := by
      intro t
      have hb : |(closedBall c (h/2)).indicator (fun _ => (1/2:ℝ)) (t:Circle)| ≤ 1/2 := by
        by_cases ht : (t:Circle) ∈ closedBall c (h/2) <;> simp [ht]
      have hm : |(closedBall c (w/2)).indicator (fun _ => h/(2*w)) (t:Circle)| ≤ |h/(2*w)| := by
        by_cases ht : (t:Circle) ∈ closedBall c (w/2) <;> simp [ht]
      have hd : |deviation w h c (t:Circle)| ≤ 1/2 + |h/(2*w)| :=
        (abs_sub _ _).trans (add_le_add hb hm)
      rw [Real.norm_eq_abs]
      cases chores
      · change |1+deviation w h c (t:Circle)| ≤ _
        have ht := abs_add_le (1:ℝ) (deviation w h c (t:Circle))
        norm_num only [abs_one] at ht
        linarith
      · change |1-deviation w h c (t:Circle)| ≤ _
        have ht := abs_sub (1:ℝ) (deviation w h c (t:Circle))
        norm_num only [abs_one] at ht
        linarith
    have hconst : IntegrableOn (fun _ : ℝ => 2 + |h/(2*w)|) (Icc (0:ℝ) 1) volume :=
      integrableOn_const (by simp : volume (Icc (0:ℝ) 1) ≠ ∞)
    have hint : IntegrableOn (fun t : ℝ => density chores w h c (t : Circle)) (Icc (0:ℝ) 1) volume :=
      hconst.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hdom)
    exact hint.integrable_indicator measurableSet_Icc

theorem row_bounds (chores : Bool) {w h : ℝ} (hw : 0 < w) (hh : 0 ≤ h) (hhw : h ≤ w)
    (c : Circle) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    1/2 ≤ (row chores w h c).density t ∧ (row chores w h c).density t ≤ 3/2 := by
  simpa only [row, indicator_of_mem ht] using density_bounds chores hw hh hhw c (t : Circle)

theorem row_total (chores : Bool) {w h : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hh : 0 ≤ h) (hhw : h ≤ w) (c : Circle) : (row chores w h c).cumulative 1 = 1 := by
  have hmap := integral_map_of_stronglyMeasurable
    (μ := volume.restrict (Ioc (0:ℝ) 1)) AddCircle.measurable_mk'
    (density_measurable chores w h c).stronglyMeasurable
  have hpreserve : Measure.map ((↑) : ℝ → Circle) (volume.restrict (Ioc (0:ℝ) 1)) = volume := by
    simpa using (AddCircle.measurePreserving_mk (1:ℝ) 0).map_eq
  rw [hpreserve, density_total chores hw hw1 hh hhw c] at hmap
  unfold Row.cumulative row
  rw [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num), setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_left.mpr Ioc_subset_Icc_self]
  exact hmap.symm

end EnvyFreeResearch.Full.MoatDensity
