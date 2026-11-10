import EnvyFreeResearch.Full.MoatDensity

/-! Physical integral semantics, admission into the published finite-step
input class, and unique-root positivity for the actual moat rows. -/
noncomputable section
namespace EnvyFreeResearch.Full.MoatPhysical
open Set MeasureTheory Metric MixedDensity NonnegativeInputClass MoatDensity
open scoped Classical ENNReal
abbrev Circle := NonnegativeCircle.Circle

def arcPart (c : Circle) (v : ℝ) (A : Set ℝ) : Set ℝ :=
  (((↑) : ℝ → Circle) ⁻¹' closedBall c (v/2)) ∩ A

theorem row_bundle_value (chores : Bool) (w h : ℝ) (c : Circle)
    (A : Set ℝ) (hA : MeasurableSet A) (hphysical : A ⊆ Icc (0:ℝ) 1) :
    (row chores w h c).signedMeasure A =
      if chores then volume.real A - (volume.real (arcPart c h A)/2 - h/(2*w)*volume.real (arcPart c w A))
      else volume.real A + (volume.real (arcPart c h A)/2 - h/(2*w)*volume.real (arcPart c w A)) := by
  let P := ((↑) : ℝ → Circle) ⁻¹' closedBall c (h/2)
  let N := ((↑) : ℝ → Circle) ⁻¹' closedBall c (w/2)
  have hP : MeasurableSet P := measurableSet_closedBall.preimage AddCircle.measurable_mk'
  have hN : MeasurableSet N := measurableSet_closedBall.preimage AddCircle.measurable_mk'
  have hfinite : volume A ≠ ∞ := measure_ne_top_of_subset hphysical (by simp)
  have hbase : IntegrableOn (fun _ : ℝ => (1:ℝ)) A volume := integrableOn_const hfinite
  have hhalf : IntegrableOn (fun _ : ℝ => (1/2:ℝ)) A volume := integrableOn_const hfinite
  have hdelta : IntegrableOn (fun _ : ℝ => h/(2*w)) A volume := integrableOn_const hfinite
  have hp := hhalf.indicator hP
  have hn := hdelta.indicator hN
  have hdev : IntegrableOn (fun t : ℝ => deviation w h c (t : Circle)) A volume := hp.sub hn
  rw [Row.signedMeasure_apply _ _ hA]
  change (∫ t in A, (Icc (0:ℝ) 1).indicator (fun t => density chores w h c (t : Circle)) t) = _
  rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_left.mpr hphysical]
  have hint : (∫ t in A, deviation w h c (t : Circle)) =
      volume.real (arcPart c h A)/2 - h/(2*w)*volume.real (arcPart c w A) := by
    change (∫ t in A, P.indicator (fun _ => (1/2:ℝ)) t - N.indicator (fun _ => h/(2*w)) t) = _
    rw [integral_sub hp hn, integral_indicator_const _ hP, integral_indicator_const _ hN,
      measureReal_restrict_apply hP, measureReal_restrict_apply hN]
    simp only [arcPart, P, N, smul_eq_mul]
    ring
  cases chores
  · change (∫ t in A, 1 + deviation w h c (t : Circle)) = _
    rw [integral_add hbase hdev, hint]
    simp
  · change (∫ t in A, 1 - deviation w h c (t : Circle)) = _
    rw [integral_sub hbase hdev, hint]
    simp

theorem row_increment_lower (chores : Bool) {w h : ℝ} (hw : 0 < w) (hh : 0 ≤ h)
    (hhw : h ≤ w) (c : Circle) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b-a)/2 ≤ (row chores w h c).cumulative b - (row chores w h c).cumulative a := by
  rw [Row.interval_value _ hab, Row.signedMeasure_apply _ _ measurableSet_Ioc]
  have hconst : IntegrableOn (fun _ : ℝ => (1/2:ℝ)) (Ioc a b) volume :=
    integrableOn_const (by simp : volume (Ioc a b) ≠ ∞)
  have hmono := setIntegral_mono_on hconst (row chores w h c).integrable.integrableOn
    measurableSet_Ioc (fun t ht => (row_bounds chores hw hh hhw c t ⟨ha.trans ht.1.le, ht.2.trans hb⟩).1)
  simpa [setIntegral_const, Real.volume_real_Ioc, max_eq_left (sub_nonneg.mpr hab),
    smul_eq_mul, div_eq_mul_inv, mul_comm] using hmono

theorem row_strictMonoOn (chores : Bool) {w h : ℝ} (hw : 0 < w) (hh : 0 ≤ h)
    (hhw : h ≤ w) (c : Circle) :
    StrictMonoOn (row chores w h c).cumulative (Icc (0:ℝ) 1) := by
  intro a ha b hb hab
  have hbound := row_increment_lower chores hw hh hhw c a b ha.1 hab.le hb.2
  linarith

theorem row_finite_step_real (chores : Bool) (w h c : ℝ)
    (hc : c ∈ Icc (0:ℝ) 1) (hw : w ≤ 1) (hh : h ≤ 1) :
    FiniteStepOnUnit (row chores w h (c : Circle)).density := by
  refine ⟨pulseEndpoints c (h/2) ∪ pulseEndpoints c (w/2), ?_⟩
  intro x hx y hy hcell
  have hB := pulse_membership_constant c (h/2) hc (by linarith) x y hx hy
    (fun e he => hcell e (Finset.mem_union_left _ he))
  have hW := pulse_membership_constant c (w/2) hc (by linarith) x y hx hy
    (fun e he => hcell e (Finset.mem_union_right _ he))
  have indicator_eq (r v : ℝ)
      (hm : (x : Circle) ∈ closedBall (c : Circle) r ↔ (y : Circle) ∈ closedBall (c : Circle) r) :
      (closedBall (c : Circle) r).indicator (fun _ => v) (x : Circle) =
        (closedBall (c : Circle) r).indicator (fun _ => v) (y : Circle) := by
    by_cases hp : (x : Circle) ∈ closedBall (c : Circle) r
    · rw [indicator_of_mem hp, indicator_of_mem (hm.mp hp)]
    · rw [indicator_of_notMem hp, indicator_of_notMem (fun hy => hp (hm.mpr hy))]
  change (Icc (0:ℝ) 1).indicator (fun t => density chores w h (c : Circle) (t : Circle)) x =
    (Icc (0:ℝ) 1).indicator (fun t => density chores w h (c : Circle) (t : Circle)) y
  rw [indicator_of_mem hx, indicator_of_mem hy]
  simp only [density, deviation, indicator_eq _ _ hB, indicator_eq _ _ hW]

theorem row_finite_step (chores : Bool) (w h : ℝ) (c : Circle) (hw : w ≤ 1) (hh : h ≤ 1) :
    FiniteStepOnUnit (row chores w h c).density := by
  have hc := NonnegativeEndpointLaw.representative_range c
  have hs := row_finite_step_real chores w h (NonnegativeEndpointLaw.representative c)
    ⟨hc.1.le, hc.2⟩ hw hh
  simpa only [NonnegativeEndpointLaw.representative_coe] using hs

theorem row_admissible (chores : Bool) {w h : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hh : 0 ≤ h) (hhw : h ≤ w) (c : Circle) : AdmissibleRow (row chores w h c) := by
  refine ⟨row_total chores hw hw1 hh hhw c, ?_, row_finite_step chores w h c hw1 (hhw.trans hw1)⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact row_bounds chores hw hh hhw c x hx

end EnvyFreeResearch.Full.MoatPhysical
