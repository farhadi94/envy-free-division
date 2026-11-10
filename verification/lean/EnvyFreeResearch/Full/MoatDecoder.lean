import EnvyFreeResearch.Full.MoatPhysical

/-! The moat decoder uses width strictly greater than the uniform bundle
length. This removes the exceptional equal-arc case; the sharp bound follows
by a later limit in the moat width. -/
noncomputable section
namespace EnvyFreeResearch.Full.MoatDecoder
open Set MeasureTheory Metric IntervalAllocation MixedDensity
open MoatDensity MoatPhysical NonnegativeAllocation NonnegativeAllocationDecoder
open scoped Classical ENNReal
abbrev Circle := NonnegativeCircle.Circle

/-- Both orientations fail at a nonowner of the narrow pulse. No connectedness
or uniform component-count restriction on the physical allocation is used. -/
theorem strict_envy {Agent : Type*} (chores : Bool) (A : Allocation Agent)
    (w h c : ℝ) (hw : 0 < w) (hh : 0 < h)
    (hc0 : 0 < c-h/2) (hc1 : c+h/2 < 1)
    (hleft : ∀ k, h/2 < |c-A.left k|) (hright : ∀ k, h/2 < |c-A.right k|)
    (i : Agent) (hi : i ≠ ownerAt A c)
    (hequal : volume.real (A.share i) = volume.real (A.share (ownerAt A c)))
    (hmoat : volume.real (A.share (ownerAt A c)) < w) :
    if chores then
      (row true w h (c:Circle)).signedMeasure (A.share (ownerAt A c)) <
        (row true w h (c:Circle)).signedMeasure (A.share i)
    else
      (row false w h (c:Circle)).signedMeasure (A.share i) <
        (row false w h (c:Circle)).signedMeasure (A.share (ownerAt A c)) := by
  have hpulse (j : Agent) : volume.real (arcPart (c:Circle) h (A.share j)) =
      if j = ownerAt A c then h else 0 := by
    have hs := pulse_share_mass A c (h/2) (by linarith) hc0 hc1 hleft hright j
    change volume.real (arcPart (c:Circle) h (A.share j)) = _ at hs
    convert hs using 1 <;> split_ifs <;> ring
  have hnonneg : 0 ≤ volume.real (arcPart (c:Circle) w (A.share i)) := measureReal_nonneg
  have hmass : volume.real (arcPart (c:Circle) w (A.share (ownerAt A c))) < w :=
    (measureReal_mono (show arcPart (c:Circle) w (A.share (ownerAt A c)) ⊆ A.share (ownerAt A c)
      from inter_subset_right) (measure_ne_top_of_subset (share_subset A _) (by simp))).trans_lt hmoat
  have hdelta : 0 < h/(2*w) := by positivity
  have hmul := mul_lt_mul_of_pos_left hmass hdelta
  have hcancel : h/(2*w)*w=h/2 := by field_simp
  rw [hcancel] at hmul
  have hnonneg' := mul_nonneg hdelta.le hnonneg
  cases chores <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    rw [row_bundle_value _ _ _ _ _ (A.share_measurable _) (share_subset A _),
      row_bundle_value _ _ _ _ _ (A.share_measurable _) (share_subset A _)] <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, hpulse, hi, ite_true, hequal] <;> linarith

theorem arcPart_unit_mass (c : Circle) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    volume.real (arcPart c v (Icc (0:ℝ) 1)) = v := by
  have heq := AddCircle.add_projection_respects_measure (1:ℝ) 0
    (measurableSet_closedBall : MeasurableSet (closedBall c (v/2)))
  have hae : (((↑) : ℝ → Circle) ⁻¹' closedBall c (v/2)) ∩ Ioc (0:ℝ) 1 =ᵐ[volume]
      arcPart c v (Icc (0:ℝ) 1) := by
    filter_upwards [Ioc_ae_eq_Icc (a := (0:ℝ)) (b := 1) (μ := volume)] with x hx
    simp only [arcPart, mem_inter_iff]
    exact propext (and_congr Iff.rfl (Iff.of_eq hx))
  simp only [zero_add] at heq
  rw [measure_congr hae] at heq
  have hreal := congrArg ENNReal.toReal heq
  change volume.real (closedBall c (v/2)) = volume.real (arcPart c v (Icc (0:ℝ) 1)) at hreal
  exact hreal.symm.trans (arc_mass c hv0 hv1)

theorem arcPart_mass_le (c : Circle) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (A : Set ℝ) (hphysical : A ⊆ Icc (0:ℝ) 1) :
    volume.real (arcPart c v A) ≤ v := by
  have hsubset : arcPart c v A ⊆ arcPart c v (Icc (0:ℝ) 1) := inter_subset_inter_right _ hphysical
  have hfinite : volume (arcPart c v (Icc (0:ℝ) 1)) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_right (by simp)
  exact (measureReal_mono hsubset hfinite).trans_eq (arcPart_unit_mass c hv0 hv1)

/-- Every measurable bundle moves by at most h/2, including wrapped moats. -/
theorem bundle_change_abs_le (chores : Bool) {w h : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hh : 0 ≤ h) (hhw : h ≤ w) (c : Circle)
    (A : Set ℝ) (hA : MeasurableSet A) (hphysical : A ⊆ Icc (0:ℝ) 1) :
    |(row chores w h c).signedMeasure A-volume.real A| ≤ h/2 := by
  have hb := arcPart_mass_le c hh (hhw.trans hw1) A hphysical
  have hm := arcPart_mass_le c hw.le hw1 A hphysical
  have hb0 : 0 ≤ volume.real (arcPart c h A) := measureReal_nonneg
  have hm0 : 0 ≤ volume.real (arcPart c w A) := measureReal_nonneg
  have hdelta : 0 ≤ h/(2*w) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hm hdelta
  have hcancel : h/(2*w)*w=h/2 := by field_simp
  rw [hcancel] at hmul
  have hmul0 := mul_nonneg hdelta hm0
  rw [row_bundle_value chores w h c A hA hphysical]
  cases chores <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> rw [abs_le] <;> constructor <;> linarith

end EnvyFreeResearch.Full.MoatDecoder
