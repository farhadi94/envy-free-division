import EnvyFreeResearch.Full.NonnegativePulse
import EnvyFreeResearch.Full.NonnegativeGeometry

namespace EnvyFreeResearch.Full.NonnegativePulseGeometry

open MeasureTheory Set Metric
open scoped ENNReal
open NonnegativePulse MixedDensity

abbrev Circle := NonnegativeCircle.Circle

/-- Avoiding the physical endpoints makes a circular bump an ordinary real
interval on the cake. Wrapped parameter values are still allowed by the
global law; this conclusion is used only on the good endpoint event. -/
theorem nonwrapping_support (c r : ℝ) (hr : 0 ≤ r)
    (hleft : 0 < c - r) (hright : c + r < 1) :
    ((((↑) : ℝ → Circle) ⁻¹' closedBall (c : Circle) r) ∩ Icc (0 : ℝ) 1) =
      Icc (c - r) (c + r) := by
  have hc : c ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [pulse_support_three_intervals c r hc (by linarith)]
  ext t
  simp only [mem_iUnion, Finset.mem_insert, Finset.mem_singleton, mem_inter_iff]
  constructor
  · rintro ⟨k, hk, hball, hphysical⟩
    rcases hk with rfl | rfl | rfl
    · norm_num at hball
      linarith [hball.2, hphysical.1]
    · simpa using hball
    · norm_num at hball
      linarith [hball.1, hphysical.2]
  · intro ht
    refine ⟨0, by simp, by simpa using ht, ?_⟩
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- A real bump avoiding both interval endpoints is entirely inside or
entirely outside that interval, according to its center. -/
theorem ball_interval_membership (c r a b t : ℝ) (_hr : 0 ≤ r)
    (ha : r < |c - a|) (hb : r < |c - b|)
    (ht : t ∈ Icc (c - r) (c + r)) :
    t ∈ Ioc a b ↔ c ∈ Ioc a b := by
  have hleft : a < t ↔ a < c := by
    by_cases hac : a < c
    · rw [abs_of_pos (sub_pos.mpr hac)] at ha
      constructor
      · exact fun _ => hac
      · intro _
        linarith [ht.1]
    · have hca : c ≤ a := le_of_not_gt hac
      rw [abs_of_nonpos (sub_nonpos.mpr hca)] at ha
      constructor
      · intro hat
        exfalso
        linarith [ht.2]
      · exact fun h => False.elim (hac h)
  have hright : t ≤ b ↔ c ≤ b := by
    by_cases hcb : c ≤ b
    · rw [abs_of_nonpos (sub_nonpos.mpr hcb)] at hb
      constructor
      · exact fun _ => hcb
      · intro _
        linarith [ht.2]
    · have hbc : b < c := lt_of_not_ge hcb
      rw [abs_of_pos (sub_pos.mpr hbc)] at hb
      constructor
      · intro htb
        exfalso
        linarith [ht.1]
      · exact fun h => False.elim (hcb h)
  exact and_congr hleft hright

theorem pulse_interval_support (c r a b : ℝ) (hr : 0 ≤ r)
    (hleft : 0 < c - r) (hright : c + r < 1)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (havoidA : r < |c - a|) (havoidB : r < |c - b|) :
    (((↑) : ℝ → Circle) ⁻¹' closedBall (c : Circle) r) ∩ Ioc a b =
      if c ∈ Ioc a b then Icc (c - r) (c + r) else ∅ := by
  classical
  have hnowrap := nonwrapping_support c r hr hleft hright
  ext t
  by_cases hc : c ∈ Ioc a b
  · simp only [ite_eq_left hc, mem_inter_iff]
    constructor
    · intro ht
      have hphysical : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans ht.2.1.le, ht.2.2.trans hb⟩
      exact hnowrap ▸ ⟨ht.1, hphysical⟩
    · intro ht
      have hsource : t ∈ (((↑) : ℝ → Circle) ⁻¹' closedBall (c : Circle) r) ∩ Icc (0 : ℝ) 1 :=
        hnowrap.symm ▸ ht
      exact ⟨hsource.1, (ball_interval_membership c r a b t hr havoidA havoidB ht).mpr hc⟩
  · simp only [ite_eq_right hc, mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hp hi
    have hphysical : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hi.1.le, hi.2.trans hb⟩
    have ht : t ∈ Icc (c - r) (c + r) := hnowrap ▸ ⟨hp, hphysical⟩
    exact hc ((ball_interval_membership c r a b t hr havoidA havoidB ht).mp hi)

theorem pulse_interval_mass (c r a b : ℝ) (hr : 0 ≤ r)
    (hleft : 0 < c - r) (hright : c + r < 1)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (havoidA : r < |c - a|) (havoidB : r < |c - b|) :
    volume.real ((((↑) : ℝ → Circle) ⁻¹' closedBall (c : Circle) r) ∩ Ioc a b) =
      if c ∈ Ioc a b then 2 * r else 0 := by
  rw [pulse_interval_support c r a b hr hleft hright ha hb havoidA havoidB]
  split_ifs
  · rw [Real.volume_real_Icc, max_eq_left (by linarith)]
    ring
  · simp

/-- Exact integral cancellation for a query that does not separate the two
centers and whose endpoints and physical endpoints avoid both bumps. -/
theorem interval_preserved (h c d a b : ℝ) (hh : 0 ≤ h)
    (hc0 : 0 < c - h / 2) (hc1 : c + h / 2 < 1)
    (hd0 : 0 < d - h / 2) (hd1 : d + h / 2 < 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hca : h / 2 < |c - a|) (hcb : h / 2 < |c - b|)
    (hda : h / 2 < |d - a|) (hdb : h / 2 < |d - b|)
    (hseparation : c ∈ Ioc a b ↔ d ∈ Ioc a b) :
    (row h (c : Circle) (d : Circle)).cumulative b -
      (row h (c : Circle) (d : Circle)).cumulative a = b - a := by
  rw [Row.interval_value _ hab, row_bundle_value _ _ _ _ measurableSet_Ioc
    (fun t ht => ⟨ha.trans ht.1.le, ht.2.trans hb⟩)]
  rw [pulse_interval_mass c (h / 2) a b (by linarith) hc0 hc1 ha hb hca hcb,
    pulse_interval_mass d (h / 2) a b (by linarith) hd0 hd1 ha hb hda hdb,
    Real.volume_real_Ioc, max_eq_left (sub_nonneg.mpr hab)]
  by_cases hc : c ∈ Ioc a b
  · rw [ite_eq_left hc, ite_eq_left (hseparation.mp hc)]
    ring
  · rw [ite_eq_right hc, ite_eq_right (fun hd => hc (hseparation.mpr hd))]
    ring

/-- The actual value of any measurable physical bundle changes by at most
half the pulse width. No fragmentation premise enters this estimate. -/
theorem bundle_change_abs_le (h c d : ℝ) (hh : 0 ≤ h)
    (hc0 : 0 < c - h / 2) (hc1 : c + h / 2 < 1)
    (hd0 : 0 < d - h / 2) (hd1 : d + h / 2 < 1)
    (A : Set ℝ) (hA : MeasurableSet A) (hphysical : A ⊆ Icc (0 : ℝ) 1) :
    |(row h (c : Circle) (d : Circle)).signedMeasure A - volume.real A| ≤ h / 2 := by
  have hbound (x : ℝ) (hx0 : 0 < x - h / 2) (hx1 : x + h / 2 < 1) :
      volume.real ((((↑) : ℝ → Circle) ⁻¹' closedBall (x : Circle) (h / 2)) ∩ A) ≤ h := by
    have hsub : ((((↑) : ℝ → Circle) ⁻¹' closedBall (x : Circle) (h / 2)) ∩ A) ⊆
        ((((↑) : ℝ → Circle) ⁻¹' closedBall (x : Circle) (h / 2)) ∩ Icc (0 : ℝ) 1) :=
      Set.inter_subset_inter_right _ hphysical
    have hfinite : volume ((((↑) : ℝ → Circle) ⁻¹' closedBall (x : Circle) (h / 2)) ∩
        Icc (0 : ℝ) 1) ≠ ∞ := measure_ne_top_of_subset inter_subset_right (by simp)
    have hm := measureReal_mono hsub hfinite
    rw [nonwrapping_support x (h / 2) (by linarith) hx0 hx1, Real.volume_real_Icc,
      max_eq_left (by linarith)] at hm
    convert hm using 1 <;> ring
  rw [row_bundle_value _ _ _ _ hA hphysical, abs_le]
  have hc := hbound c hc0 hc1
  have hd := hbound d hd0 hd1
  have hcn : 0 ≤ volume.real ((((↑) : ℝ → Circle) ⁻¹'
      closedBall (c : Circle) (h / 2)) ∩ A) := measureReal_nonneg
  have hdn : 0 ≤ volume.real ((((↑) : ℝ → Circle) ⁻¹'
      closedBall (d : Circle) (h / 2)) ∩ A) := measureReal_nonneg
  constructor <;> linarith

/-- Every old strict uniform comparison with gap larger than the pulse
width survives on the same replayed physical output. -/
theorem old_strict_gap_preserved (h c d : ℝ) (hh : 0 ≤ h)
    (hc0 : 0 < c - h / 2) (hc1 : c + h / 2 < 1)
    (hd0 : 0 < d - h / 2) (hd1 : d + h / 2 < 1)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hphysicalA : A ⊆ Icc (0 : ℝ) 1) (hphysicalB : B ⊆ Icc (0 : ℝ) 1)
    (hgap : volume.real A + h < volume.real B) :
    (row h (c : Circle) (d : Circle)).signedMeasure A <
      (row h (c : Circle) (d : Circle)).signedMeasure B := by
  have hAv := abs_le.mp (bundle_change_abs_le h c d hh hc0 hc1 hd0 hd1 A hA hphysicalA)
  have hBv := abs_le.mp (bundle_change_abs_le h c d hh hc0 hc1 hd0 hd1 B hB hphysicalB)
  linarith [hAv.2, hBv.1]

end EnvyFreeResearch.Full.NonnegativePulseGeometry

#print axioms EnvyFreeResearch.Full.NonnegativePulseGeometry.nonwrapping_support
#print axioms EnvyFreeResearch.Full.NonnegativePulseGeometry.pulse_interval_mass
#print axioms EnvyFreeResearch.Full.NonnegativePulseGeometry.interval_preserved
#print axioms EnvyFreeResearch.Full.NonnegativePulseGeometry.old_strict_gap_preserved
