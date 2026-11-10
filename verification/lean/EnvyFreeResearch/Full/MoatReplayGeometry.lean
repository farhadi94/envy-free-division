import EnvyFreeResearch.Full.MoatPhysical

/-! Exact preservation of determining integrals outside the moat. The
argument includes wrapped moats, ordinary forward Cuts, and flag brackets. -/
noncomputable section
namespace EnvyFreeResearch.Full.MoatReplayGeometry
open Set MeasureTheory Metric MixedDensity MoatDensity MoatPhysical
open NonnegativePulseGeometry
open scoped Classical
abbrev Circle := NonnegativeCircle.Circle

theorem real_avoid (c r a : ℝ) (ha : (a:Circle) ∉ closedBall (c:Circle) r) (k : ℤ) :
    r < |c+(k:ℝ)-a| := by
  by_contra h
  have hle : |a-(c+(k:ℝ))| ≤ r := by simpa only [abs_sub_comm] using le_of_not_gt h
  apply ha
  change a ∈ ((↑) : ℝ → Circle) ⁻¹' closedBall (c:Circle) r
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion]
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  simpa only [mem_closedBall, Real.dist_eq, zsmul_eq_mul, mul_one] using hle

theorem circular_interval_support (c r a b : ℝ) (hr : 0 ≤ r)
    (hc0 : 0 < c) (hc1 : c < 1) (ha : 0 ≤ a) (hb : b ≤ 1)
    (havoidA : (a:Circle) ∉ closedBall (c:Circle) r)
    (havoidB : (b:Circle) ∉ closedBall (c:Circle) r) :
    (((↑) : ℝ → Circle) ⁻¹' closedBall (c:Circle) r) ∩ Ioc a b =
      if c ∈ Ioc a b then Icc (c-r) (c+r) else ∅ := by
  have hshift (t : ℝ) (ht : t ∈ Ioc a b)
      (hp : (t:Circle) ∈ closedBall (c:Circle) r) : t ∈ Icc (c-r) (c+r) := by
    change t ∈ ((↑) : ℝ → Circle) ⁻¹' closedBall (c:Circle) r at hp
    rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hp
    obtain ⟨k, hk⟩ := mem_iUnion.mp hp
    have hkball : t ∈ Icc (c+(k:ℝ)-r) (c+(k:ℝ)+r) := by
      simpa only [Real.closedBall_eq_Icc, zsmul_eq_mul, mul_one] using hk
    have hcint := (ball_interval_membership (c+(k:ℝ)) r a b t hr
      (real_avoid c r a havoidA k) (real_avoid c r b havoidB k) hkball).mp ht
    have hk0 : k=0 := by
      have hlo : (-1:ℝ) < (k:ℝ) := by linarith [hcint.1]
      have hhi : (k:ℝ) < 1 := by linarith [hcint.2]
      have hlo' : (-1:ℤ) < k := by exact_mod_cast hlo
      have hhi' : k < (1:ℤ) := by exact_mod_cast hhi
      omega
    simpa only [hk0, Int.cast_zero, add_zero] using hkball
  have hrealA : r < |c-a| := by simpa using real_avoid c r a havoidA 0
  have hrealB : r < |c-b| := by simpa using real_avoid c r b havoidB 0
  ext t
  by_cases hc : c ∈ Ioc a b
  · rw [ite_eq_left hc]
    constructor
    · intro ht
      exact hshift t ht.2 ht.1
    · intro ht
      have hp : (t:Circle) ∈ closedBall (c:Circle) r := by
        change t ∈ ((↑) : ℝ → Circle) ⁻¹' closedBall (c:Circle) r
        rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion]
        exact mem_iUnion.mpr ⟨0, by simpa only [zero_zsmul, add_zero, Real.closedBall_eq_Icc] using ht⟩
      exact ⟨hp, (ball_interval_membership c r a b t hr hrealA hrealB ht).mpr hc⟩
  · rw [ite_eq_right hc]
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hp ht
    exact hc ((ball_interval_membership c r a b t hr hrealA hrealB (hshift t ht hp)).mp ht)

theorem circular_interval_mass (c v a b : ℝ) (hv : 0 ≤ v)
    (hc0 : 0 < c) (hc1 : c < 1) (ha : 0 ≤ a) (hb : b ≤ 1)
    (havoidA : (a:Circle) ∉ closedBall (c:Circle) (v/2))
    (havoidB : (b:Circle) ∉ closedBall (c:Circle) (v/2)) :
    volume.real (arcPart (c:Circle) v (Ioc a b)) = if c ∈ Ioc a b then v else 0 := by
  rw [arcPart, circular_interval_support c (v/2) a b (by linarith) hc0 hc1 ha hb havoidA havoidB]
  split_ifs
  · rw [Real.volume_real_Icc, max_eq_left (by linarith)]
    ring
  · simp

theorem interval_preserved (chores : Bool) (w h c a b : ℝ) (hw : 0 < w)
    (hh : 0 ≤ h) (hhw : h ≤ w) (hc0 : 0 < c) (hc1 : c < 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (havoidA : (a:Circle) ∉ closedBall (c:Circle) (w/2))
    (havoidB : (b:Circle) ∉ closedBall (c:Circle) (w/2)) :
    (row chores w h (c:Circle)).cumulative b - (row chores w h (c:Circle)).cumulative a = b-a := by
  have hnarrow : closedBall (c:Circle) (h/2) ⊆ closedBall (c:Circle) (w/2) :=
    closedBall_subset_closedBall (by linarith)
  have hbumpA : (a:Circle) ∉ closedBall (c:Circle) (h/2) := fun ha => havoidA (hnarrow ha)
  have hbumpB : (b:Circle) ∉ closedBall (c:Circle) (h/2) := fun hb => havoidB (hnarrow hb)
  rw [Row.interval_value _ hab, row_bundle_value chores w h (c:Circle) (Ioc a b) measurableSet_Ioc
    (fun t ht => ⟨ha.trans ht.1.le, ht.2.trans hb⟩),
    circular_interval_mass c h a b hh hc0 hc1 ha hb hbumpA hbumpB,
    circular_interval_mass c w a b hw.le hc0 hc1 ha hb havoidA havoidB,
    Real.volume_real_Ioc, max_eq_left (sub_nonneg.mpr hab)]
  cases chores <;> split_ifs <;> field_simp <;> ring

end EnvyFreeResearch.Full.MoatReplayGeometry
