import EnvyFreeResearch.Full.NonnegativeAllocation
import EnvyFreeResearch.R3QueryLower

namespace EnvyFreeResearch.Full.NonnegativeAllocationDecoder

open Set MeasureTheory Metric IntervalAllocation NonnegativeAllocation
open NonnegativePulse NonnegativePulseGeometry
open scoped Classical

abbrev Circle := NonnegativeCircle.Circle
variable {Agent : Type*}

theorem pulse_share_support (A : Allocation Agent) (c r : ℝ) (hr : 0 ≤ r)
    (hc0 : 0 < c - r) (hc1 : c + r < 1)
    (hleft : ∀ k, r < |c - A.left k|) (hright : ∀ k, r < |c - A.right k|)
    (i : Agent) :
    (((↑) : ℝ → Circle) ⁻¹' closedBall (c : Circle) r) ∩ A.share i =
      if i = ownerAt A c then Icc (c - r) (c + r) else ∅ := by
  have hnowrap := nonwrapping_support c r hr hc0 hc1
  have hcunit : c ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  ext t
  by_cases hi : i = ownerAt A c
  · rw [ite_eq_left hi]
    constructor
    · intro ht
      exact hnowrap ▸ ⟨ht.1, share_subset A i ht.2⟩
    · intro ht
      have hsource : t ∈ (((↑) : ℝ → Circle) ⁻¹' closedBall (c : Circle) r) ∩ Icc (0 : ℝ) 1 :=
        hnowrap.symm ▸ ht
      have hcshare : c ∈ A.share i := by simpa only [hi] using ownerAt_mem A c hcunit
      exact ⟨hsource.1, (share_membership_constant A c r t hr hc0 hc1 hleft hright ht i).mpr hcshare⟩
  · rw [ite_eq_right hi]
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hp hshare
    have ht : t ∈ Icc (c - r) (c + r) := hnowrap ▸ ⟨hp, share_subset A i hshare⟩
    have hcshare := (share_membership_constant A c r t hr hc0 hc1 hleft hright ht i).mp hshare
    exact hi ((ownerAt_eq_iff A c hcunit i).mpr hcshare).symm

theorem pulse_share_mass (A : Allocation Agent) (c r : ℝ) (hr : 0 ≤ r)
    (hc0 : 0 < c - r) (hc1 : c + r < 1)
    (hleft : ∀ k, r < |c - A.left k|) (hright : ∀ k, r < |c - A.right k|)
    (i : Agent) :
    volume.real ((((↑) : ℝ → Circle) ⁻¹' closedBall (c : Circle) r) ∩ A.share i) =
      if i = ownerAt A c then 2 * r else 0 := by
  rw [pulse_share_support A c r hr hc0 hc1 hleft hright i]
  split_ifs
  · rw [Real.volume_real_Icc, max_eq_left (by linarith)]
    ring
  · simp

/-- The actual utility table of an arbitrary physical finite output is the
literal transfer table, once the two bumps avoid all its free endpoints. -/
theorem literal_share_values (A : Allocation Agent) (h c d : ℝ) (hh : 0 ≤ h)
    (hc0 : 0 < c - h / 2) (hc1 : c + h / 2 < 1)
    (hd0 : 0 < d - h / 2) (hd1 : d + h / 2 < 1)
    (hcl : ∀ k, h / 2 < |c - A.left k|) (hcr : ∀ k, h / 2 < |c - A.right k|)
    (hdl : ∀ k, h / 2 < |d - A.left k|) (hdr : ∀ k, h / 2 < |d - A.right k|)
    (i : Agent) :
    (row h (c : Circle) (d : Circle)).signedMeasure (A.share i) =
      R3QueryLower.transfer (fun k => volume.real (A.share k)) (ownerAt A c) (ownerAt A d) (h / 2) i := by
  rw [row_bundle_value _ _ _ _ (A.share_measurable i) (share_subset A i),
    pulse_share_mass A c (h / 2) (by linarith) hc0 hc1 hcl hcr i,
    pulse_share_mass A d (h / 2) (by linarith) hd0 hd1 hdl hdr i]
  unfold R3QueryLower.transfer
  split_ifs <;> ring

/-- Every successful equal-length uniform cake output is made strictly
incorrect unless the changed observer owns the positive pulse. -/
theorem cake_strict_envy (A : Allocation Agent) (h c d : ℝ) (hh : 0 < h)
    (hc0 : 0 < c - h / 2) (hc1 : c + h / 2 < 1)
    (hd0 : 0 < d - h / 2) (hd1 : d + h / 2 < 1)
    (hcl : ∀ k, h / 2 < |c - A.left k|) (hcr : ∀ k, h / 2 < |c - A.right k|)
    (hdl : ∀ k, h / 2 < |d - A.left k|) (hdr : ∀ k, h / 2 < |d - A.right k|)
    (i : Agent) (hexception : i ≠ ownerAt A c) (hdifferent : ownerAt A c ≠ ownerAt A d)
    (hequal : volume.real (A.share i) = volume.real (A.share (ownerAt A c))) :
    (row h (c : Circle) (d : Circle)).signedMeasure (A.share i) <
      (row h (c : Circle) (d : Circle)).signedMeasure (A.share (ownerAt A c)) := by
  rw [literal_share_values A h c d hh.le hc0 hc1 hd0 hd1 hcl hcr hdl hdr i,
    literal_share_values A h c d hh.le hc0 hc1 hd0 hd1 hcl hcr hdl hdr (ownerAt A c)]
  exact R3QueryLower.cake_strict_envy _ _ _ _ _ hexception hdifferent hequal (by positivity)

/-- The same physical pulse profile makes the chore output strictly
incorrect unless the changed observer owns the negative pulse. -/
theorem chore_strict_envy (A : Allocation Agent) (h c d : ℝ) (hh : 0 < h)
    (hc0 : 0 < c - h / 2) (hc1 : c + h / 2 < 1)
    (hd0 : 0 < d - h / 2) (hd1 : d + h / 2 < 1)
    (hcl : ∀ k, h / 2 < |c - A.left k|) (hcr : ∀ k, h / 2 < |c - A.right k|)
    (hdl : ∀ k, h / 2 < |d - A.left k|) (hdr : ∀ k, h / 2 < |d - A.right k|)
    (i : Agent) (hexception : i ≠ ownerAt A d) (hdifferent : ownerAt A c ≠ ownerAt A d)
    (hequal : volume.real (A.share i) = volume.real (A.share (ownerAt A d))) :
    (row h (c : Circle) (d : Circle)).signedMeasure (A.share (ownerAt A d)) <
      (row h (c : Circle) (d : Circle)).signedMeasure (A.share i) := by
  rw [literal_share_values A h c d hh.le hc0 hc1 hd0 hd1 hcl hcr hdl hdr i,
    literal_share_values A h c d hh.le hc0 hc1 hd0 hd1 hcl hcr hdl hdr (ownerAt A d)]
  exact R3QueryLower.chore_strict_envy _ _ _ _ _ hexception hdifferent.symm hequal (by positivity)

end EnvyFreeResearch.Full.NonnegativeAllocationDecoder

#print axioms EnvyFreeResearch.Full.NonnegativeAllocationDecoder.literal_share_values
#print axioms EnvyFreeResearch.Full.NonnegativeAllocationDecoder.cake_strict_envy
#print axioms EnvyFreeResearch.Full.NonnegativeAllocationDecoder.chore_strict_envy
