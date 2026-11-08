import EnvyFreeResearch.Full.IntervalAllocation
import EnvyFreeResearch.Full.NonnegativeEndpointLaw
import EnvyFreeResearch.Full.NonnegativePulseGeometry

/-! The nonnegative adversary applied to actual complete physical allocations
with arbitrary finite real output endpoints. -/

namespace EnvyFreeResearch.Full.NonnegativeAllocation

open Set MeasureTheory IntervalAllocation NonnegativeEndpointLaw NonnegativePulseGeometry
open scoped Classical
open scoped BigOperators ENNReal

variable {Agent : Type*}

theorem share_subset (A : Allocation Agent) (i : Agent) : A.share i ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  rw [← A.share_cover]
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

theorem exists_owner (A : Allocation Agent) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ i, x ∈ A.share i := by
  have h : x ∈ ⋃ i, A.share i := A.share_cover.symm ▸ hx
  exact Set.mem_iUnion.mp h

noncomputable def ownerAt (A : Allocation Agent) (x : ℝ) : Agent := by
  classical
  exact if hx : x ∈ Icc (0 : ℝ) 1 then Classical.choose (exists_owner A x hx)
    else A.endpointOwner

theorem ownerAt_mem (A : Allocation Agent) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    x ∈ A.share (ownerAt A x) := by
  classical
  simp only [ownerAt, dite_eq_left hx]
  exact Classical.choose_spec (exists_owner A x hx)

theorem ownerAt_eq_iff (A : Allocation Agent) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (i : Agent) :
    ownerAt A x = i ↔ x ∈ A.share i := by
  constructor
  · intro hi
    simpa only [hi] using ownerAt_mem A x hx
  · intro hi
    by_contra hne
    exact Set.disjoint_left.mp (A.share_disjoint hne) (ownerAt_mem A x hx) hi

theorem ownerAt_preimage (A : Allocation Agent) (i : Agent) :
    ownerAt A ⁻¹' {i} = A.share i ∪
      if A.endpointOwner = i then (Icc (0 : ℝ) 1)ᶜ else ∅ := by
  classical
  ext x
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · simp only [mem_preimage, mem_singleton_iff, mem_union,
      ownerAt_eq_iff A x hx i]
    split_ifs <;> simp [hx]
  · have hnot : x ∉ A.share i := fun h => hx (share_subset A i h)
    simp [ownerAt, hx, hnot]

theorem ownerAt_measurable [MeasurableSpace Agent] [Countable Agent] (A : Allocation Agent) :
    Measurable (ownerAt A) := by
  classical
  apply measurable_to_countable'
  intro i
  rw [ownerAt_preimage]
  apply (A.share_measurable i).union
  split_ifs
  · exact measurableSet_Icc.compl
  · exact MeasurableSet.empty

noncomputable def circleOwner (A : Allocation Agent) (x : NonnegativeCircle.Circle) : Agent :=
  ownerAt A (representative x)

theorem circleOwner_measurable [MeasurableSpace Agent] [Countable Agent] (A : Allocation Agent) :
    Measurable (circleOwner A) :=
  (ownerAt_measurable A).comp measurable_representative

theorem representative_of_mem (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    representative (x : NonnegativeCircle.Circle) = x := by
  exact AddCircle.equivIoc_coe_of_mem (by simpa using hx)

/-- Circular owner fibers have precisely the physical bundle length, so the
same-owner probability estimate applies to every actual finite allocation. -/
theorem circleOwner_fiber_mass [MeasurableSpace Agent] [Countable Agent]
    [MeasurableSingletonClass Agent] (A : Allocation Agent) (i : Agent) :
    volume (circleOwner A ⁻¹' {i}) = volume (A.share i) := by
  have hfiber := (measurableSet_singleton i).preimage (circleOwner_measurable A)
  rw [AddCircle.add_projection_respects_measure (1 : ℝ) 0 hfiber]
  have heq : (((↑) : ℝ → NonnegativeCircle.Circle) ⁻¹' (circleOwner A ⁻¹' {i})) ∩
      Ioc (0 : ℝ) (0 + 1) = A.share i ∩ Ioc (0 : ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, zero_add]
    constructor
    · rintro ⟨hx, hunit⟩
      have hrep := representative_of_mem x hunit
      have ho : ownerAt A x = i := by simpa only [circleOwner, hrep] using hx
      exact ⟨(ownerAt_eq_iff A x ⟨hunit.1.le, hunit.2⟩ i).mp ho, hunit⟩
    · rintro ⟨hx, hunit⟩
      have ho := (ownerAt_eq_iff A x ⟨hunit.1.le, hunit.2⟩ i).mpr hx
      exact ⟨by simpa only [circleOwner, representative_of_mem x hunit] using ho, hunit⟩
  rw [heq]
  have hae : A.share i ∩ Ioc (0 : ℝ) 1 =ᵐ[volume] A.share i ∩ Icc (0 : ℝ) 1 := by
    filter_upwards [Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1) (μ := volume)] with x hx
    exact congrArg (fun p : Prop => x ∈ A.share i ∧ p) hx
  rw [measure_congr hae, Set.inter_eq_left.mpr (share_subset A i)]

theorem share_lengths_sum [Fintype Agent] (A : Allocation Agent) :
    (∑ i, volume.real (A.share i)) = 1 := by
  have hsum := measureReal_iUnion_fintype (μ := volume)
    (fun i j hij => A.share_disjoint hij) (A.share_measurable)
    (fun i => measure_ne_top_of_subset (share_subset A i) (by simp))
  rw [A.share_cover, Real.volume_real_Icc] at hsum
  norm_num at hsum
  exact hsum.symm

/-- Exact envy-freeness on the uniform profile forces equal bundle length
for every complete finite output. Chore comparisons give the same premise
by interchanging the observer and comparison indices. -/
theorem equal_lengths_of_uniformEF [Fintype Agent] (A : Allocation Agent)
    (hEF : ∀ i j, volume.real (A.share j) ≤ volume.real (A.share i)) (i : Agent) :
    volume.real (A.share i) = 1 / (Fintype.card Agent : ℝ) := by
  have heq (j : Agent) : volume.real (A.share j) = volume.real (A.share i) :=
    le_antisymm (hEF i j) (hEF j i)
  have hsum := share_lengths_sum A
  simp_rw [heq] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcard : 0 < Fintype.card Agent := Fintype.card_pos_iff.mpr ⟨A.endpointOwner⟩
  have hcardR : (Fintype.card Agent : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hcard
  apply (eq_div_iff hcardR).mpr
  simpa only [mul_comm] using hsum

theorem circle_fibers_of_uniformEF {n : ℕ} (hn : 0 < n) (A : Allocation (Fin n))
    (hEF : ∀ i j, volume.real (A.share j) ≤ volume.real (A.share i)) (i : Fin n) :
    volume (circleOwner A ⁻¹' {i}) = (n : ℝ≥0∞)⁻¹ := by
  rw [circleOwner_fiber_mass]
  have hfinite : volume (A.share i) ≠ ∞ :=
    measure_ne_top_of_subset (share_subset A i) (by simp)
  have hlength : volume.real (A.share i) = 1 / (n : ℝ) := by
    simpa only [Fintype.card_fin] using equal_lengths_of_uniformEF A hEF i
  calc
    volume (A.share i) = ENNReal.ofReal (volume.real (A.share i)) :=
      (ENNReal.ofReal_toReal hfinite).symm
    _ = ENNReal.ofReal (1 / (n : ℝ)) := by rw [hlength]
    _ = (n : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn)]
      simp

/-- Every interval membership, and therefore every owner's entire bundle,
is locally constant inside a bump that avoids the finite output endpoints. -/
theorem share_membership_constant (A : Allocation Agent) (c r t : ℝ) (hr : 0 ≤ r)
    (hc0 : 0 < c - r) (hc1 : c + r < 1)
    (hleft : ∀ k, r < |c - A.left k|) (hright : ∀ k, r < |c - A.right k|)
    (ht : t ∈ Icc (c - r) (c + r)) (i : Agent) :
    t ∈ A.share i ↔ c ∈ A.share i := by
  have hcpos : 0 < c := by linarith
  have htpos : 0 < t := by linarith [ht.1]
  rw [A.mem_share, A.mem_share]
  simp only [ne_of_gt hcpos, ne_of_gt htpos, and_false, or_false]
  rw [A.mem_positiveShare, A.mem_positiveShare]
  apply exists_congr
  intro k
  exact and_congr_right (fun _ =>
    ball_interval_membership c r (A.left k) (A.right k) t hr (hleft k) (hright k) ht)

theorem ownerAt_constant_on_bump (A : Allocation Agent) (c r t : ℝ) (hr : 0 ≤ r)
    (hc0 : 0 < c - r) (hc1 : c + r < 1)
    (hleft : ∀ k, r < |c - A.left k|) (hright : ∀ k, r < |c - A.right k|)
    (ht : t ∈ Icc (c - r) (c + r)) : ownerAt A t = ownerAt A c := by
  have hcunit : c ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have htunit : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  apply (ownerAt_eq_iff A t htunit (ownerAt A c)).mpr
  exact (share_membership_constant A c r t hr hc0 hc1 hleft hright ht _).mpr
    (ownerAt_mem A c hcunit)

end EnvyFreeResearch.Full.NonnegativeAllocation

#print axioms EnvyFreeResearch.Full.NonnegativeAllocation.ownerAt_measurable
#print axioms EnvyFreeResearch.Full.NonnegativeAllocation.circleOwner_fiber_mass
#print axioms EnvyFreeResearch.Full.NonnegativeAllocation.ownerAt_constant_on_bump
