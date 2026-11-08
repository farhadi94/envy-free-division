import EnvyFreeResearch.Full.IntervalAllocation
import EnvyFreeResearch.Full.MixedObstruction

/-! Exact valuation of complete physical finite-interval outputs and
preservation under a prefix extension. -/

namespace EnvyFreeResearch.Full.IntervalValues
open Set MeasureTheory TranscriptAdversary MixedDensity MixedObstruction IntervalAllocation
open scoped BigOperators Classical

variable {Agent : Type*}

theorem share_inter_domain (A : Allocation Agent) (i : Agent) :
    A.share i ∩ Ioc (0 : ℝ) 1 = A.positiveShare i := by
  ext x
  constructor
  · rintro ⟨hx, hunit⟩
    rcases (A.mem_share i x).mp hx with hp | ⟨_, rfl⟩
    · exact hp
    · exact False.elim ((lt_irrefl (0 : ℝ)) hunit.1)
  · intro hx
    exact ⟨(A.mem_share i x).mpr (Or.inl hx), A.positiveShare_subset i hx⟩

/-- Physical values equal the sum of cumulative differences on the records.
The extra point 0 carries zero value and is still assigned in the allocation. -/
theorem value_share (R : Row) (A : Allocation Agent) (i : Agent) :
    value R (A.share i) = ∑ k, if A.owner k = i then
      R.cumulative (A.right k) - R.cumulative (A.left k) else 0 := by
  rw [value_signedMeasure R (A.share i) (A.share_measurable i), share_inter_domain]
  rw [R.signedMeasure_apply _ (A.positiveShare_measurable i)]
  let pieces : Fin A.count → Set ℝ := fun k =>
    if A.owner k = i then Ioc (A.left k) (A.right k) else ∅
  have hm : ∀ k, MeasurableSet (pieces k) := by
    intro k
    dsimp only [pieces]
    split_ifs
    · exact measurableSet_Ioc
    · exact MeasurableSet.empty
  have hd : Pairwise (fun k m => Disjoint (pieces k) (pieces m)) := by
    intro k m hkm
    dsimp only [pieces]
    split_ifs <;> first
      | exact A.disjoint hkm
      | exact disjoint_bot_left
      | exact disjoint_bot_right
  change (∫ x in ⋃ k, pieces k, R.density x) = _
  rw [integral_iUnion_fintype hm hd (fun _ => R.integrable.integrableOn)]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : A.owner k = i
  · simp only [pieces, ite_eq_left hki]
    rw [← R.signedMeasure_apply _ measurableSet_Ioc, R.interval_value (A.bounded k).2.1]
  · simp [pieces, hki]

/-- Arbitrarily fragmented physical output values are preserved once all
proper endpoints are behind the frozen frontier. -/
theorem value_share_preserved (R S : Row) (A : Allocation Agent) (i : Agent) (l : ℝ)
    (hprefix : ∀ x ∈ Icc (0 : ℝ) l, S.cumulative x = R.cumulative x)
    (htotal : S.cumulative 1 = R.cumulative 1)
    (hleft : ∀ k, FrozenCoordinate l (A.left k))
    (hright : ∀ k, FrozenCoordinate l (A.right k)) :
    value S (A.share i) = value R (A.share i) := by
  rw [value_share S A i, value_share R A i]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : A.owner k = i
  · simp only [ite_eq_left hki]
    exact frozen_interval_value hprefix htotal (A.bounded k).1
      ((A.bounded k).1.trans (A.bounded k).2.1) (hleft k) (hright k)
  · simp [hki]

end EnvyFreeResearch.Full.IntervalValues
