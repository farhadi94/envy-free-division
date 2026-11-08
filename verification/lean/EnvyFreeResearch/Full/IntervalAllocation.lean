import EnvyFreeResearch.Full.MixedReplay

/-! Complete physical allocations into arbitrary finite unions of intervals.
All output endpoints are free real numbers. The common endpoint 0 is assigned
explicitly, so the allocation is literally complete and pairwise disjoint. -/

namespace EnvyFreeResearch.Full.IntervalAllocation
open Set MeasureTheory TranscriptAdversary
open scoped Classical

structure Allocation (Agent : Type*) where
  count : ℕ
  left : Fin count → ℝ
  right : Fin count → ℝ
  owner : Fin count → Agent
  endpointOwner : Agent
  bounded : ∀ k, 0 ≤ left k ∧ left k ≤ right k ∧ right k ≤ 1
  disjoint : Pairwise (fun k m => Disjoint (Ioc (left k) (right k)) (Ioc (left m) (right m)))
  covers : (⋃ k, Ioc (left k) (right k)) = Ioc (0 : ℝ) 1

namespace Allocation
variable {Agent : Type*}

noncomputable def positiveShare (A : Allocation Agent) (i : Agent) : Set ℝ :=
  ⋃ k, if A.owner k = i then Ioc (A.left k) (A.right k) else ∅

noncomputable def share (A : Allocation Agent) (i : Agent) : Set ℝ :=
  A.positiveShare i ∪ (if i = A.endpointOwner then {0} else ∅)

theorem mem_positiveShare (A : Allocation Agent) (i : Agent) (x : ℝ) :
    x ∈ A.positiveShare i ↔ ∃ k, A.owner k = i ∧ x ∈ Ioc (A.left k) (A.right k) := by
  simp only [positiveShare, mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hi : A.owner k = i
    · exact ⟨k, hi, by simpa [hi] using hk⟩
    · simp [hi] at hk
  · rintro ⟨k, hi, hx⟩
    exact ⟨k, by simpa [hi] using hx⟩

theorem positiveShare_subset (A : Allocation Agent) (i : Agent) :
    A.positiveShare i ⊆ Ioc (0 : ℝ) 1 := by
  intro x hx
  obtain ⟨k, hi, hk⟩ := (A.mem_positiveShare i x).mp hx
  exact ⟨(A.bounded k).1.trans_lt hk.1, hk.2.trans (A.bounded k).2.2⟩

theorem positiveShare_measurable (A : Allocation Agent) (i : Agent) :
    MeasurableSet (A.positiveShare i) := by
  apply MeasurableSet.iUnion
  intro k
  split_ifs
  · exact measurableSet_Ioc
  · exact MeasurableSet.empty

theorem share_measurable (A : Allocation Agent) (i : Agent) : MeasurableSet (A.share i) := by
  apply (A.positiveShare_measurable i).union
  split_ifs
  · exact measurableSet_singleton 0
  · exact MeasurableSet.empty

theorem positiveShare_disjoint (A : Allocation Agent) {i j : Agent} (hij : i ≠ j) :
    Disjoint (A.positiveShare i) (A.positiveShare j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨k, hki, hk⟩ := (A.mem_positiveShare i x).mp hx
  obtain ⟨m, hmj, hm⟩ := (A.mem_positiveShare j x).mp hy
  by_cases hkm : k = m
  · subst m
    exact hij (hki.symm.trans hmj)
  · exact Set.disjoint_left.mp (A.disjoint hkm) hk hm

theorem mem_share (A : Allocation Agent) (i : Agent) (x : ℝ) :
    x ∈ A.share i ↔ x ∈ A.positiveShare i ∨ (i = A.endpointOwner ∧ x = 0) := by
  simp only [share, mem_union]
  by_cases hi : i = A.endpointOwner <;> simp [hi]

theorem share_disjoint (A : Allocation Agent) {i j : Agent} (hij : i ≠ j) :
    Disjoint (A.share i) (A.share j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rw [mem_share] at hx hy
  rcases hx with hx | ⟨hi, rfl⟩
  · rcases hy with hy | ⟨hj, rfl⟩
    · exact Set.disjoint_left.mp (A.positiveShare_disjoint hij) hx hy
    · exact (lt_irrefl (0 : ℝ)) (A.positiveShare_subset i hx).1
  · rcases hy with hy | ⟨hj, hzero⟩
    · exact (lt_irrefl (0 : ℝ)) (A.positiveShare_subset j hy).1
    · exact hij (hi.trans hj.symm)

theorem share_cover (A : Allocation Agent) : (⋃ i, A.share i) = Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rcases (A.mem_share i x).mp hi with hpos | ⟨_, rfl⟩
    · exact ⟨(A.positiveShare_subset i hpos).1.le, (A.positiveShare_subset i hpos).2⟩
    · norm_num
  · intro hx
    by_cases hx0 : x = 0
    · exact mem_iUnion.mpr ⟨A.endpointOwner, (A.mem_share _ _).mpr (Or.inr ⟨rfl, hx0⟩)⟩
    · have hpos : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩
      rw [← A.covers] at hpos
      obtain ⟨k, hk⟩ := mem_iUnion.mp hpos
      refine mem_iUnion.mpr ⟨A.owner k, (A.mem_share _ _).mpr (Or.inl ?_)⟩
      exact (A.mem_positiveShare _ _).mpr ⟨k, rfl, hk⟩

/-- Once every free output endpoint below 1 is behind the frontier, one
agent owns the entire remaining tail. -/
theorem exists_tail_owner (A : Allocation Agent) (l : ℝ) (hl : 0 ≤ l) (hl1 : l < 1)
    (hleft : ∀ k, FrozenCoordinate l (A.left k))
    (hright : ∀ k, FrozenCoordinate l (A.right k)) :
    ∃ i, Ioc l (1 : ℝ) ⊆ A.share i := by
  let x : ℝ := (l + 1) / 2
  have hxl : l < x := by dsimp [x]; linarith
  have hx1 : x < 1 := by dsimp [x]; linarith
  have hx : x ∈ Ioc (0 : ℝ) 1 := ⟨hl.trans_lt hxl, hx1.le⟩
  rw [← A.covers] at hx
  obtain ⟨k, hk⟩ := mem_iUnion.mp hx
  have hkl : A.left k ≤ l := by
    rcases hleft k with h | h
    · exact h
    · rw [h] at hk
      linarith [hk.1]
  have hkr : A.right k = 1 := by
    rcases hright k with h | h
    · linarith [hk.2]
    · exact h
  refine ⟨A.owner k, ?_⟩
  intro y hy
  apply (A.mem_share _ _).mpr
  apply Or.inl
  apply (A.mem_positiveShare _ _).mpr
  exact ⟨k, rfl, hkl.trans_lt hy.1, by simpa [hkr] using hy.2⟩

end Allocation
end EnvyFreeResearch.Full.IntervalAllocation
