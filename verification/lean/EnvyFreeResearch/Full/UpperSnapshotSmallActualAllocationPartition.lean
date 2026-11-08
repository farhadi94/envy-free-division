import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationValues

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m J : ℕ}
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpositive : 0 < (μ cutter).real (domain origin.cells))
  (cuts : Fin (m+2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
  (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
  (selected : Finset (Fin (m+1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
  (hJ : 0 < J) (hfit : (J : ℝ)*t < 1) (first second : Circle)
include hpolicy hgood hpositive hzero hmono hsep ht ht1 hfit

theorem actual_allocation_cover :
    (⋃ j, domain ((actualAllocation hJ policy origin cutter cuts selected t first second).1 j).cells) ∪
      domain (actualAllocation hJ policy origin cutter cuts selected t first second).2.1.cells = domain origin.cells := by
  rw [← first_second_cover μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 hJ hfit first second]
  ext x
  constructor
  · rintro (hx | hx)
    · obtain ⟨j,hx⟩ := mem_iUnion.mp hx
      by_cases hj : j.val=0
      · have hz : j=⟨0,hJ⟩ := Fin.ext hj
        rw [hz,actual_share_zero,firstAllocationFrom_actual] at hx
        exact Or.inl hx
      · rw [actual_share_nonzero hJ policy origin cutter cuts selected t first second j hj] at hx
        exact Or.inr (mem_iUnion.mpr ⟨_,hx⟩)
    · rw [actual_buffer] at hx
      exact Or.inr (mem_iUnion.mpr ⟨_,hx⟩)
  · rintro (hx | hx)
    · apply Or.inl
      apply mem_iUnion.mpr
      refine ⟨⟨0,hJ⟩,?_⟩
      rw [actual_share_zero,firstAllocationFrom_actual]
      exact hx
    · obtain ⟨j,hx⟩ := mem_iUnion.mp hx
      by_cases hj : j.val+1 < J
      · apply Or.inl
        apply mem_iUnion.mpr
        refine ⟨⟨j.val+1,hj⟩,?_⟩
        rw [actual_share_nonzero hJ policy origin cutter cuts selected t first second _ (by simp)]
        have he : (⟨(j.val+1)-1,by omega⟩ : Fin J)=j := Fin.ext (by change (j.val+1)-1=j.val; omega)
        simpa only [he] using hx
      · apply Or.inr
        rw [actual_buffer]
        have he : j=⟨J-1,by omega⟩ := Fin.ext (by change j.val=J-1; have hh:=j.isLt; omega)
        simpa only [he] using hx

theorem actual_shares_disjoint :
    Pairwise (fun i j => Disjoint (domain ((actualAllocation hJ policy origin cutter cuts selected t first second).1 i).cells)
      (domain ((actualAllocation hJ policy origin cutter cuts selected t first second).1 j).cells)) := by
  intro i j hij
  by_cases hi : i.val=0
  · have he : i=⟨0,hJ⟩ := Fin.ext hi
    have hj : j.val≠0 := fun hj => hij (Fin.ext (hi.trans hj.symm))
    rw [he,actual_share_zero,firstAllocationFrom_actual,actual_share_nonzero hJ policy origin cutter cuts selected t first second j hj]
    exact first_second_disjoint μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 hJ hfit first second _
  · rw [actual_share_nonzero hJ policy origin cutter cuts selected t first second i hi]
    by_cases hj : j.val=0
    · have he : j=⟨0,hJ⟩ := Fin.ext hj
      rw [he,actual_share_zero,firstAllocationFrom_actual]
      exact (first_second_disjoint μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 hJ hfit first second _).symm
    · rw [actual_share_nonzero hJ policy origin cutter cuts selected t first second j hj]
      apply (second_all_parts μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 hJ hfit first second).2
      intro he
      apply hij
      apply Fin.ext
      have hv := congrArg Fin.val he
      dsimp only at hv
      omega

theorem actual_share_buffer_disjoint (j : Fin J) :
    Disjoint (domain ((actualAllocation hJ policy origin cutter cuts selected t first second).1 j).cells)
      (domain (actualAllocation hJ policy origin cutter cuts selected t first second).2.1.cells) := by
  rw [actual_buffer]
  by_cases hj : j.val=0
  · have he : j=⟨0,hJ⟩ := Fin.ext hj
    rw [he,actual_share_zero,firstAllocationFrom_actual]
    exact first_second_disjoint μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 hJ hfit first second _
  · rw [actual_share_nonzero hJ policy origin cutter cuts selected t first second j hj]
    apply (second_all_parts μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 hJ hfit first second).2
    intro he
    have hv := congrArg Fin.val he
    dsimp only at hv
    have hh := j.isLt
    omega

end EnvyFreeResearch.Full.UpperSnapshotSmall
