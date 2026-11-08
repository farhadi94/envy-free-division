import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationPhysical

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m J : ℕ}

theorem actual_share_zero (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle) :
    (actualAllocation hJ policy origin cutter cuts selected t first second).1 ⟨0,hJ⟩ =
      firstAllocationFrom origin cutter cuts selected t first (firstRun policy origin cutter cuts selected t first)
        (secondRun (J:=J) policy origin cutter cuts selected t first second) := rfl

theorem actual_share_nonzero (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle)
    (j : Fin J) (hj : j.val ≠ 0) :
    (actualAllocation hJ policy origin cutter cuts selected t first second).1 j =
      secondPiece hJ policy origin cutter cuts selected t first second ⟨j.val-1, by omega⟩ := by
  simp only [actualAllocation, allocationFrom, hj, dite_false, secondAllocationFrom_actual]

theorem actual_buffer (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle) :
    (actualAllocation hJ policy origin cutter cuts selected t first second).2.1 =
      secondPiece hJ policy origin cutter cuts selected t first second ⟨J-1,by omega⟩ := rfl

theorem actual_whole (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle) :
    (actualAllocation hJ policy origin cutter cuts selected t first second).2.2 =
      secondRestored (J:=J) policy origin cutter cuts selected t first second := rfl

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpositive : 0 < (μ cutter).real (domain origin.cells))
  (cuts : Fin (m+2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
  (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
  (selected : Finset (Fin (m+1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
include hpolicy hgood hpositive hzero hmono hsep ht ht1

theorem actual_allocation_wellFormed (hJ : 0 < J) (first second : Circle) :
    (∀ j, WellFormed μ ((actualAllocation hJ policy origin cutter cuts selected t first second).1 j)) ∧
    WellFormed μ (actualAllocation hJ policy origin cutter cuts selected t first second).2.1 ∧
    WellFormed μ (actualAllocation hJ policy origin cutter cuts selected t first second).2.2 := by
  refine ⟨?_,?_,?_⟩
  · intro j
    by_cases hj : j.val = 0
    · have hz : j = ⟨0,hJ⟩ := Fin.ext hj
      rw [hz, actual_share_zero]
      exact firstAllocation_wellFormed μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep
        selected t ht ht1 first second
    · rw [actual_share_nonzero hJ policy origin cutter cuts selected t first second j hj]
      exact second_piece_wellFormed μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep
        selected t ht ht1 hJ first second _
  · rw [actual_buffer]
    exact second_piece_wellFormed μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep
      selected t ht ht1 hJ first second _
  · rw [actual_whole]
    exact secondRestored_wellFormed μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep
      selected t ht ht1 first second

theorem actual_allocation_cutter_mass (hJ : 0 < J) (hfit : (J : ℝ)*t < 1)
    (first second : Circle) (j : Fin J) :
    total ((actualAllocation hJ policy origin cutter cuts selected t first second).1 j) cutter =
      t*(μ cutter).real (domain origin.cells) := by
  by_cases hj : j.val = 0
  · have hw := (actual_allocation_wellFormed μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep
      selected t ht ht1 hJ first second).1 j
    rw [total_correct μ _ hw]
    have hz : j = ⟨0,hJ⟩ := Fin.ext hj
    rw [hz,actual_share_zero,firstAllocationFrom_actual]
    exact firstEndowment_mass μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 first
  · rw [actual_share_nonzero hJ policy origin cutter cuts selected t first second j hj]
    apply second_piece_mass μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 hJ hfit
    change j.val-1+1 < J
    omega

theorem actual_buffer_cutter_mass (hJ : 0 < J) (hfit : (J : ℝ)*t < 1) (first second : Circle) :
    total (actualAllocation hJ policy origin cutter cuts selected t first second).2.1 cutter =
      (1-J*t)*(μ cutter).real (domain origin.cells) := by
  rw [actual_buffer]
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  have hw := (first_partition μ policy hpolicy origin hgood cutter cuts selected t hs first).2.1
  have hp := firstRemainder_positive μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 first
  change total (partState hJ policy _ cutter _ second _) cutter = _
  rw [remainder_buffer_value μ policy hpolicy _ hw cutter hp hJ t ht hfit second _ (by change J-1+1=J; omega),
    firstRemainder_mass μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1]
  field_simp

end EnvyFreeResearch.Full.UpperSnapshotSmall
