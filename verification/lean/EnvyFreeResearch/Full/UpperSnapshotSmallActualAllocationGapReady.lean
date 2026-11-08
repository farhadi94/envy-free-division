import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocationGap

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperGridInterpolation UpperGridSensitivity
variable {n m J : ℕ} {Generated : Type*} [Nonempty (Fin J)]

/-- The actually sampled estimated witness gives the physical foreign-row
contrast, since the actual cutter shares have exactly equal mass. -/
theorem actualAllocation_gap_ready
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (active : Fin J → Fin n) (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter : Fin J) (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0)
    (hone : cuts (Fin.last (m+1))=1) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m+1))) (t : ℝ) (ht : 0<t) (ht1 : t<1)
    (hfit : (J:ℝ)*t<1) (first second : Circle)
    (points : Generated → ℝ)
    (hfirst : ∀ j, ∃ e, points e=(firstRun policy origin (active cutter) cuts selected t first).1 j)
    (hsecond : ∀ j, ∃ e, points e=(secondRun (J:=J) policy origin (active cutter) cuts selected t first second).1 j)
    (eps : ℝ) (heps : eps ≤ 3/(64*(J:ℝ)))
    (hinterp : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts points eps)
    (hJ : 2≤J) (i : Fin J)
    (hwitness : distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter/(8*(J:ℝ)) ≤
      candidateContrast hJ policy origin (active cutter) cuts selected t
        (signedEstimate (fun e => physicalRows (fun i => μ (active i))
          (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts i e-
          physicalRows (fun i => μ (active i))
          (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts cutter e)
          (cell (domain origin.cells) cuts)) (first,second)) :
    distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter/(32*(J:ℝ)) ≤
      (μ (active i)).real (domain ((actualAllocation (J:=J) (by omega) policy origin (active cutter) cuts selected t first second).1 ⟨0,by omega⟩).cells)/(μ (active i)).real (domain origin.cells)-
      (μ (active i)).real (domain ((actualAllocation (J:=J) (by omega) policy origin (active cutter) cuts selected t first second).1 ⟨1,by omega⟩).cells)/(μ (active i)).real (domain origin.cells) := by
  have hw := actual_allocation_wellFormed μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
    cuts hzero hmono hsep selected t ht ht1 (by omega : 0<J) first second
  have hequal : (μ (active cutter)).real (domain ((actualAllocation (J:=J) (by omega) policy origin (active cutter) cuts selected t first second).1 ⟨0,by omega⟩).cells)=
      (μ (active cutter)).real (domain ((actualAllocation (J:=J) (by omega) policy origin (active cutter) cuts selected t first second).1 ⟨1,by omega⟩).cells) := by
    rw [← total_correct μ _ (hw.1 ⟨0,by omega⟩),← total_correct μ _ (hw.1 ⟨1,by omega⟩),
      actual_allocation_cutter_mass μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
        cuts hzero hmono hsep selected t ht ht1 (by omega) hfit first second,
      actual_allocation_cutter_mass μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
        cuts hzero hmono hsep selected t ht ht1 (by omega) hfit first second]
  have hh := actualAllocation_physical_gap (fun i => μ (active i)) policy origin hgood.2.1 (active cutter)
    cuts hzero hone hmono hsep selected t first second points hfirst hsecond eps hinterp hJ i cutter _ hequal hwitness
  have hD : 0 ≤ distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  exact (witness_margin_arithmetic (by omega : 0<J) _ eps hD heps).trans hh

end EnvyFreeResearch.Full.UpperSnapshotSmall
