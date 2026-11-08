import EnvyFreeResearch.Full.UpperSnapshotProtocolZeroPhysical
import EnvyFreeResearch.Full.UpperSnapshotSmallVirtual

/-! The zero branch is accepted on the actual supported-interpolation event.
Agreement of the finite cell table alone is never treated as agreement of
physical values inside cells. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotSmall UpperDomainDifference UpperAggregateInterpolation
  UpperGridSensitivity UpperGridInterpolation
variable {n k g : ℕ} [Nonempty (Fin k)]

 theorem supported_zero_rows (μ : Fin k → Measure ℝ) (normalizer : Fin k → ℝ)
    (origin : List Component) (cuts : Fin (g+2) → ℝ) {Generated : Type*}
    (points : Generated → ℝ) (b : ℝ) (hgood : ¬BadSupportedRecordedUnion μ normalizer origin cuts points b)
    (i c : Fin k) (hzero : distance (physicalRows μ normalizer origin cuts) i c = 0)
    (virtual : List Component) (actual : Set ℝ) (hends : RecordedEndpoints cuts points virtual)
    (hactual : actual = domain origin ∩ domain virtual) :
    (μ i).real actual / normalizer i = (μ c).real actual / normalizer c := by
  have herr : |(μ i).real actual / normalizer i - (μ c).real actual / normalizer c -
      UpperEnvelope.estimate (physicalRows μ normalizer origin cuts)
        (UpperEnvelope.uniformCells (UpperLogicalCells.cell (domain origin) cuts)) i c actual| ≤
      b * distance (physicalRows μ normalizer origin cuts) i c := by
    apply le_of_not_gt
    intro h
    exact hgood ⟨i,c,virtual,actual,hends,hactual,h⟩
  have hrow (e : Fin (g+1)) : physicalRows μ normalizer origin cuts i e = physicalRows μ normalizer origin cuts c e := by
    have hh := coord_le_distance (physicalRows μ normalizer origin cuts) i c e
    rw [hzero] at hh
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  have he : UpperEnvelope.estimate (physicalRows μ normalizer origin cuts)
      (UpperEnvelope.uniformCells (UpperLogicalCells.cell (domain origin) cuts)) i c actual = 0 := by
    unfold UpperEnvelope.estimate
    simp only [hrow,sub_self,zero_mul,Finset.sum_const_zero]
  rw [he,sub_zero,hzero,mul_zero] at herr
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm herr (abs_nonneg _)))

 theorem zero_accepts_of_interpolation
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (origin : State n)
    (hgood : WellFormed μ origin) (cutter : Fin k)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cuts : Fin (g+2) → ℝ) (hzero : cuts 0=0) (hone : cuts (Fin.last (g+1))=1)
    (start : UpperSnapshotSmall.Circle) (b : ℝ)
    (hD : ∀ i, distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter = 0)
    (hevent : ¬BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts
      (partitionRun policy origin (active cutter) (equalTargets k) start).1 b) :
    (zeroExecute policy hk chores active origin cutter start).2.2 = false := by
  apply (zeroFinish_success hk chores active start _).mpr
  apply (completeCheck_iff chores active _).mpr
  rw [equalPieces_actual]
  have hw := partState_wellFormed μ hk policy hpolicy origin hgood (active cutter) (hpositive cutter)
    (equalTargets k) start
  have heq (i j : Fin k) :
      total (partState hk policy origin (active cutter) (equalTargets k) start j) (active i) /
          (μ (active i)).real (domain origin.cells) =
      ((μ (active cutter)).real (domain origin.cells) / k) /
          (μ (active cutter)).real (domain origin.cells) := by
    obtain ⟨virtual,hends,hactual⟩ := actual_part_supported hk policy origin (active cutter) cuts hzero hone (equalTargets k) start j
    have hr := supported_zero_rows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts _ b hevent i cutter (hD i)
      virtual _ hends hactual
    rw [← total_correct μ _ (hw j) (active i), ← total_correct μ _ (hw j) (active cutter)] at hr
    rw [equal_partition_value μ policy hpolicy origin hgood (active cutter) (hpositive cutter) hk start j] at hr
    exact hr
  intro i j
  have hvalues : total (partState hk policy origin (active cutter) (equalTargets k) start i) (active i) =
      total (partState hk policy origin (active cutter) (equalTargets k) start j) (active i) :=
    (div_left_inj' (ne_of_gt (hpositive i))).mp ((heq i i).trans (heq i j).symm)
  cases chores <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> exact le_of_eq (by first | exact hvalues | exact hvalues.symm)

end EnvyFreeResearch.Full.UpperSnapshotProtocol
