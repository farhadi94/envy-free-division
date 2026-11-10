import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolLegalityAllSmall
import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolLargeFacts
import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolCost

/-! Every branch of actual Snapshot preserves a truthful complete history,
without conditioning on a passing probability or good interpolation event. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotCandidates UpperRepairPreparationChecks UpperRepairParameters
  UpperEndpointCache UpperSnapshotSmall UpperDomainDifference UpperSortedGrid UpperCommonGrid
open UpperSnapshotProtocol (zeroExecute zeroFinish_history)
variable {n k : ℕ} [Nonempty (Fin k)]

theorem zero_history_truthful
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n)
    (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin k)
    (hpositive : 0 < (μ (active cutter)).real (domain origin.cells)) (start : UpperSnapshotSmall.Circle) :
    Truthful μ (zeroExecute policy hk chores active origin cutter start).2.1.history := by
  have hw := execute_wellFormed μ policy hpolicy origin hgood (active cutter) hpositive
    (shifts (equalTargets k)) start
  unfold zeroExecute
  rw [zeroFinish_history]
  exact hw.2.2.1

theorem large_history_truthful
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (draw : Fin (RefinedUpperRepair.fine n) → Fin k × I) (cutter : Fin k)
    (hD : 0 < selectedDistance (by omega) (UpperGridData.table active origin
      (UpperGridMerge.prepare policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) draw)) cutter)
    (fresh : RefinedUpperRepair.Tape n k) :
    Truthful μ (restoreRejected origin (execute policy (by omega) chores active (margin n)
      (candidateBuffer (by omega) active origin (UpperGridMerge.prepare policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) draw) cutter)
      (candidateOld (by omega) active origin (UpperGridMerge.prepare policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) draw) cutter) fresh)).2.1.history := by
  let data := UpperGridMerge.prepare policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) draw
  let old := candidateOld (by omega) active origin data cutter
  let buffer := candidateBuffer (by omega) active origin data cutter
  have hscale := RefinedUpperSnapshotParameters.coarse_cap_small
    (show 2 ≤ scale n by exact_mod_cast (show (2:ℝ) ≤ scale n from (by norm_num : (2:ℝ) ≤ 2^42).trans (scale_large n)))
    (logarithm_positive (scale_large n))
  have htau : 0 ≤ RefinedUpperRepair.nearError n :=
    by unfold RefinedUpperRepair.nearError RefinedUpperParameterCounts.oldError; positivity
  obtain ⟨hold,hbuffer,hpair,hdisj,hcover,hmasses⟩ := recorded_large_ready μ policy hpolicy active origin
    hgood hpositive (by omega) (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) draw cutter
    (RefinedUpperRepair.nearError n) htau hscale.2 hscale.1 hD
  have hnear : Near chores μ active buffer old (RefinedUpperRepair.nearError n) := by
    intro i j
    cases chores
    · exact (le_abs_self _).trans ((hmasses i).2.2 j i)
    · exact (le_abs_self _).trans ((hmasses i).2.2 i j)
  rw [restoreRejected_history]
  exact repaired_history_truthful μ policy hpolicy (by omega) chores active hinj (margin n) buffer hbuffer
    (fun i => (hmasses i).2.1) old hold hnear fresh

theorem snapshot_history_truthful
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter : Fin k) (tape : Tape n k) :
    Truthful μ (snapshotExecute policy hk chores active origin cutter tape).2.1.history := by
  let data := UpperGridMerge.prepare policy active origin (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) tape.1
  let values := UpperGridData.table active origin data
  let D := selectedDistance (by omega) values cutter
  have hw : WellFormed μ (UpperGridData.aligned data) :=
    UpperGridCache.aligned_wellFormed μ policy hpolicy active origin hgood hpositive _ _ _
  have hd : domain (UpperGridData.aligned data).cells = domain origin.cells :=
    UpperGridCache.aligned_domain policy active origin _ _ _
  have hp : ∀ i, 0 < (μ (active i)).real (domain (UpperGridData.aligned data).cells) := by
    simpa only [hd] using hpositive
  have hnonneg : 0 ≤ D := rowDistance_nonnegative values cutter _
  change Truthful μ
    (fromDataExecute policy hk chores active origin cutter data tape.2.1 tape.2.2.1 tape.2.2.2).2.1.history
  unfold fromDataExecute
  by_cases hz : D=0
  · dsimp only [D,values] at hz
    simp only [hz,ite_true]
    exact zero_history_truthful μ policy hpolicy (by omega) chores active _ hw cutter (hp cutter) tape.2.1
  · have hD : 0<D := lt_of_le_of_ne hnonneg (Ne.symm hz)
    dsimp only [D,values] at hz
    simp only [hz,ite_false]
    by_cases hsmall : D<RefinedUpperRepair.nearError n/16
    · dsimp only [D,values] at hsmall
      simp only [hsmall,ite_true]
      have hend := UpperGridMerge.cuts_endpoints μ policy hpolicy active origin hgood hpositive
        (RefinedUpperRepair.coarse n) (RefinedUpperRepair.fine n) tape.1
      have hmono : Monotone (UpperGridData.cuts data) := grid_monotone _
      have hsep : ∀ e, SeparatedAt (UpperGridData.cuts data e) (UpperGridData.aligned data).cells :=
        UpperGridCache.aligned_separated policy active origin _ _ _
      exact small_history_truthful μ policy hpolicy (by omega) chores active hinj _ hw cutter (hp cutter)
        (UpperGridData.cuts data) hend.1 hmono hsep
        (fun e => values (selectedRow (by omega) values cutter) e-values cutter e)
        D hD hsmall tape.2.2.1 tape.2.2.2
    · dsimp only [D,values] at hsmall
      simp only [hsmall,ite_false]
      exact large_history_truthful μ policy hpolicy hk chores active hinj origin hgood hpositive
        tape.1 cutter hD tape.2.2.2

theorem snapshot_history_extension (policy : Policy n) (hk : 3 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (cutter : Fin k) (tape : Tape n k) :
    origin.history ⊆ (snapshotExecute policy hk chores active origin cutter tape).2.1.history := by
  obtain ⟨trace,_,hh,_,_⟩ := snapshot_program_cost policy hk chores active hinj origin cutter tape
  rw [hh]
  exact List.subset_append_left _ _

end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
