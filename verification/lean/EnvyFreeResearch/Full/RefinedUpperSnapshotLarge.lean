import EnvyFreeResearch.Full.RefinedUpperSnapshotAcceptance
import EnvyFreeResearch.Full.RefinedUpperSnapshotReserve
import EnvyFreeResearch.Full.UpperSnapshotCandidatesParameters

/-! The recorded large-disagreement branch has an actual passing probability
strictly above 31/64, with no assumed candidate contrast or fairness premise. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotRepair UpperSnapshotContrast UpperRepairPreparationChecks
  UpperSnapshotCandidates RefinedUpperRepairSnapshot UpperRepairParameters
variable {n k : ℕ} [Nonempty (Fin k)]

theorem large_acceptance_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (hk : 3 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (q m : ℕ) (draw : Fin m → Fin k × I) (cutter : Fin k)
    (hquarter : 1/(q+1:ℝ) ≤ 1/4) (hscale : 1/(q+1:ℝ) ≤ RefinedUpperRepair.nearError n/2)
    (hD : 0 < selectedDistance (by omega)
      (UpperGridData.table active origin (UpperGridMerge.prepare policy active origin q m draw)) cutter) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    let old := candidateOld (by omega) active origin data cutter
    let buffer := candidateBuffer (by omega) active origin data cutter
    let Lambda := selectedDistance (by omega) (UpperGridData.table active origin data) cutter /
      (3 * (UpperRecordedQuantiles.count (Agent:=Fin k) q + m + 1 : ℕ))
    31/64 < (RefinedUpperRepair.law n k).real
      {p | (UpperSnapshotProtocol.finish (by omega) chores active (Lambda/8) buffer old
        (RefinedUpperRepair.execute policy (by omega) chores active buffer old p)).2.2 = false} := by
  let data := UpperGridMerge.prepare policy active origin q m draw
  let old := candidateOld (by omega) active origin data cutter
  let buffer := candidateBuffer (by omega) active origin data cutter
  let Lambda := selectedDistance (by omega) (UpperGridData.table active origin data) cutter /
    (3 * (UpperRecordedQuantiles.count (Agent:=Fin k) q + m + 1 : ℕ))
  have htau : 0 ≤ RefinedUpperRepair.nearError n := by
    unfold RefinedUpperRepair.nearError RefinedUpperParameterCounts.oldError
    positivity
  obtain ⟨hold,hbuffer,hpair,hdisj,hcover,hmasses⟩ := recorded_large_ready μ policy hpolicy active origin
    hgood hpositive (by omega) q m draw cutter (RefinedUpperRepair.nearError n) htau hquarter hscale hD
  have hbufpos := fun i => (hmasses i).2.1
  have hnear : Near chores μ active buffer old (RefinedUpperRepair.nearError n) := by
    intro i j
    cases chores
    · exact (le_abs_self _).trans ((hmasses i).2.2 j i)
    · exact (le_abs_self _).trans ((hmasses i).2.2 i j)
  have hhistory (j : Fin k) : (old j).history ⊆ buffer.history := by
    change (candidateOld _ active origin data cutter j).history ⊆
      (candidateBuffer _ active origin data cutter).history
    rw [candidateOld_history,candidateBuffer_history]
  let chosen : Preparation n k → Selection k := fun x =>
    candidateChoice hk active origin data cutter (prepReserve policy active buffer x)
  have hchosen : Measurable chosen :=
    candidateChoice_measurable hk active (fun _ => origin) (prepReserve policy active buffer)
      (fun _ => data) cutter measurable_const (freshReserve_measurable policy hmeas active buffer) measurable_const
  have hLambda : 0 < Lambda := div_pos hD (by positivity)
  apply acceptance_probability μ policy hpolicy hmeas (by omega) chores active hinj buffer hbuffer hbufpos
    old hold hnear hpair hdisj hhistory chosen hchosen Lambda hLambda
  intro p hp
  exact large_baseline μ policy hpolicy active origin hgood hpositive hinj hk q m draw cutter
    hbuffer hbufpos hD (view p).1
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
