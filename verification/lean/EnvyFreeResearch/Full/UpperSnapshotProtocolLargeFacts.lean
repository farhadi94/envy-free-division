import EnvyFreeResearch.Full.UpperSnapshotProtocolBranchFacts
import EnvyFreeResearch.Full.UpperSnapshotIntegrationLarge

/-! Every accepted actual large-disagreement branch has the full physical
Snapshot contract, independently of the random good events used to prove its
acceptance probability. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperSnapshotCandidates UpperRepairPreparationChecks UpperRepairParameters
variable {n k : ℕ} [Nonempty (Fin k)]

theorem large_snapshot_facts
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (draw : Fin (UpperRepair.fine n) → Fin k × I) (cutter : Fin k)
    (hD : 0 < selectedDistance (by omega) (UpperGridData.table active origin
      (UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) draw)) cutter)
    (fresh : UpperRepair.Tape n k)
    (hs : (restoreRejected origin (execute policy (by omega) chores active (margin n)
      (candidateBuffer (by omega) active origin (UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) draw) cutter)
      (candidateOld (by omega) active origin (UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) draw) cutter) fresh)).2.2=false) :
    SnapshotSuccessFacts μ chores active origin
      (restoreRejected origin (execute policy (by omega) chores active (margin n)
        (candidateBuffer (by omega) active origin (UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) draw) cutter)
        (candidateOld (by omega) active origin (UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) draw) cutter) fresh)) := by
  let data := UpperGridMerge.prepare policy active origin (UpperRepair.coarse n) (UpperRepair.fine n) draw
  let old := candidateOld (by omega) active origin data cutter
  let buffer := candidateBuffer (by omega) active origin data cutter
  have hscale := coarse_cap_small (scale_large n) (by exact_mod_cast logarithm_positive (scale_large n))
  have htau : 0 ≤ UpperRepair.nearError n :=
    (oldError_positive (scale_large n) (by exact_mod_cast logarithm_positive (scale_large n))).le
  obtain ⟨hold,hbuffer,hpair,hdisj,hcover,hmasses⟩ := recorded_large_ready μ policy hpolicy active origin
    hgood hpositive (by omega) (UpperRepair.coarse n) (UpperRepair.fine n) draw cutter
    (UpperRepair.nearError n) htau hscale.2 hscale.1 hD
  have hnear : Near chores μ active buffer old (UpperRepair.nearError n) := by
    intro i j
    cases chores
    · exact (le_abs_self _).trans ((hmasses i).2.2 j i)
    · exact (le_abs_self _).trans ((hmasses i).2.2 i j)
  have hhistory (j : Fin k) : (old j).history ⊆ buffer.history := by
    change (candidateOld _ _ _ _ _ j).history ⊆ (candidateBuffer _ _ _ _ _).history
    rw [candidateOld_history,candidateBuffer_history]
  exact repaired_snapshot_facts μ policy hpolicy (by omega) chores active hinj origin buffer hbuffer
    (fun i => (hmasses i).2.1) old hold hnear hpair hdisj hhistory hcover fresh hs
end EnvyFreeResearch.Full.UpperSnapshotProtocol
