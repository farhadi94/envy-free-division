import EnvyFreeResearch.Full.UpperGlobalProtocolSnapshotPhysicalValidity
import EnvyFreeResearch.Full.UpperSnapshotProtocolSuccess
import EnvyFreeResearch.Full.UpperSnapshotProtocolLegalityAllHistory

/-! The actual executed Snapshot call preserves the global phase invariant
on every tape. Local success and history obligations are instantiated from the
concrete producer; no abstract successful-Snapshot premise remains. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperCircularStage
variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (a : Anchor n) [Nonempty (Fin a.active.card)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (hk : 3 ≤ a.active.card) (chores : Bool) (whole : Set ℝ)
  (ha : Phase.Valid μ chores whole (.snapshot a))

include ha in
theorem snapshot_input_positive (i : Fin a.active.card) :
    0 < (μ (enumerate a.active i)).real (domain a.residue.cells) := by
  rw [← total_correct μ _ ha.1.1.residue_wellFormed]
  exact ha.2.2.2.1 _ (enumerate_mem a.active i)

include ha hpolicy in
theorem snapshotAttempt_valid (tape : UpperSnapshotProtocol.Tape n a.active.card) :
    Phase.Valid μ chores whole (a.snapshotAttempt policy hk chores tape) := by
  have hp := snapshot_input_positive μ a chores whole ha
  apply finishSnapshot_valid μ a (by omega) chores whole ha
  · exact UpperSnapshotProtocol.snapshot_history_truthful μ policy hpolicy hk chores
      (enumerate a.active) (enumerate_injective _) a.residue ha.1.1.residue_wellFormed hp ⟨0,by omega⟩ tape
  · exact UpperSnapshotProtocol.snapshot_history_extension policy hk chores
      (enumerate a.active) (enumerate_injective _) a.residue ⟨0,by omega⟩ tape
  · intro hs
    exact UpperSnapshotProtocol.snapshot_success_facts μ policy hpolicy hk chores
      (enumerate a.active) (enumerate_injective _) a.residue ha.1.1.residue_wellFormed hp ⟨0,by omega⟩ tape hs

end EnvyFreeResearch.Full.UpperGlobalPhysical
