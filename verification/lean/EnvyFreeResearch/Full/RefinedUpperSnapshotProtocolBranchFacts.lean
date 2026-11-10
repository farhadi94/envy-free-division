import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolFacts
import EnvyFreeResearch.Full.UpperSnapshotProtocolZeroPhysical
import EnvyFreeResearch.Full.RefinedUpperSnapshotProtocolSafety

/-! Complete physical Snapshot facts from each already checked primitive.
The positive-residue branch uses the actual checked Repair output; the zero
branch is a complete allocation with no leftover material. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperRepairProgram UpperRepairPreparationChecks UpperSnapshotSmall
open UpperSnapshotProtocol (zeroExecute zeroFinish zeroFinish_success zero_success_complete)
variable {n k : ℕ} [Nonempty (Fin k)]

theorem repaired_snapshot_facts
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
    (whole buffer : State n) (hbuffer : WellFormed μ buffer)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain buffer.cells))
    (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
    (hnear : Near chores μ active buffer old (RefinedUpperRepair.nearError n))
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain buffer.cells))
    (holdHistory : ∀ j, (old j).history ⊆ buffer.history)
    (hcover : (⋃ j, domain (old j).cells) ∪ domain buffer.cells = domain whole.cells)
    (p : RefinedUpperRepair.Tape n k)
    (hs : (restoreRejected whole (execute policy hk chores active (margin n) buffer old p)).2.2=false) :
    SnapshotSuccessFacts μ chores active whole
      (restoreRejected whole (execute policy hk chores active (margin n) buffer old p)) := by
  have hp := (restoreRejected_success whole _).mp hs
  have he : restoreRejected whole (execute policy hk chores active (margin n) buffer old p) =
      execute policy hk chores active (margin n) buffer old p := by simp [restoreRejected,hp]
  rw [he]
  have hf := success_facts μ policy hpolicy hk chores active hinj buffer hbuffer hpositive old hold hnear
    holdpair holdbuffer holdHistory (margin n) p hp
  refine ⟨hf.allocation_wellFormed,hf.residue_wellFormed,hf.allocation_disjoint,hf.residue_disjoint,
    hf.material_preserved.trans hcover,hf.envyFree,hf.common_history,Or.inr ⟨?_,?_⟩⟩
  · intro i
    exact (mul_pos (by norm_num) (hpositive i)).trans (hf.residue_mass i).1
  · exact success_margin μ policy hpolicy hk chores active hinj buffer hbuffer hpositive old hold hnear
      holdpair holdbuffer holdHistory (margin n) p hp

theorem zero_snapshot_facts
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 0 < k) (chores : Bool) (active : Fin k → Fin n) (origin : State n)
    (hgood : WellFormed μ origin) (cutter : Fin k)
    (hpositive : 0 < (μ (active cutter)).real (domain origin.cells)) (start : UpperSnapshotSmall.Circle)
    (hs : (zeroExecute policy hk chores active origin cutter start).2.2=false) :
    SnapshotSuccessFacts μ chores active origin (zeroExecute policy hk chores active origin cutter start) := by
  obtain ⟨ha,hr,hrem,hcover,hpair,hef⟩ := zero_success_complete μ policy hpolicy hk chores active origin hgood cutter hpositive start hs
  have hp := (zeroFinish_success hk chores active start _).mp hs
  refine ⟨ha,hr,hpair,?_,?_,hef,?_,Or.inl ?_⟩
  · intro j
    rw [hrem]
    exact disjoint_empty _
  · rw [hrem,union_empty]
    exact hcover
  · intro j
    unfold zeroExecute
    rw [zeroFinish,if_pos hp]
    rfl
  · unfold zeroExecute
    rw [zeroFinish,if_pos hp]
end EnvyFreeResearch.Full.RefinedUpperSnapshotProtocol
