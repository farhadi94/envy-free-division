import EnvyFreeResearch.Full.UpperGlobalProtocolDispatch
import EnvyFreeResearch.Full.UpperSnapshotProtocolCost

/-! Oracle trace and history of the actual Snapshot phase callback. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperZeroRows UpperQueryPrograms Chores.QueryProgram
variable {n : ℕ}

theorem finishSnapshot_history (a : Anchor n) [Nonempty (Fin a.active.card)]
    (hk : 0 < a.active.card) (chores : Bool)
    (r : UpperRepairProgram.PhysicalResult n a.active.card) :
    (a.finishSnapshot hk chores r).history=r.2.1.history := by
  unfold Anchor.finishSnapshot
  split
  · rfl
  · split <;> rfl

theorem snapshotAttempt_executes (a : Anchor n) [Nonempty (Fin a.active.card)]
    (policy : Policy n) (hk : 3 ≤ a.active.card) (chores : Bool)
    (tape : UpperSnapshotProtocol.Tape n a.active.card) :
    ∃ trace, Executes (totalPolicy policy) (a.snapshotProgram hk chores tape) a.residue.history
      (a.snapshotAttempt policy hk chores tape) trace ∧
      (a.snapshotAttempt policy hk chores tape).history=a.residue.history++trace ∧
      trace.length ≤ 12*n*UpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 6*UpperRepair.fine n := by
  obtain ⟨tr,he,hh,hq,hc⟩ := UpperSnapshotProtocol.snapshot_program_cost policy hk chores
    (enumerate a.active) (enumerate_injective _) a.residue ⟨0,by omega⟩ tape
  refine ⟨tr,?_,?_,hq,hc⟩
  · simpa only [Anchor.snapshotProgram,Anchor.snapshotAttempt,Anchor.snapshotResult,List.append_nil] using
      he.bind (fun result => .returned (a.finishSnapshot (by omega) chores result)) (Executes.returned _ _)
  · exact (finishSnapshot_history a (by omega) chores _).trans hh

theorem finishRepair_history (p : Pending n)
    (r : UpperRepairProgram.PhysicalResult n p.anchor.active.card) :
    (p.finishRepair r).history=r.2.1.history := by
  unfold Pending.finishRepair
  split <;> rfl

theorem repairAttempt_history (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (tape : UpperRepair.Tape n p.anchor.active.card) :
    (p.repairAttempt policy hk chores tape).history=(p.repairResult policy hk chores tape).2.1.history :=
  finishRepair_history p _

end EnvyFreeResearch.Full.UpperGlobalPhysical
