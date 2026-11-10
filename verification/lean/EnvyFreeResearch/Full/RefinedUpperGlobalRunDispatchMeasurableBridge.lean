import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunDispatchMeasurableStages

/-! Literal agreement of fixed-stratum finishes with the actual phase code. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRun.DispatchMeasurable
open RefinedUpperGlobalPhysical RefinedUpperGlobalNormalize RefinedUpperRepairProgram
variable {n : ℕ}

theorem finishSecondAt_eq (p : Pending n) (result : PhysicalResult n p.anchor.active.card) :
    finishSecondAt p.anchor.active p result = p.finishSecondShrink result := rfl

theorem snapshotPendingAt_eq (a : Anchor n) [Nonempty (Fin a.active.card)]
    (hk : 0 < a.active.card) (chores : Bool) (result : PhysicalResult n a.active.card) :
    snapshotPendingAt a.active hk chores a result = a.snapshotPending hk chores result := rfl

theorem finishSnapshotAt_eq (a : Anchor n) [Nonempty (Fin a.active.card)]
    (hk : 0 < a.active.card) (chores : Bool) (result : PhysicalResult n a.active.card) :
    finishSnapshotAt a.active hk chores a result = a.finishSnapshot hk chores result := rfl

theorem finishFirstAt_eq (p : Pending n) (chores : Bool) (G : ℝ)
    (result : PhysicalResult n p.anchor.active.card) :
    finishFirstAt p.anchor.active p chores G result = p.finishFirstShrink chores G result := by
  cases h : result.2.2 with
  | true => simp only [finishFirstAt,Pending.finishFirstShrink,h,ite_true,finishShrinkAt_eq]
  | false =>
    simp only [finishFirstAt,Pending.finishFirstShrink,h,Bool.false_eq_true,ite_false]
    let next := finishShrinkAt p.anchor.active p result
    change (match next.selectPhaseAt p.anchor.active (direction chores) with
      | some phase => phase | none => Phase.firstShrink next G) =
      (match next.selectTransfer (direction chores) with
      | some candidate => next.dispatchTransfer candidate | none => Phase.firstShrink next G)
    have ha : next.anchor.active=p.anchor.active := by
      simp only [next,finishShrinkAt,h,Bool.false_eq_true,ite_false,Pending.addShrink]
    have he : next.selectPhaseAt p.anchor.active (direction chores) =
        (next.selectTransfer (direction chores)).map next.dispatchTransfer := by
      rw [← ha]
      unfold Pending.selectPhaseAt
      rw [selectionDataAt_eq]
      change (next.selectTransfer (direction chores)).map (next.dispatchTransferAt next.anchor.active) = _
      congr 1
      funext c
      exact dispatchTransferAt_eq next c
    rw [he]
    cases next.selectTransfer (direction chores) <;> rfl

end EnvyFreeResearch.Full.RefinedUpperGlobalRun.DispatchMeasurable
