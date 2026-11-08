import EnvyFreeResearch.Full.UpperGlobalProtocolDispatch
import EnvyFreeResearch.Full.UpperGlobalProtocolSelectionSecond

/-! Actual oracle traces of the shrinking stage callbacks. -/
noncomputable section
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperZeroRows UpperQueryPrograms Chores.QueryProgram
variable {n : ℕ}

theorem finishShrink_history (p : Pending n)
    (r : UpperRepairProgram.PhysicalResult n p.anchor.active.card) :
    (p.finishShrink r).buffer.history=r.2.1.history := by
  unfold Pending.finishShrink
  split <;> rfl

theorem finishFirstShrink_history (p : Pending n) (chores : Bool) (G : ℝ)
    (r : UpperRepairProgram.PhysicalResult n p.anchor.active.card) :
    (p.finishFirstShrink chores G r).history=r.2.1.history := by
  unfold Pending.finishFirstShrink
  split
  · exact finishShrink_history p r
  · cases hc : (p.finishShrink r).selectTransfer (if chores then .chore else .cake) with
    | none => simp only [hc]; exact finishShrink_history p r
    | some c => simp only [hc]; cases c <;> exact finishShrink_history p r

theorem finishSecondShrink_history (p : Pending n)
    (r : UpperRepairProgram.PhysicalResult n p.anchor.active.card) :
    (p.finishSecondShrink r).history=r.2.1.history := by
  unfold Pending.finishSecondShrink
  split <;> exact finishShrink_history p r

theorem firstShrinkAttempt_executes (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool) (G : ℝ)
    (hG : 1 ≤ G) (tape : UpperRepair.Tape n p.anchor.active.card) :
    ∃ trace, Executes (totalPolicy policy) (p.firstShrinkProgram hk chores G tape) p.buffer.history
      (p.firstShrinkAttempt policy hk chores G tape) trace ∧
      (p.firstShrinkAttempt policy hk chores G tape).history=p.buffer.history++trace ∧
      trace.length ≤ 8*n*UpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 4*UpperRepair.fine n := by
  obtain ⟨tr,he,hh,hq,hc⟩ := UpperShrink.program_cost policy hk chores
    (enumerate p.anchor.active) (enumerate_injective _) p.buffer G hG tape
  refine ⟨tr,?_,?_,hq,hc⟩
  · simpa only [Pending.firstShrinkProgram,Pending.firstShrinkAttempt,Pending.shrinkResult,List.append_nil] using
      he.bind (fun result => .returned (p.finishFirstShrink chores G result)) (Executes.returned _ _)
  · exact (finishFirstShrink_history p chores G _).trans hh

theorem secondShrinkAttempt_executes (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool)
    (tape : UpperRepair.Tape n p.anchor.active.card) :
    ∃ trace, Executes (totalPolicy policy) (p.secondShrinkProgram hk chores tape) p.buffer.history
      (p.secondShrinkAttempt policy hk chores tape) trace ∧
      (p.secondShrinkAttempt policy hk chores tape).history=p.buffer.history++trace ∧
      trace.length ≤ 8*n*UpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 4*UpperRepair.fine n := by
  obtain ⟨tr,he,hh,hq,hc⟩ := UpperShrink.program_cost policy hk chores
    (enumerate p.anchor.active) (enumerate_injective _) p.buffer (2/UpperRepair.nearError n)
      (secondFactor_range p hk).1 tape
  refine ⟨tr,?_,?_,hq,hc⟩
  · simpa only [Pending.secondShrinkProgram,Pending.secondShrinkAttempt,Pending.shrinkResult,List.append_nil] using
      he.bind (fun result => .returned (p.finishSecondShrink result)) (Executes.returned _ _)
  · exact (finishSecondShrink_history p _).trans hh

end EnvyFreeResearch.Full.UpperGlobalPhysical
