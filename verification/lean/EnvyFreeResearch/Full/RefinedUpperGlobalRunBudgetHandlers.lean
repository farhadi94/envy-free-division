import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunBudgetTerminal
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolRepairValidity

/-! Credit changes of the concrete response handlers. Failed calls retain
in-flight credit; an accepted Snapshot either starts it or saturates the cap. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
open RefinedUpperGlobalPhysical UpperRecordedDomain UpperCorrectionExecution GlobalCompletion
variable {n : ℕ}

def acceptedBit (rejected : Bool) : ℕ := if rejected then 0 else 1

theorem finishShrink_anchor (p : Pending n)
    (result : RefinedUpperRepairProgram.PhysicalResult n p.anchor.active.card) :
    (p.finishShrink result).anchor=p.anchor := by
  unfold Pending.finishShrink
  split <;> rfl

theorem dispatchTransfer_credit (p : Pending n) (chores : Bool)
    (candidate : RefinedUpperGlobal.Transfer.Selection.Candidate p.anchor.active.card) :
    credit chores (p.dispatchTransfer candidate)=
      p.anchor.cachedPotential (if chores then .chore else .cake)+1 := by
  cases candidate <;> rfl

theorem first_handler_credit (p : Pending n) (chores : Bool) (G : ℝ)
    (result : RefinedUpperRepairProgram.PhysicalResult n p.anchor.active.card) :
    credit chores (p.finishFirstShrink chores G result)=credit chores (.firstShrink p G) := by
  cases hr : result.2.2 with
  | true =>
    simp only [Pending.finishFirstShrink,hr,ite_true]
    change (p.finishShrink result).anchor.cachedPotential _+1=p.anchor.cachedPotential _+1
    rw [finishShrink_anchor]
  | false =>
    simp only [Pending.finishFirstShrink,hr,Bool.false_eq_true,ite_false]
    cases hs : (p.finishShrink result).selectTransfer (if chores then .chore else .cake) with
    | none =>
      simp only [hs]
      change (p.finishShrink result).anchor.cachedPotential _+1=p.anchor.cachedPotential _+1
      rw [finishShrink_anchor]
    | some c =>
      simp only [hs]
      rw [dispatchTransfer_credit,finishShrink_anchor]
      rfl

theorem second_handler_credit (p : Pending n) (chores : Bool)
    (result : RefinedUpperRepairProgram.PhysicalResult n p.anchor.active.card) :
    credit chores (p.finishSecondShrink result)=credit chores (.secondShrink p) := by
  unfold Pending.finishSecondShrink
  split <;> change (p.finishShrink result).anchor.cachedPotential _+1=p.anchor.cachedPotential _+1
  all_goals rw [finishShrink_anchor]

theorem snapshot_handler_remaining (a : Anchor n) [Nonempty (Fin a.active.card)]
    (hk : 0<a.active.card) (chores : Bool)
    (result : RefinedUpperRepairProgram.PhysicalResult n a.active.card) :
    remainingCalls (a.finishSnapshot hk chores result) ≤ 3*acceptedBit result.2.2 := by
  unfold Anchor.finishSnapshot
  split
  · rename_i hr
    simp [remainingCalls,acceptedBit,hr]
  · rename_i hr
    split <;> simp [remainingCalls,acceptedBit,hr]

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ)

theorem snapshot_handler_credit (a : Anchor n) [Nonempty (Fin a.active.card)]
    (hk : 0<a.active.card) (chores : Bool)
    (result : RefinedUpperRepairProgram.PhysicalResult n a.active.card)
    (ha : (Phase.snapshot a).Valid μ chores whole)
    (hb : (a.finishSnapshot hk chores result).Valid μ chores whole) :
    credit chores (.snapshot a)+acceptedBit result.2.2 ≤
      credit chores (a.finishSnapshot hk chores result) := by
  by_cases hr : result.2.2=true
  · simp only [Anchor.finishSnapshot,hr,ite_true] at hb ⊢
    change a.cachedPotential _+acceptedBit true ≤ (refresh a result.2.1.history).cachedPotential _
    rw [refreshed_potential μ whole a _ _ ha.1.1 hb.1.1]
    simp [acceptedBit]
  · have hf : result.2.2=false := Bool.eq_false_iff.mpr hr
    by_cases hz : result.2.1.cells=[]
    · simp only [Anchor.finishSnapshot,hf,Bool.false_eq_true,ite_false,hz,ite_true] at hb ⊢
      change a.cachedPotential _+1 ≤ (terminal a _ _).cachedPotential _
      rw [valid_done_saturated μ whole chores _ hb]
      exact valid_snapshot_room μ chores whole a ha
    · simp only [Anchor.finishSnapshot,hf,Bool.false_eq_true,ite_false,hz,ite_false]
      exact le_rfl

end EnvyFreeResearch.Full.RefinedUpperGlobalRunBudget
