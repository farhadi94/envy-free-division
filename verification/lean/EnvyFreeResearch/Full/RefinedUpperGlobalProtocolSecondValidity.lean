import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolShrinkValidity
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionSecond
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolValidityRefresh

/-! An accepted second Shrink yields the actual final-Repair invariant. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperCircularStage
open RefinedUpperGlobal.Transfer
variable {n : ℕ}

theorem acceptSecondShrink_ready (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.SecondReady μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card)
    (haccept : (p.shrinkResult policy (by have := hp.population; omega) chores
      (2/RefinedUpperRepair.nearError n) tape).2.2=false) :
    (p.acceptShrink policy (by have := hp.population; omega) chores
      (2/RefinedUpperRepair.nearError n) tape).RepairReady μ chores whole := by
  let next := p.acceptShrink policy (by have := hp.population; omega) chores
    (2/RefinedUpperRepair.nearError n) tape
  have hrange := secondFactor_range p (by have := hp.population; omega)
  have hb := acceptShrink_basic μ whole chores p hp.toBasic policy hpolicy _ hrange.1 hrange.2 tape haccept
  have hv := commit_after_actual_secondShrink μ whole p hp.physical policy hpolicy hp.population
    chores (hp.toBasic.positive_local μ whole chores p) hp.edge hp.bad tape haccept
  have hid : next.permutation=Equiv.refl _ := hp.permutation_identity
  refine ⟨hb,hp.edge,?_,?_⟩
  · intro i hi
    change next.snapshotGap (if chores then .chore else .cake) i (next.permutation i) ≤ _
    rw [hid]
    change GlobalCompletion.margin _ _ i i ≤ _
    rw [GlobalCompletion.margin_self]
    exact mul_nonneg (RefinedUpperShrink.nearError_positive n).le (hb.positive i hi).le
  · have hh := hv.2.2
    change 2*total next.buffer (enumerate p.anchor.active (activeIndex p.anchor.active p.witness)) ≤
      next.snapshotGap (if chores then .chore else .cake)
        (enumerate p.anchor.active (activeIndex p.anchor.active p.witness))
        (enumerate p.anchor.active (activeIndex p.anchor.active p.target)) at hh
    rw [enumerate_activeIndex _ _ hp.edge.1,enumerate_activeIndex _ _ hp.edge.2.1] at hh
    change 2*total next.buffer p.witness ≤ next.snapshotGap _ p.witness (next.permutation p.target)
    rw [hid]
    exact hh

theorem secondShrinkAttempt_valid (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.SecondReady μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 2 ≤ p.anchor.active.card) (tape : RefinedUpperRepair.Tape n p.anchor.active.card) :
    Phase.Valid μ chores whole (p.secondShrinkAttempt policy hk chores tape) := by
  cases hres : (p.shrinkResult policy hk chores (2/RefinedUpperRepair.nearError n) tape).2.2 with
  | false =>
    have h := acceptSecondShrink_ready μ whole chores p hp policy hpolicy tape hres
    simpa only [Pending.secondShrinkAttempt,Pending.finishSecondShrink,Pending.finishShrink,
      hres,Bool.false_eq_true,ite_false,Phase.Valid,Pending.acceptShrink] using h
  | true =>
    have hrange := secondFactor_range p hk
    have hphysical := refreshShrink_physical μ whole p hp.physical policy hpolicy hp.population
      chores (hp.toBasic.positive_local μ whole chores p) _ hrange.1 hrange.2 tape
    have h := pending_refresh_secondReady_of_physical μ whole p chores hp _ hphysical
    simpa only [Pending.secondShrinkAttempt,Pending.finishSecondShrink,Pending.finishShrink,
      hres,ite_true,Phase.Valid] using h

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
