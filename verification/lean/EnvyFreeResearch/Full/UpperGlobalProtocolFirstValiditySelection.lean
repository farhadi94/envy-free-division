import EnvyFreeResearch.Full.UpperGlobalProtocolFirstValidityReachability
import EnvyFreeResearch.Full.UpperGlobalProtocolShrinkValidity
import EnvyFreeResearch.Full.UpperGlobalProtocolSelectionSecond

/-! An accepted actual first Shrink dispatches to a valid second Shrink or
final Repair. The finite selector succeeds from the saved Snapshot witness. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperCircularStage GlobalCompletion
open UpperGlobal.Transfer
variable {n : ℕ}

theorem firstShrinkAttempt_accepted_selection
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (whole : Set ℝ) (chores : Bool) (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (G : ℝ) (hp : p.FirstReady μ chores whole G)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (tape : UpperRepair.Tape n p.anchor.active.card)
    (haccept : (p.shrinkResult policy (by have := hp.population; omega) chores G tape).2.2=false) :
    let next := p.acceptShrink policy (by have := hp.population; omega) chores G tape
    ∃ c, next.selectTransfer (if chores then .chore else .cake)=some c ∧
      Selection.Valid (UpperRepair.nearError n) (next.selectionData (if chores then .chore else .cake)) c ∧
      p.firstShrinkAttempt policy (by have := hp.population; omega) chores G tape=next.dispatchTransfer c := by
  have hk : 3≤p.anchor.active.card := hp.population
  let direction : Direction := if chores then .chore else .cake
  have hfactor : G=p.firstFactor direction := hp.factor_eq inferInstance
  have hrange : 1≤G ∧ G≤(2/UpperShrinkPrecision.theta n)*(8/UpperRepair.nearError n)^(p.anchor.active.card-1) := by
    rw [hfactor]
    exact firstFactor_range p (by omega) direction
  let next := p.acceptShrink policy (by omega : 2≤p.anchor.active.card) chores G tape
  have hb : next.Basic μ chores whole := acceptShrink_basic μ whole chores p hp.toBasic policy hpolicy
    G hrange.1 hrange.2 tape haccept
  have hs : ∃ c, next.selectTransfer direction=some c ∧
      Selection.Valid (UpperRepair.nearError n) (next.selectionData direction) c := by
    dsimp [next]
    rw [hfactor]
    exact selectTransfer_after_actual_firstShrink μ whole p hp.physical policy hpolicy hk chores
      (hp.toBasic.positive_local μ whole chores p) hp.snapshot_ef hp.witness_active hp.target_active
      hp.certificate (localGraph_reachable p direction hp.strong) tape (by simpa only [hfactor] using haccept)
  obtain ⟨c,hselect,hvalid⟩ := hs
  have hresult : p.shrinkResult policy (by omega) chores G tape =
      ((p.shrinkResult policy (by omega) chores G tape).1,
        (p.shrinkResult policy (by omega) chores G tape).2.1,false) := by
    apply Prod.ext
    · rfl
    · exact Prod.ext rfl haccept
  have he : p.firstShrinkAttempt policy (by omega) chores G tape=next.dispatchTransfer c := by
    rw [Pending.firstShrinkAttempt,hresult]
    dsimp only [Pending.finishFirstShrink,Pending.finishShrink,Bool.false_eq_true,ite_false]
    change (match next.selectTransfer direction with
      | some candidate => next.dispatchTransfer candidate
      | none => Phase.firstShrink next G)=next.dispatchTransfer c
    rw [hselect]
  exact ⟨c,hselect,hvalid,he⟩

end EnvyFreeResearch.Full.UpperGlobalPhysical
