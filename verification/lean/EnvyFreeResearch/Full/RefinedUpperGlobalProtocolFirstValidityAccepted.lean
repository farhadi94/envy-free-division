import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolFirstValiditySelection

/-! An accepted actual first Shrink dispatches to a valid second Shrink or
final Repair. The finite selector succeeds from the saved Snapshot witness. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperCircularStage GlobalCompletion
open RefinedUpperGlobal.Transfer
variable {n : ℕ}

theorem firstShrinkAttempt_accepted_valid
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (whole : Set ℝ) (chores : Bool) (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (G : ℝ) (hp : p.FirstReady μ chores whole G)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card)
    (haccept : (p.shrinkResult policy (by have := hp.population; omega) chores G tape).2.2=false) :
    (p.firstShrinkAttempt policy (by have := hp.population; omega) chores G tape).Valid μ chores whole := by
  have hk : 3≤p.anchor.active.card := hp.population
  let direction : Direction := if chores then .chore else .cake
  have hfactor : G=p.firstFactor direction := hp.factor_eq inferInstance
  have hrange : 1≤G ∧ G≤(2/RefinedUpperShrinkPrecision.theta n)*(8/RefinedUpperRepair.nearError n)^(p.anchor.active.card-1) := by
    rw [hfactor]
    exact firstFactor_range p (by omega) direction
  let next := p.acceptShrink policy (by omega : 2≤p.anchor.active.card) chores G tape
  have hb : next.Basic μ chores whole := acceptShrink_basic μ whole chores p hp.toBasic policy hpolicy
    G hrange.1 hrange.2 tape haccept
  obtain ⟨c,hselect,hvalid,he⟩ := firstShrinkAttempt_accepted_selection μ whole chores p G hp policy hpolicy tape haccept
  rw [he]
  have hbc := transferCandidate_basic μ whole chores next hb c
  cases c with
  | commit alpha b h =>
    have hc := transferCandidate_commit_cached next direction alpha b h hvalid
    exact ⟨hbc,hc.1,hc.2.1,hc.2.2⟩
  | shrink b h =>
    have hc := selected_shrink_cached next direction b h hvalid
    exact ⟨hbc,rfl,hc.1,hc.2⟩

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
