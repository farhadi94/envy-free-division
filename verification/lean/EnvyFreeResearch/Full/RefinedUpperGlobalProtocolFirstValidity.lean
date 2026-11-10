import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolFirstValidityAccepted
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolValidityRefresh

/-! Both outcomes of the actual first-Shrink attempt preserve the phase
invariant. Rejection retains the entire new query history and saved factor. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperCircularStage GlobalCompletion
variable {n : ℕ}

theorem firstShrinkAttempt_valid
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (whole : Set ℝ) (chores : Bool) (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (G : ℝ) (hp : p.FirstReady μ chores whole G)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) :
    (p.firstShrinkAttempt policy (by have := hp.population; omega) chores G tape).Valid μ chores whole := by
  have hk : 3≤p.anchor.active.card := hp.population
  by_cases hreject : (p.shrinkResult policy (by omega) chores G tape).2.2=true
  · have hfactor : G=p.firstFactor (if chores then .chore else .cake) := hp.factor_eq inferInstance
    have hrange : 1≤G ∧ G≤(2/RefinedUpperShrinkPrecision.theta n)*(8/RefinedUpperRepair.nearError n)^(p.anchor.active.card-1) := by
      rw [hfactor]
      exact firstFactor_range p (by omega) _
    have hr := refreshShrink_physical μ whole p hp.physical policy hpolicy hk chores
      (hp.toBasic.positive_local μ whole chores p) G hrange.1 hrange.2 tape
    have hh := pending_refresh_firstReady_of_physical μ whole p chores G hp
      (p.shrinkResult policy (by omega) chores G tape).2.1.history hr
    simpa only [Pending.firstShrinkAttempt,Pending.finishFirstShrink,Pending.finishShrink,hreject,
      if_true,Phase.Valid] using hh
  · exact firstShrinkAttempt_accepted_valid μ whole chores p G hp policy hpolicy tape (Bool.eq_false_iff.mpr hreject)

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
