import EnvyFreeResearch.Full.UpperGlobalProtocolShrinkValidity
import EnvyFreeResearch.Full.UpperGlobalProtocolSelectionFactor
import EnvyFreeResearch.Full.UpperGlobalProtocolSelectionSecond
import EnvyFreeResearch.Full.UpperShrinkExecuteMeasurable

/-! Actual Shrink rejection laws follow from the reached phase invariant and
its prescribed scale. No phase-level success-probability premise is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperCircularStage UpperStageMeasurable
variable {n : ℕ}

theorem basicShrink_failure_lt (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.Basic μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (G : ℝ) (hG : 1 ≤ G)
    (hmax : G ≤ (2/UpperShrinkPrecision.theta n)*(8/UpperRepair.nearError n)^(p.anchor.active.card-1))
    (hk : 2 ≤ p.anchor.active.card) :
    UpperRepair.law n p.anchor.active.card
      {tape | (p.shrinkResult policy hk chores G tape).2.2=true} < 1/64 := by
  exact UpperShrink.failure_lt μ policy hpolicy hp.population (enumerate p.anchor.active)
    (enumerate_injective _) p.buffer hp.physical.buffer_wf
    (hp.positive_local μ whole chores p) G hG hmax chores hmeas

theorem firstShrink_failure_lt (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (G : ℝ) (hp : p.FirstReady μ chores whole G)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (hk : 2 ≤ p.anchor.active.card) :
    UpperRepair.law n p.anchor.active.card
      {tape | (p.shrinkResult policy hk chores G tape).2.2=true} < 1/64 := by
  have hg := firstFactor_range p hk (if chores then .chore else .cake)
  have he := hp.factor_eq inferInstance
  apply basicShrink_failure_lt μ whole chores p hp.toBasic policy hpolicy hmeas G _ _ hk
  · simpa only [he] using hg.1
  · simpa only [he] using hg.2

theorem secondShrink_failure_lt (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.SecondReady μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (hk : 2 ≤ p.anchor.active.card) :
    UpperRepair.law n p.anchor.active.card
      {tape | (p.shrinkResult policy hk chores (2/UpperRepair.nearError n) tape).2.2=true} < 1/64 := by
  have hg := secondFactor_range p hk
  exact basicShrink_failure_lt μ whole chores p hp.toBasic policy hpolicy hmeas _ hg.1 hg.2 hk

end EnvyFreeResearch.Full.UpperGlobalPhysical
