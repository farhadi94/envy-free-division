import EnvyFreeResearch.Full.UpperGlobalRunChanceShrink
import EnvyFreeResearch.Full.UpperGlobalRunChanceBoolean
import EnvyFreeResearch.Full.UpperGlobalProtocolEvents
import EnvyFreeResearch.Full.UpperGlobalProtocolRepairValidityProbability

/-! The actual universal fresh draw has exactly the required local primitive
law at every valid paid phase, including the saved full query history. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.UpperGlobalRunChance
open UpperGlobalTape
variable {n : ℕ}

theorem request_false_probability (request : Request n) (reject : Draw n request → Bool)
    (hr : Measurable reject) :
    universalLaw n {draw | reject (draw request)=false} =
      drawLaw n request {tape | reject tape=false} :=
  (request_preserves n request).measure_preimage
    (hr (measurableSet_singleton false)).nullMeasurableSet

end EnvyFreeResearch.Full.UpperGlobalRunChance

namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperCircularStage UpperStageMeasurable
  UpperGlobalTape UpperGlobalRunChance UpperGlobalPhysicalFinish
variable {n : ℕ}

theorem shrinkReject_measurable (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hmeas : MeasurablePolicy policy) (hk : 2 ≤ p.anchor.active.card)
    (chores : Bool) (G : ℝ) :
    Measurable (fun tape => (p.shrinkResult policy hk chores G tape).2.2) := by
  have hr := UpperShrink.execute_measurable policy hmeas hk chores (enumerate p.anchor.active)
    (fun _ : UpperRepair.Tape n p.anchor.active.card => p.buffer) (fun _ => G) id
    measurable_const measurable_const measurable_id
  exact measurable_snd.comp (measurable_snd.comp hr)

theorem firstShrink_universal_factor (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (G : ℝ) (hp : p.FirstReady μ chores whole G)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) :
    1 ≤ (64/63 : ℝ≥0∞) * universalLaw n
      {draw | Phase.accepted policy chores (.firstShrink p G) draw=true} := by
  have hk : 2 ≤ p.anchor.active.card := by have := hp.population; omega
  have hr := shrinkReject_measurable p policy hmeas hk chores G
  have hf := success_factor_of_rejection (UpperRepair.law n p.anchor.active.card) _ hr
    (firstShrink_failure_lt μ whole chores p G hp policy hpolicy hmeas hk)
  have he : {draw | Phase.accepted policy chores (.firstShrink p G) draw=true} =
      {draw : Universal n | (p.shrinkResult policy hk chores G
        (draw (p.anchor.request hk .shrink))).2.2=false} := by
    ext draw
    simp only [Phase.accepted,dif_pos hp.population,Bool.not_eq_true']
  rw [he,request_false_probability (p.anchor.request hk .shrink) _ hr]
  exact hf

theorem secondShrink_universal_factor (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.SecondReady μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) :
    1 ≤ (64/63 : ℝ≥0∞) * universalLaw n
      {draw | Phase.accepted policy chores (.secondShrink p) draw=true} := by
  have hk : 2 ≤ p.anchor.active.card := by have := hp.population; omega
  have hr := shrinkReject_measurable p policy hmeas hk chores (2/UpperRepair.nearError n)
  have hf := success_factor_of_rejection (UpperRepair.law n p.anchor.active.card) _ hr
    (secondShrink_failure_lt μ whole chores p hp policy hpolicy hmeas hk)
  have he : {draw | Phase.accepted policy chores (.secondShrink p) draw=true} =
      {draw : Universal n | (p.shrinkResult policy hk chores (2/UpperRepair.nearError n)
        (draw (p.anchor.request hk .shrink))).2.2=false} := by
    ext draw
    simp only [Phase.accepted,dif_pos hp.population,Bool.not_eq_true']
  rw [he,request_false_probability (p.anchor.request hk .shrink) _ hr]
  exact hf

theorem repairReject_measurable (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hmeas : MeasurablePolicy policy) (hk : 2 ≤ p.anchor.active.card)
    (chores : Bool) : Measurable (fun tape => (p.repairResult policy hk chores tape).2.2) := by
  have hr := UpperRepairOutputMeasurable.execute_measurable policy hmeas hk chores
    (enumerate p.anchor.active) (fun _ : UpperRepair.Tape n p.anchor.active.card => p.buffer)
    (fun _ => localEndowments p) (UpperRepair.coarse n) (UpperRepair.fine n) (UpperRepair.repeats n)
    (UpperRepair.reserveMark n) (UpperRepair.cutoff n) (UpperRepair.cellBound n)
    (UpperRepair.gapMultiplier n) id measurable_const (fun _ => measurable_const) measurable_id
  exact measurable_snd.comp (measurable_snd.comp hr)

theorem repair_universal_factor (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.RepairReady μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) :
    1 ≤ (64/63 : ℝ≥0∞) * universalLaw n
      {draw | Phase.accepted policy chores (.finalRepair p) draw=true} := by
  have hk : 2 ≤ p.anchor.active.card := by have := hp.population; omega
  have hr := repairReject_measurable p policy hmeas hk chores
  have hf := success_factor_of_rejection (UpperRepair.law n p.anchor.active.card) _ hr
    (repairAttempt_failure_lt μ whole p chores hp policy hpolicy hmeas hk)
  have he : {draw | Phase.accepted policy chores (.finalRepair p) draw=true} =
      {draw : Universal n | (p.repairResult policy hk chores
        (draw (p.anchor.request hk .repair))).2.2=false} := by
    ext draw
    simp only [Phase.accepted,dif_pos hp.population,Bool.not_eq_true']
  rw [he,request_false_probability (p.anchor.request hk .repair) _ hr]
  exact hf

end EnvyFreeResearch.Full.UpperGlobalPhysical
