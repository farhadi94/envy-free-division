import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalRunChanceUniversal

/-! Reached Shrink and final-Repair phases inherit their actual primitive
success laws. There is no assumption on unreachable malformed phases. -/
noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable RefinedUpperGlobalTape
variable {n : ℕ}

theorem valid_shrink_phase_factor (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
    (phase : Phase n) (hv : phase.Valid μ chores whole) (hkind : phase.paidKind=some .shrink)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) :
    1 ≤ (64/63 : ℝ≥0∞) * universalLaw n {draw | Phase.accepted policy chores phase draw=true} := by
  cases phase with
  | normalize a => simp [Phase.paidKind] at hkind
  | snapshot a => simp [Phase.paidKind] at hkind
  | firstShrink p G =>
    have hp : p.FirstReady μ chores whole G := hv
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by have := hp.population; omega⟩⟩
    exact firstShrink_universal_factor μ whole chores p G hp policy hpolicy hmeas
  | secondShrink p =>
    have hp : p.SecondReady μ chores whole := hv
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by have := hp.population; omega⟩⟩
    exact secondShrink_universal_factor μ whole chores p hp policy hpolicy hmeas
  | finalRepair p => simp [Phase.paidKind] at hkind
  | done a => simp [Phase.paidKind] at hkind

theorem valid_repair_phase_factor (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)
    (phase : Phase n) (hv : phase.Valid μ chores whole) (hkind : phase.paidKind=some .repair)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) :
    1 ≤ (64/63 : ℝ≥0∞) * universalLaw n {draw | Phase.accepted policy chores phase draw=true} := by
  cases phase with
  | normalize a => simp [Phase.paidKind] at hkind
  | snapshot a => simp [Phase.paidKind] at hkind
  | firstShrink p G => simp [Phase.paidKind] at hkind
  | secondShrink p => simp [Phase.paidKind] at hkind
  | finalRepair p =>
    have hp : p.RepairReady μ chores whole := hv
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by have := hp.population; omega⟩⟩
    exact repair_universal_factor μ whole chores p hp policy hpolicy hmeas
  | done a => simp [Phase.paidKind] at hkind

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
