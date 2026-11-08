import EnvyFreeResearch.Full.UpperGlobalProtocolDispatch
import EnvyFreeResearch.Full.UpperGlobalNormalizeCorrectness
import EnvyFreeResearch.Full.UpperGlobalPendingMassReady

/-! The concrete phase invariant for the global protocol. Each phase records
only facts already established by its preceding physical primitive. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution GlobalCompletion
variable {n : ℕ}

structure Pending.Basic (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (chores : Bool) (whole : Set ℝ) (p : Pending n) : Prop where
  physical : p.Physical μ whole
  anchor_valid : Valid (if chores then .chore else .cake) (p.anchor.table μ)
  population : 3 ≤ p.anchor.active.card
  snapshot_ef : ActiveEF (if chores then .chore else .cake) (value μ p.snapshot) p.anchor.active
  shrunk_ef : ActiveEF (if chores then .chore else .cake) (value μ p.shrunk) p.anchor.active
  positive : ∀ i ∈ p.anchor.active, 0 < total p.buffer i
  strong : UpperGlobal.Sink.StrongOn (p.anchor.edge (if chores then .chore else .cake)) p.anchor.active

structure Pending.FirstReady (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (chores : Bool) (whole : Set ℝ) (p : Pending n) (G : ℝ) : Prop
    extends p.Basic μ chores whole where
  permutation_identity : p.permutation = Equiv.refl _
  witness_active : p.witness ∈ p.anchor.active
  target_active : p.target ∈ p.anchor.active
  certificate : UpperShrinkPrecision.theta n * total p.buffer p.witness ≤
    p.snapshotGap (if chores then .chore else .cake) p.witness p.target
  factor_eq : ∀ inst : Nonempty (Fin p.anchor.active.card),
    G = @Pending.firstFactor n p inst (if chores then .chore else .cake)

structure Pending.SecondReady (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (chores : Bool) (whole : Set ℝ) (p : Pending n) : Prop
    extends p.Basic μ chores whole where
  permutation_identity : p.permutation = Equiv.refl _
  edge : p.anchor.edge (if chores then .chore else .cake) p.witness p.target
  bad : UpperRepair.nearError n * total p.buffer p.witness <
    p.snapshotGap (if chores then .chore else .cake) p.witness p.target

structure Pending.RepairReady (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (chores : Bool) (whole : Set ℝ) (p : Pending n) : Prop
    extends p.Basic μ chores whole where
  edge : p.anchor.edge (if chores then .chore else .cake) p.witness p.target
  own_loss : ∀ i ∈ p.anchor.active,
    p.snapshotGap (if chores then .chore else .cake) i (p.permutation i) ≤
      UpperRepair.nearError n * total p.buffer i
  large : 2 * total p.buffer p.witness ≤
    p.snapshotGap (if chores then .chore else .cake) p.witness (p.permutation p.target)

def Phase.Valid (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (chores : Bool) (whole : Set ℝ) : Phase n → Prop
  | .normalize a => a.Committed μ (if chores then .chore else .cake) whole ∧
      a.HistoryCompatible ∧ a.active.Nonempty
  | .snapshot a => UpperGlobalNormalize.Normalized μ chores whole (.snapshot a)
  | .firstShrink p G => p.FirstReady μ chores whole G
  | .secondShrink p => p.SecondReady μ chores whole
  | .finalRepair p => p.RepairReady μ chores whole
  | .done a => UpperGlobalNormalize.Normalized μ chores whole (.done a)

end EnvyFreeResearch.Full.UpperGlobalPhysical
