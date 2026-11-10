import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSnapshotPhysicalActual
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolFirstValidity
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSecondValidity
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolRepairValidity
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolEvents

/-! Full pathwise invariant of the concrete global protocol on every tape.
No successful primitive or termination oracle is assumed. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape
variable {n : ℕ}

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool)

theorem normalized_valid (phase : Phase n)
    (h : RefinedUpperGlobalNormalize.Normalized μ chores whole phase) : phase.Valid μ chores whole := by
  cases phase <;> first | exact h | exact h.elim

theorem step_valid (phase : Phase n) (hv : phase.Valid μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (fallback : Fin n) (draw : Universal n) :
    (phase.step policy fallback chores draw).Valid μ chores whole := by
  cases phase with
  | normalize a =>
    exact normalized_valid μ whole chores _
      (RefinedUpperGlobalNormalize.execute_valid μ policy hpolicy fallback chores whole a hv.1 hv.2.1 hv.2.2)
  | snapshot a =>
    have hk : 3 ≤ a.active.card := hv.2.2.1
    letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
    simpa only [Phase.step,dite_eq_left hk] using
      snapshotAttempt_valid μ a policy hpolicy hk chores whole hv (draw (a.request (by omega) .snapshot))
  | firstShrink p G =>
    have hk : 3 ≤ p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    simpa only [Phase.step,dite_eq_left hk] using
      firstShrinkAttempt_valid μ whole chores p G hv policy hpolicy (draw (p.anchor.request (by omega) .shrink))
  | secondShrink p =>
    have hk : 3 ≤ p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    simpa only [Phase.step,dite_eq_left hk] using
      secondShrinkAttempt_valid μ whole chores p hv policy hpolicy (by omega) (draw (p.anchor.request (by omega) .shrink))
  | finalRepair p =>
    have hk : 3 ≤ p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    simpa only [Phase.step,dite_eq_left hk] using
      repairAttempt_valid μ whole p chores hv policy hpolicy (by omega) (draw (p.anchor.request (by omega) .repair))
  | done a => exact hv

theorem run_valid (initial : Phase n) (hinit : initial.Valid μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (fallback : Fin n) (t : ℕ) (omega : Stream (Universal n)) :
    (Phase.run policy fallback chores initial t omega).Valid μ chores whole := by
  induction t with
  | zero => exact hinit
  | succ t ih => exact step_valid μ whole chores _ ih policy hpolicy fallback (omega t)

theorem run_done_complete (initial : Phase n) (hinit : initial.Valid μ chores whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (fallback : Fin n) (t : ℕ) (omega : Stream (Universal n)) (a : Anchor n)
    (hdone : Phase.run policy fallback chores initial t omega=.done a) :
    a.Committed μ (if chores then .chore else .cake) whole ∧ a.HistoryCompatible ∧
      (⋃ j, UpperRecordedDomain.domain (a.bundles j).cells)=whole := by
  have hv := run_valid μ whole chores initial hinit policy hpolicy fallback t omega
  rw [hdone] at hv
  exact hv

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
