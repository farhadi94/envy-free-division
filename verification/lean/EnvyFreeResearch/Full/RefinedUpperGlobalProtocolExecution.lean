import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolStageRun
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSnapshotRun
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolValidity
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolSelectionFactor

/-! Each concrete dispatcher step has an actual finite query trace, including
all rejected work. Pure normalization and terminal states have separate costs. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperCircularStage RefinedUpperGlobalTape UpperQueryPrograms Chores.QueryProgram
variable {n : ℕ}

def Phase.queryCap : Phase n → ℕ
  | .normalize _ => n+1
  | .snapshot _ => 12*n*RefinedUpperRepair.fine n
  | .firstShrink _ _ | .secondShrink _ => 8*n*RefinedUpperRepair.fine n
  | .finalRepair _ => 6*n*RefinedUpperRepair.fine n
  | .done _ => 0

def Phase.cutCap : Phase n → ℕ
  | .normalize _ => 1
  | .snapshot _ => 6*RefinedUpperRepair.fine n
  | .firstShrink _ _ | .secondShrink _ => 4*RefinedUpperRepair.fine n
  | .finalRepair _ => 3*RefinedUpperRepair.fine n
  | .done _ => 0

theorem normalize_history_phase (policy : Policy n) (fallback : Fin n) (chores : Bool) (a : Anchor n) :
    (RefinedUpperGlobalNormalize.execute policy fallback chores a).history =
      (RefinedUpperGlobalNormalize.execute policy fallback chores a).anchor.residue.history := by
  unfold RefinedUpperGlobalNormalize.execute
  cases RefinedUpperGlobalNormalize.normalize fallback chores n a <;> rfl

theorem step_executes (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (chores : Bool) (phase : Phase n)
    (hv : phase.Valid μ chores whole) (policy : Policy n) (fallback : Fin n) (draw : Universal n) :
    ∃ trace, Executes (totalPolicy policy) (phase.stepProgram fallback chores draw) phase.history
      (phase.step policy fallback chores draw) trace ∧
      (phase.step policy fallback chores draw).history=phase.history++trace ∧
      trace.length ≤ phase.queryCap ∧ (trace.map Prod.fst).countP isCut ≤ phase.cutCap := by
  cases phase with
  | normalize a =>
    obtain ⟨tr,he,hh,hq,hc⟩ := RefinedUpperGlobalNormalize.program_executes policy fallback chores a
    exact ⟨tr,he,(normalize_history_phase policy fallback chores a).trans hh,hq,hc⟩
  | snapshot a =>
    have hk : 3 ≤ a.active.card := hv.2.2.1
    letI : Nonempty (Fin a.active.card) := ⟨⟨0,by omega⟩⟩
    simpa only [Phase.stepProgram,Phase.step,dif_pos hk,Phase.history,Phase.queryCap,Phase.cutCap] using
      snapshotAttempt_executes a policy hk chores (draw (a.request (by omega) .snapshot))
  | firstShrink p G =>
    have hk : 3 ≤ p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    have hG : 1 ≤ G := by rw [hv.factor_eq inferInstance]; exact (firstFactor_range p (by omega) _).1
    simpa only [Phase.stepProgram,Phase.step,dif_pos hk,Phase.history,Phase.queryCap,Phase.cutCap] using
      firstShrinkAttempt_executes p policy (by omega) chores G hG (draw (p.anchor.request (by omega) .shrink))
  | secondShrink p =>
    have hk : 3 ≤ p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    simpa only [Phase.stepProgram,Phase.step,dif_pos hk,Phase.history,Phase.queryCap,Phase.cutCap] using
      secondShrinkAttempt_executes p policy (by omega) chores (draw (p.anchor.request (by omega) .shrink))
  | finalRepair p =>
    have hk : 3 ≤ p.anchor.active.card := hv.population
    letI : Nonempty (Fin p.anchor.active.card) := ⟨⟨0,by omega⟩⟩
    obtain ⟨tr,he,hh,hq,hc⟩ := repairAttempt_executes p policy (by omega) chores (draw (p.anchor.request (by omega) .repair))
    refine ⟨tr,?_,?_,hq,hc⟩
    · simpa only [Phase.stepProgram,dif_pos hk,Phase.step,Phase.history] using he
    · simpa only [Phase.step,dif_pos hk,Phase.history] using
        (repairAttempt_history p policy (by omega) chores (draw (p.anchor.request (by omega) .repair))).trans hh
  | done a =>
    exact ⟨[],Executes.returned _ _,by simp [Phase.step,Phase.history],by simp [Phase.queryCap],by simp [Phase.cutCap]⟩

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
