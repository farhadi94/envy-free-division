import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolShrink

/-! A paid Shrink attempt as an actual oracle program on the pending state.
Rejected calls preserve material and retain their entire query history. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution UpperZeroRows UpperCircularStage
open UpperQueryPrograms Chores.QueryProgram
variable {n : ℕ}

def Pending.finishShrink (p : Pending n)
    (result : RefinedUpperRepairProgram.PhysicalResult n p.anchor.active.card) : Pending n :=
  if result.2.2 then p.refresh result.2.1.history
  else p.addShrink (extendPieces p.anchor.active result.1 result.2.1.history) result.2.1

def Pending.shrinkAttempt (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool) (G : ℝ)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) : Pending n :=
  p.finishShrink (p.shrinkResult policy hk chores G tape)

def Pending.shrinkProgram (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (hk : 2 ≤ p.anchor.active.card) (chores : Bool) (G : ℝ)
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) : QProgram n (Pending n) :=
  (RefinedUpperShrink.program hk chores (enumerate p.anchor.active) p.buffer G tape).bind
    (fun result => .returned (p.finishShrink result))

theorem shrinkAttempt_executes (p : Pending n) [Nonempty (Fin p.anchor.active.card)]
    (policy : Policy n) (hk : 2 ≤ p.anchor.active.card) (chores : Bool) (G : ℝ)
    (hG : 1 ≤ G) (tape : RefinedUpperRepair.Tape n p.anchor.active.card) :
    ∃ trace, Executes (totalPolicy policy) (p.shrinkProgram hk chores G tape) p.buffer.history
      (p.shrinkAttempt policy hk chores G tape) trace ∧
      (p.shrinkAttempt policy hk chores G tape).buffer.history=p.buffer.history++trace ∧
      trace.length ≤ 8*n*RefinedUpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 4*RefinedUpperRepair.fine n := by
  obtain ⟨tr,he,hh,hq,hc⟩ := RefinedUpperShrink.program_cost policy hk chores
    (enumerate p.anchor.active) (enumerate_injective _) p.buffer G hG tape
  refine ⟨tr,?_,?_,hq,hc⟩
  · simpa only [Pending.shrinkProgram,Pending.shrinkAttempt,Pending.shrinkResult,List.append_nil] using
      he.bind (fun result => .returned (p.finishShrink result)) (Executes.returned _ _)
  · unfold Pending.shrinkAttempt Pending.finishShrink
    split <;> exact hh

theorem shrinkAttempt_physical (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (whole : Set ℝ) (p : Pending n)
    [Nonempty (Fin p.anchor.active.card)] (hp : p.Physical μ whole)
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hk : 3 ≤ p.anchor.active.card) (chores : Bool)
    (hpositive : ∀ i, 0 < (μ (enumerate p.anchor.active i)).real (domain p.buffer.cells))
    (G : ℝ) (hG : 1 ≤ G)
    (hmax : G ≤ (2/RefinedUpperShrinkPrecision.theta n)*(8/RefinedUpperRepair.nearError n)^(p.anchor.active.card-1))
    (tape : RefinedUpperRepair.Tape n p.anchor.active.card) :
    (p.shrinkAttempt policy (by omega) chores G tape).Physical μ whole := by
  unfold Pending.shrinkAttempt Pending.finishShrink
  split
  · exact refreshShrink_physical μ whole p hp policy hpolicy hk chores hpositive G hG hmax tape
  · rename_i hf
    have ha : (p.shrinkResult policy (by omega) chores G tape).2.2=false := Bool.eq_false_iff.mpr hf
    exact acceptShrink_physical μ whole p hp policy hpolicy hk chores hpositive G hG hmax tape ha

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
