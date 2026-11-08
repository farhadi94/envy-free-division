import EnvyFreeResearch.Full.UpperGlobalOracleStabilityBasic
import EnvyFreeResearch.Full.UpperGlobalProtocolUnitRun

/-! The actual increasing finite prefixes have one consistent observable
next action at every tape and history. Returned live phases are deliberately
excluded: later prefixes continue their actual ordinary-query computation. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalOracleStability
open OracleProtocol Chores.QueryProgram UpperCircularStage UpperGlobalTape UpperGlobalPhysical
variable {n : ℕ}

def Terminal (phase : Phase n) : Prop := phase.finished=true

theorem step_absorbs_terminal (fallback : Fin n) (chores : Bool) (draw : Universal n)
    (phase : Phase n) (h : Terminal phase) :
    phase.stepProgram fallback chores draw=.returned phase := by
  cases phase <;> simp only [Terminal,Phase.finished,Bool.false_eq_true] at h
  rfl

theorem unitPrefixProgram_succ (fallback : Fin n) (chores : Bool)
    (omega : Stream (Universal n)) (t : ℕ) :
    unitPrefixProgram fallback chores omega (t+1)=
      (unitPrefixProgram fallback chores omega t).bind
        (fun phase => phase.stepProgram fallback chores (omega t)) := by
  unfold unitPrefixProgram
  change UpperGlobalUnit.program.bind
      (fun a => (prefixProgram fallback chores (.normalize a) omega t).bind
        (fun phase => phase.stepProgram fallback chores (omega t)))=_
  exact (bind_associative UpperGlobalUnit.program
    (fun a => prefixProgram fallback chores (.normalize a) omega t)
    (fun phase => phase.stepProgram fallback chores (omega t))).symm

theorem unitPrefix_action_succ (fallback : Fin n) (chores : Bool)
    (omega : Stream (Universal n)) (history : UpperCircularStage.History n) (t : ℕ)
    (hobs : Observable Terminal ((unitPrefixProgram fallback chores omega t).after history).action) :
    ((unitPrefixProgram fallback chores omega (t+1)).after history).action=
      ((unitPrefixProgram fallback chores omega t).after history).action := by
  rw [unitPrefixProgram_succ]
  exact after_bind_action_eq Terminal _ _ (step_absorbs_terminal fallback chores (omega t)) history hobs

theorem unitPrefix_action_stable (fallback : Fin n) (chores : Bool)
    (omega : Stream (Universal n)) (history : UpperCircularStage.History n) (t s : ℕ) (hts : t ≤ s)
    (hobs : Observable Terminal ((unitPrefixProgram fallback chores omega t).after history).action) :
    ((unitPrefixProgram fallback chores omega s).after history).action=
      ((unitPrefixProgram fallback chores omega t).after history).action := by
  induction s, hts using Nat.le_induction with
  | base => rfl
  | succ s hts ih =>
    have hs : Observable Terminal ((unitPrefixProgram fallback chores omega s).after history).action := by
      rw [ih]
      exact hobs
    exact (unitPrefix_action_succ fallback chores omega history s hs).trans ih

theorem unitPrefix_observable_actions_eq (fallback : Fin n) (chores : Bool)
    (omega : Stream (Universal n)) (history : UpperCircularStage.History n) (t s : ℕ)
    (ht : Observable Terminal ((unitPrefixProgram fallback chores omega t).after history).action)
    (hs : Observable Terminal ((unitPrefixProgram fallback chores omega s).after history).action) :
    ((unitPrefixProgram fallback chores omega s).after history).action=
      ((unitPrefixProgram fallback chores omega t).after history).action := by
  rcases le_total t s with h | h
  · exact unitPrefix_action_stable fallback chores omega history t s h ht
  · exact (unitPrefix_action_stable fallback chores omega history s t h hs).symm

end EnvyFreeResearch.Full.UpperGlobalOracleStability
