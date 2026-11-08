import EnvyFreeResearch.Full.UpperGlobalRunProgramCertifiedPrefix
import EnvyFreeResearch.Full.UpperGlobalRunTerminationMeasurable

/-! A single global next-action protocol. Intermediate phase returns are internal
computations; the first query, divergence, or completed allocation is observable. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperGlobalRun.OracleNext
open UpperGlobalPhysical UpperGlobalTape UpperCircularStage UpperQueryPrograms
  Chores.QueryProgram OracleProtocol ProtocolMeasurable
variable {n : ℕ}

def observable : Action (Query n) (Phase n) → Bool
  | .ask _ => true
  | .returned p => p.finished
  | .diverge => true

def prefixAction (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n))
    (history : UpperCircularStage.History n) (t : ℕ) : Action (Query n) (Phase n) :=
  ((unitPrefixProgram fallback chores omega t).after history).action

def next (fallback : Fin n) (chores : Bool) :
    Protocol (Stream (Universal n)) (Query n) ℝ (Phase n) := fun omega history =>
  if h : ∃ t, observable (prefixAction fallback chores omega history t) = true then
    prefixAction fallback chores omega history (Nat.find h)
  else .diverge

theorem next_eq_find (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n))
    (history : UpperCircularStage.History n)
    (h : ∃ t, observable (prefixAction fallback chores omega history t) = true) :
    next fallback chores omega history = prefixAction fallback chores omega history (Nat.find h) := by
  simp only [next,dite_eq_left h]

theorem next_eq_of_observable (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n))
    (history : UpperCircularStage.History n) (t : ℕ)
    (h : observable (prefixAction fallback chores omega history t) = true)
    (hsame : ∀ s, observable (prefixAction fallback chores omega history s) = true →
      prefixAction fallback chores omega history s = prefixAction fallback chores omega history t) :
    next fallback chores omega history = prefixAction fallback chores omega history t := by
  have hex : ∃ s, observable (prefixAction fallback chores omega history s) = true := ⟨t,h⟩
  rw [next_eq_find fallback chores omega history hex]
  exact hsame _ (Nat.find_spec hex)

theorem next_eq_diverge_of_none (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n))
    (history : UpperCircularStage.History n)
    (h : ¬ ∃ t, observable (prefixAction fallback chores omega history t) = true) :
    next fallback chores omega history = .diverge := by simp only [next,dite_eq_right h]

theorem next_observable (fallback : Fin n) (chores : Bool) (omega : Stream (Universal n))
    (history : UpperCircularStage.History n) : observable (next fallback chores omega history) = true := by
  unfold next
  split
  next h => exact Nat.find_spec h
  · rfl

theorem observable_measurable : Measurable (observable (n:=n)) := by
  have hm := ((measurable_const : Measurable (fun _ : Query n => true)).sumElim
    (phase_finished_measurable.sumElim (measurable_const : Measurable (fun _ : Unit => true)))).comp
    (measurable_actionCode (α:=Query n) (β:=Phase n))
  convert hm using 1
  funext a
  cases a <;> rfl

theorem prefixAction_measurable (fallback : Fin n) (chores : Bool) (t : ℕ) :
    Measurable (fun z : Stream (Universal n) × UpperCircularStage.History n =>
      prefixAction fallback chores z.1 z.2 t) :=
  ProgramCertified.unitPrefixProgram_next_measurable fallback chores id measurable_id t

end EnvyFreeResearch.Full.UpperGlobalRun.OracleNext
