import EnvyFreeResearch.Full.ProtocolMeasurable
import EnvyFreeResearch.Full.AttemptedQueries
import EnvyFreeResearch.Full.MixedViews

/-! Geometric output validation can discard a malformed return without
altering any oracle call. This is an actual executor simulation. -/

namespace EnvyFreeResearch.Full.OutputPostprocess
open Set MeasureTheory OracleProtocol ProtocolMeasurable AttemptedQueries

variable {Tape Query Reply Raw Output : Type*}

def action (decode : Raw → Option Output) : Action Query Raw → Action Query Output
  | .ask q => .ask q
  | .returned r => match decode r with
    | some a => .returned a
    | none => .diverge
  | .diverge => .diverge

def stop (decode : Raw → Option Output) : Stop Query Raw → Stop Query Output
  | .returned r => match decode r with
    | some a => .returned a
    | none => .diverged
  | .diverged => .diverged
  | .illegal q => .illegal q
  | .exhausted q => .exhausted q

def execution (decode : Raw → Option Output) (e : Execution Query Reply Raw) :
    Execution Query Reply Output := ⟨e.answered,stop decode e.stop⟩

def normalized (decode : Raw → Option Output) (next : Protocol Tape Query Reply Raw) :
    Protocol Tape Query Reply Output := fun tape history => action decode (next tape history)

theorem run_normalized (decode : Raw → Option Output) (next : Protocol Tape Query Reply Raw)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ) (history : History Query Reply) :
    run (normalized decode next) oracle tape fuel history =
      execution decode (run next oracle tape fuel history) := by
  induction fuel generalizing history with
  | zero =>
    cases hn : next tape history with
    | ask q => simp [normalized,action,hn,execution,stop]
    | diverge => simp [normalized,action,hn,execution,stop]
    | returned r => cases hd : decode r <;> simp [normalized,action,hn,execution,stop,hd]
  | succ fuel ih =>
    cases hn : next tape history with
    | diverge => simp [normalized,action,hn,execution,stop]
    | returned r => cases hd : decode r <;> simp [normalized,action,hn,execution,stop,hd]
    | ask q =>
      cases ho : oracle q with
      | none => simp [normalized,action,hn,execution,stop,ho]
      | some r =>
        have hn' : normalized decode next tape history = .ask q := by simp [normalized,action,hn]
        rw [run_succ_some (normalized decode next) oracle tape fuel history q r hn' ho,
          run_succ_some next oracle tape fuel history q r hn ho, ih]
        rfl

theorem queryCost_normalized (decode : Raw → Option Output) (next : Protocol Tape Query Reply Raw)
    (oracle : Query → Option Reply) (tape : Tape) (history : History Query Reply) :
    queryCost (normalized decode next) oracle tape history = queryCost next oracle tape history := by
  unfold queryCost
  simp only [run_normalized,execution]

theorem attempts_execution (decode : Raw → Option Output) (e : Execution Query Reply Raw) :
    attempts (execution decode e) = attempts e := by
  cases hs : e.stop with
  | returned r => cases hd : decode r <;> simp [attempts,execution,stop,hs,hd]
  | diverged => simp [attempts,execution,stop,hs]
  | illegal q => simp [attempts,execution,stop,hs]
  | exhausted q => simp [attempts,execution,stop,hs]

theorem attemptedCost_normalized (decode : Raw → Option Output) (next : Protocol Tape Query Reply Raw)
    (oracle : Query → Option Reply) (tape : Tape) (history : History Query Reply) :
    attemptedCost (normalized decode next) oracle tape history = attemptedCost next oracle tape history := by
  unfold attemptedCost
  simp only [run_normalized,attempts_execution]

theorem returned_normalized_iff (decode : Raw → Option Output) (next : Protocol Tape Query Reply Raw)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ) (history : History Query Reply)
    (out : Output) :
    (run (normalized decode next) oracle tape fuel history).stop = .returned out ↔
      ∃ raw, (run next oracle tape fuel history).stop = .returned raw ∧ decode raw = some out := by
  rw [run_normalized]
  cases hs : (run next oracle tape fuel history).stop with
  | returned raw => cases hd : decode raw <;> simp [execution,stop,hs,hd]
  | diverged => simp [execution,stop,hs]
  | illegal q => simp [execution,stop,hs]
  | exhausted q => simp [execution,stop,hs]

theorem action_measurable [MeasurableSpace Query] [MeasurableSpace Raw] [MeasurableSpace Output]
    (decode : Raw → Option Output) (hd : Measurable decode) : Measurable (action (Query := Query) decode) := by
  have hr : Measurable (fun raw => match decode raw with
      | some a => Action.returned (Query := Query) a
      | none => Action.diverge) :=
    measurable_option_cases hd (measurable_action_returned.comp measurable_snd) measurable_const
  have hc : Measurable (fun _ : Unit => (Action.diverge : Action Query Output)) := measurable_const
  have h := measurable_action_ask.sumElim (hr.sumElim hc)
  convert h.comp (comap_measurable (actionCode (α := Query) (β := Raw))) using 1
  funext a
  cases a <;> rfl

theorem normalized_measurable [MeasurableSpace Tape] [MeasurableSpace Query]
    [MeasurableSpace Reply] [MeasurableSpace Raw] [MeasurableSpace Output]
    (decode : Raw → Option Output) (hd : Measurable decode)
    (next : Protocol Tape Query Reply Raw)
    (hn : Measurable (fun p : Tape × History Query Reply => next p.1 p.2)) :
    Measurable (fun p : Tape × History Query Reply => normalized decode next p.1 p.2) :=
  (action_measurable decode hd).comp hn

end EnvyFreeResearch.Full.OutputPostprocess
