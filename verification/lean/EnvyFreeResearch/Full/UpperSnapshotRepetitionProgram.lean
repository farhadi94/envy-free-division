import EnvyFreeResearch.Full.ChoresProgram

/-! First-accepting finite query program. Rejected outputs retain the full
state and history; every attempted query is included in the final trace. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open OracleProtocol Chores.QueryProgram
variable {State Draw Query Reply Output : Type}

def run (step : State → Draw → State × Option Output) :
    List Draw → State → State × Option Output
  | [], s => (s,none)
  | d::ds, s =>
    let r := step s d
    match r.2 with
    | some a => (r.1,some a)
    | none => run step ds r.1

def program (attempt : State → Draw → Program Query Reply (State × Option Output)) :
    List Draw → State → Program Query Reply (State × Option Output)
  | [], s => .returned (s,none)
  | d::ds, s => (attempt s d).bind fun r =>
    match r.2 with
    | some a => .returned (r.1,some a)
    | none => program attempt ds r.1

theorem program_executes
    (oracle : AdaptiveOracle.Policy Query Reply)
    (history : State → History Query Reply)
    (step : State → Draw → State × Option Output)
    (attempt : State → Draw → Program Query Reply (State × Option Output))
    (cut : Query → Bool) (Q C : ℕ)
    (hstep : ∀ s d, ∃ trace,
      Executes oracle (attempt s d) (history s) (step s d) trace ∧
      history (step s d).1=history s++trace ∧
      trace.length ≤ Q ∧ (trace.map Prod.fst).countP cut ≤ C)
    (draws : List Draw) (s : State) :
    ∃ trace, Executes oracle (program attempt draws s) (history s) (run step draws s) trace ∧
      history (run step draws s).1=history s++trace ∧
      trace.length ≤ draws.length*Q ∧ (trace.map Prod.fst).countP cut ≤ draws.length*C := by
  induction draws generalizing s with
  | nil => exact ⟨[],Executes.returned _ _,by simp [run],by simp,by simp⟩
  | cons d ds ih =>
    obtain ⟨first,he,hh,hq,hc⟩ := hstep s d
    cases ho : (step s d).2 with
    | some a =>
      refine ⟨first,?_,?_,?_,?_⟩
      · have hp := he.bind (fun r => match r.2 with
          | some a => Program.returned (r.1,some a)
          | none => program attempt ds r.1)
          (by simpa only [ho] using (Executes.returned (oracle := oracle) ((step s d).1,some a) (history s++first)))
        simpa only [program,run,ho,List.append_nil] using hp
      · simpa only [run,ho] using hh
      · simp only [List.length_cons]; nlinarith
      · simp only [List.length_cons]; nlinarith
    | none =>
      obtain ⟨rest,her,hhr,hqr,hcr⟩ := ih (step s d).1
      refine ⟨first++rest,?_,?_,?_,?_⟩
      · have hp := he.bind (fun r => match r.2 with
          | some a => Program.returned (r.1,some a)
          | none => program attempt ds r.1)
          (by simpa only [ho,hh] using her)
        simpa only [program,run,ho] using hp
      · simpa only [run,ho,hh,List.append_assoc] using hhr
      · simp only [List.length_append,List.length_cons]; nlinarith
      · simp only [List.map_append,List.countP_append,List.length_cons]; nlinarith

theorem run_preserves (step : State → Draw → State × Option Output)
    (Inv : State → Prop) (hstep : ∀ s d, Inv s → Inv (step s d).1)
    (draws : List Draw) (s : State) (hs : Inv s) : Inv (run step draws s).1 := by
  induction draws generalizing s with
  | nil => exact hs
  | cons d ds ih =>
    have hn := hstep s d hs
    cases ho : (step s d).2 with
    | some a => simpa only [run,ho] using hn
    | none => simpa only [run,ho] using ih (step s d).1 hn

theorem run_accepted (step : State → Draw → State × Option Output)
    (Valid : Output → Prop)
    (hstep : ∀ s d a, (step s d).2=some a → Valid a)
    (draws : List Draw) (s : State) (a : Output)
    (ha : (run step draws s).2=some a) : Valid a := by
  induction draws generalizing s with
  | nil => simp [run] at ha
  | cons d ds ih =>
    cases ho : (step s d).2 with
    | some b =>
      have hab : b=a := by simpa only [run,ho,Option.some.injEq] using ha
      subst b
      exact hstep s d a ho
    | none => exact ih (step s d).1 (by simpa only [run,ho] using ha)

end EnvyFreeResearch.Full.UpperSnapshotRepetition
