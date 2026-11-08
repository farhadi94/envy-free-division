import EnvyFreeResearch.Full.UpperSnapshotRepetitionProgramTrace

/-! A successful candidate carries its originating state and random starts,
so later physical reconstruction is a pure computation on the returned data. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open OracleProtocol Chores.QueryProgram
variable {State Draw Query Reply Output : Type}

abbrev Packet (State Draw Output : Type) := State × Draw × Output

def packetStep (step : State → Draw → State × Option Output) (s : State) (d : Draw) :
    State × Option (Packet State Draw Output) :=
  ((step s d).1, (step s d).2.map (fun a => (s,d,a)))

def packetAttempt (attempt : State → Draw → Program Query Reply (State × Option Output))
    (s : State) (d : Draw) : Program Query Reply (State × Option (Packet State Draw Output)) :=
  (attempt s d).bind (fun r => .returned (r.1,r.2.map (fun a => (s,d,a))))

theorem packet_run_erasure (step : State → Draw → State × Option Output)
    (draws : List Draw) (s : State) :
    ((run (packetStep step) draws s).1,(run (packetStep step) draws s).2.map (fun p => p.2.2))=
      run step draws s := by
  induction draws generalizing s with
  | nil => rfl
  | cons d ds ih =>
    cases ho : (step s d).2 with
    | none => simpa only [run,packetStep,ho,Option.map_none] using ih (step s d).1
    | some a => simp only [run,packetStep,ho,Option.map_some]

theorem packet_run_none (step : State → Draw → State × Option Output)
    (draws : List Draw) (s : State) :
    (run (packetStep step) draws s).2=none ↔ (run step draws s).2=none := by
  have h := congrArg Prod.snd (packet_run_erasure step draws s)
  rw [← h]
  simp

theorem packet_run_state (step : State → Draw → State × Option Output)
    (draws : List Draw) (s : State) :
    (run (packetStep step) draws s).1=(run step draws s).1 :=
  congrArg Prod.fst (packet_run_erasure step draws s)

theorem packet_run_provenance (step : State → Draw → State × Option Output)
    (Inv : State → Prop) (hpreserve : ∀ s d, Inv s → Inv (step s d).1)
    (draws : List Draw) (s : State) (hs : Inv s) (p : Packet State Draw Output)
    (hp : (run (packetStep step) draws s).2=some p) :
    Inv p.1 ∧ step p.1 p.2.1=((run (packetStep step) draws s).1,some p.2.2) := by
  induction draws generalizing s with
  | nil => simp [run] at hp
  | cons d ds ih =>
    cases ho : (step s d).2 with
    | none =>
      have hh := ih (step s d).1 (hpreserve s d hs)
        (by simpa only [run,packetStep,ho,Option.map_none] using hp)
      simpa only [run,packetStep,ho,Option.map_none] using hh
    | some a =>
      have hpacket : (s,d,a)=p := by simpa only [run,packetStep,ho,Option.map_some,Option.some.injEq] using hp
      subst p
      refine ⟨hs,?_⟩
      apply Prod.ext
      · simp only [run,packetStep,ho,Option.map_some]
      · exact ho

theorem packet_attempt_executes (oracle : AdaptiveOracle.Policy Query Reply)
    (history : State → History Query Reply)
    (step : State → Draw → State × Option Output)
    (attempt : State → Draw → Program Query Reply (State × Option Output))
    (s : State) (d : Draw) (trace : History Query Reply)
    (he : Executes oracle (attempt s d) (history s) (step s d) trace) :
    Executes oracle (packetAttempt attempt s d) (history s) (packetStep step s d) trace := by
  have h := he.bind (fun r => Program.returned (r.1,r.2.map (fun a => (s,d,a))))
    (Executes.returned (oracle:=oracle) (packetStep step s d) (history s++trace))
  simpa only [packetAttempt,List.append_nil] using h

end EnvyFreeResearch.Full.UpperSnapshotRepetition
