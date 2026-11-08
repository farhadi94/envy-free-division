import EnvyFreeResearch.Full.UpperSnapshotRepetitionProgram

noncomputable section
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open OracleProtocol Chores.QueryProgram
variable {State Draw Query Reply Output : Type}

theorem program_executes_trace_invariant
    (oracle : AdaptiveOracle.Policy Query Reply)
    (history : State → History Query Reply)
    (step : State → Draw → State × Option Output)
    (attempt : State → Draw → Program Query Reply (State × Option Output))
    (cut : Query → Bool) (Q C : ℕ)
    (TraceGood : Query × Reply → Prop) (Inv : State → Prop) (hpreserve : ∀ s d, Inv s → Inv (step s d).1)
    (hstep : ∀ s d, Inv s → ∃ trace,
      Executes oracle (attempt s d) (history s) (step s d) trace ∧
      history (step s d).1=history s++trace ∧
      trace.length ≤ Q ∧ (trace.map Prod.fst).countP cut ≤ C ∧ ∀ e ∈ trace, TraceGood e)
    (draws : List Draw) (s : State) (hs : Inv s) :
    ∃ trace, Executes oracle (program attempt draws s) (history s) (run step draws s) trace ∧
      history (run step draws s).1=history s++trace ∧
      trace.length ≤ draws.length*Q ∧ (trace.map Prod.fst).countP cut ≤ draws.length*C ∧ ∀ e ∈ trace, TraceGood e := by
  induction draws generalizing s with
  | nil => exact ⟨[],Executes.returned _ _,by simp [run],by simp,by simp,by simp⟩
  | cons d ds ih =>
    obtain ⟨first,he,hh,hq,hc,hl⟩ := hstep s d hs
    cases ho : (step s d).2 with
    | some a =>
      refine ⟨first,?_,?_,?_,?_,hl⟩
      · have hp := he.bind (fun r => match r.2 with
          | some a => Program.returned (r.1,some a)
          | none => program attempt ds r.1)
          (by simpa only [ho] using (Executes.returned (oracle := oracle) ((step s d).1,some a) (history s++first)))
        simp only [program,run,ho,List.append_nil] at hp ⊢
        exact hp
      · simpa only [run,ho] using hh
      · simp only [List.length_cons]; nlinarith
      · simp only [List.length_cons]; nlinarith
    | none =>
      obtain ⟨rest,her,hhr,hqr,hcr,hlr⟩ := ih (step s d).1 (hpreserve s d hs)
      refine ⟨first++rest,?_,?_,?_,?_,?_⟩
      · have hp := he.bind (fun r => match r.2 with
          | some a => Program.returned (r.1,some a)
          | none => program attempt ds r.1)
          (by simpa only [ho,hh] using her)
        simp only [program,run,ho] at hp ⊢
        exact hp
      · simpa only [run,ho,hh,List.append_assoc] using hhr
      · simp only [List.length_append,List.length_cons]; nlinarith
      · simp only [List.map_append,List.countP_append,List.length_cons]; nlinarith

      · intro e hm
        rcases List.mem_append.mp hm with he | he
        · exact hl e he
        · exact hlr e he

end EnvyFreeResearch.Full.UpperSnapshotRepetition
