import EnvyFreeResearch.Full.IntervalOracle

/-!
# Execution with history-dependent ordinary oracle replies

This extends the execution semantics without changing `OracleProtocol`.
The oracle receives the complete answered history before each call, so repeated
Cut queries may receive different legal roots. Returns after the last allowed
answer are observed before a further ask exhausts the fuel budget.
-/

namespace EnvyFreeResearch.Full.AdaptiveOracle

open OracleProtocol

universe u v w t

abbrev Policy (Query : Type u) (Reply : Type v) := History Query Reply → Query → Option Reply

variable {Tape : Type t} {Query : Type u} {Reply : Type v} {Output : Type w}

def run (next : Protocol Tape Query Reply Output) (oracle : Policy Query Reply)
    (tape : Tape) : ℕ → History Query Reply → Execution Query Reply Output
  | fuel, history =>
    match next tape history with
    | .returned output => ⟨[], .returned output⟩
    | .diverge => ⟨[], .diverged⟩
    | .ask query =>
      match fuel with
      | 0 => ⟨[], .exhausted query⟩
      | fuel + 1 =>
        match oracle history query with
        | none => ⟨[], .illegal query⟩
        | some reply =>
          let tail := run next oracle tape fuel (history ++ [(query, reply)])
          ⟨(query, reply) :: tail.answered, tail.stop⟩

@[simp] theorem run_returned (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (output : Output)
    (h : next tape history = .returned output) :
    run next oracle tape fuel history = ⟨[], .returned output⟩ := by
  rw [run, h]

@[simp] theorem run_diverge (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (h : next tape history = .diverge) :
    run next oracle tape fuel history = ⟨[], .diverged⟩ := by
  rw [run, h]

@[simp] theorem run_zero_ask (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape)
    (history : History Query Reply) (query : Query) (h : next tape history = .ask query) :
    run next oracle tape 0 history = ⟨[], .exhausted query⟩ := by
  rw [run, h]

@[simp] theorem run_succ_none (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (query : Query)
    (h : next tape history = .ask query) (ho : oracle history query = none) :
    run next oracle tape (fuel + 1) history = ⟨[], .illegal query⟩ := by
  rw [run, h]
  simp only [ho]

@[simp] theorem run_succ_some (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (query : Query) (reply : Reply)
    (h : next tape history = .ask query) (ho : oracle history query = some reply) :
    run next oracle tape (fuel + 1) history =
      ⟨(query, reply) :: (run next oracle tape fuel (history ++ [(query, reply)])).answered,
        (run next oracle tape fuel (history ++ [(query, reply)])).stop⟩ := by
  rw [run, h]
  simp only [ho]

theorem answered_length_le (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) :
    (run next oracle tape fuel history).answered.length ≤ fuel := by
  induction fuel generalizing history with
  | zero => cases h : next tape history <;> simp [h]
  | succ fuel ih =>
    cases h : next tape history with
    | returned output => simp [h]
    | diverge => simp [h]
    | ask query =>
      cases ho : oracle history query with
      | none => simp [h, ho]
      | some reply =>
        simpa [h, ho] using Nat.succ_le_succ (ih (history ++ [(query, reply)]))

/-- A history-independent selector embeds faithfully into the extended model. -/
theorem fixed_policy_agrees (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) :
    run next (fun _ => oracle) tape fuel history =
      OracleProtocol.run next oracle tape fuel history := by
  induction fuel generalizing history with
  | zero => cases h : next tape history <;> simp [h]
  | succ fuel ih =>
    cases h : next tape history with
    | returned output => simp [h]
    | diverge => simp [h]
    | ask query =>
      cases ho : oracle query with
      | none => simp [h, ho]
      | some reply => simp [h, ho, ih]

section OrdinaryIntervals

open IntervalOracle

/-- At every finite history, the policy must answer every legal ordinary
query and may return only legal answers. Repeated roots need not agree. -/
def IsLegalPolicy {Agent : Type*} (P : Profile Agent)
    (oracle : Policy (IntervalOracle.Query Agent) ℝ) : Prop :=
  ∀ history, IsLegalOracle P (oracle history)

theorem fixed_isLegalPolicy {Agent : Type*} (P : Profile Agent)
    (oracle : IntervalOracle.Query Agent → Option ℝ) (h : IsLegalOracle P oracle) :
    IsLegalPolicy P (fun _ => oracle) := fun _ => h

/-- On legal requests a complete policy has an actual real answer, so a total
stage executor can use this adapter without changing any oracle response. -/
def answer {Agent : Type*} (oracle : Policy (IntervalOracle.Query Agent) ℝ)
    (history : History (IntervalOracle.Query Agent) ℝ) (query : IntervalOracle.Query Agent) : ℝ :=
  (oracle history query).getD 0

theorem answer_spec {Agent : Type*} (P : Profile Agent)
    (oracle : Policy (IntervalOracle.Query Agent) ℝ) (h : IsLegalPolicy P oracle)
    (history : History (IntervalOracle.Query Agent) ℝ) (query : IntervalOracle.Query Agent)
    (hquery : Legal P query) :
    oracle history query = some (answer oracle history query) ∧
      ValidReply P query (answer oracle history query) := by
  obtain ⟨reply, hreply⟩ := (h history).complete query hquery
  have heq : answer oracle history query = reply := by simp [answer, hreply]
  rw [heq]
  exact ⟨hreply, ((h history).sound query reply hreply).2⟩

end OrdinaryIntervals

end EnvyFreeResearch.Full.AdaptiveOracle
