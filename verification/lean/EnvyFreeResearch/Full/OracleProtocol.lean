import Mathlib

/-!
# Actual adaptive oracle execution and all-outcome replay

The protocol is a next-action function of the complete fixed tape and the
finite answered history. `diverge` represents query-free nonreturn; deciding
that case is not required to be computable. `none` is a terminal illegal oracle
request. An allowed unavailable-target *reply* instead belongs to `Reply` and
is returned as `some reply`, so it is counted.

The fuel cap is checked only on an `ask`: returns and query-free divergence
after the final allowed answer are retained. A terminal illegal call after
`q` answers is exposed using fuel `q + 1` and is never counted as an answer.

Replay below is derived from the recursive execution, not imposed as a
protocol field. Measurability and concrete interval-oracle semantics are
separate obligations.
-/

namespace EnvyFreeResearch.Full.OracleProtocol

universe u v w t

inductive Action (Query : Type u) (Output : Type w)
  | ask (query : Query)
  | returned (output : Output)
  | diverge
  deriving DecidableEq

inductive Stop (Query : Type u) (Output : Type w)
  | returned (output : Output)
  | diverged
  | illegal (query : Query)
  | exhausted (query : Query)
  deriving DecidableEq

structure Execution (Query : Type u) (Reply : Type v) (Output : Type w) where
  answered : List (Query × Reply)
  stop : Stop Query Output
  deriving DecidableEq

abbrev History (Query : Type u) (Reply : Type v) := List (Query × Reply)

abbrev Protocol (Tape : Type t) (Query : Type u) (Reply : Type v) (Output : Type w) :=
  Tape → History Query Reply → Action Query Output

variable {Tape : Type t} {Query : Type u} {Reply : Type v} {Output : Type w}

/-- The returned history is the suffix of answers made during this call. -/
def run (next : Protocol Tape Query Reply Output) (oracle : Query → Option Reply)
    (tape : Tape) : ℕ → History Query Reply → Execution Query Reply Output
  | fuel, history =>
    match next tape history with
    | .returned output => ⟨[], .returned output⟩
    | .diverge => ⟨[], .diverged⟩
    | .ask query =>
      match fuel with
      | 0 => ⟨[], .exhausted query⟩
      | fuel + 1 =>
        match oracle query with
        | none => ⟨[], .illegal query⟩
        | some reply =>
          let tail := run next oracle tape fuel (history ++ [(query, reply)])
          ⟨(query, reply) :: tail.answered, tail.stop⟩

@[simp] theorem run_returned (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (output : Output)
    (h : next tape history = .returned output) :
    run next oracle tape fuel history = ⟨[], .returned output⟩ := by
  rw [run, h]

@[simp] theorem run_diverge (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (h : next tape history = .diverge) :
    run next oracle tape fuel history = ⟨[], .diverged⟩ := by
  rw [run, h]

@[simp] theorem run_zero_ask (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape)
    (history : History Query Reply) (query : Query) (h : next tape history = .ask query) :
    run next oracle tape 0 history = ⟨[], .exhausted query⟩ := by
  rw [run, h]

@[simp] theorem run_succ_none (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (query : Query)
    (h : next tape history = .ask query) (ho : oracle query = none) :
    run next oracle tape (fuel + 1) history = ⟨[], .illegal query⟩ := by
  rw [run, h]
  simp only [ho]

@[simp] theorem run_succ_some (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (query : Query) (reply : Reply)
    (h : next tape history = .ask query) (ho : oracle query = some reply) :
    run next oracle tape (fuel + 1) history =
      ⟨(query, reply) :: (run next oracle tape fuel (history ++ [(query, reply)])).answered,
        (run next oracle tape fuel (history ++ [(query, reply)])).stop⟩ := by
  rw [run, h]
  simp only [ho]

/-- Preserving every actually answered reply and the possible terminal illegal
request suffices to preserve the entire adaptive execution. There is no
condition on unasked queries, or on the request at an exhausted cap. -/
theorem replay (next : Protocol Tape Query Reply Output)
    (before after : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply)
    (hanswers : ∀ query reply,
      (query, reply) ∈ (run next before tape fuel history).answered →
        after query = some reply)
    (hillegal : ∀ query,
      (run next before tape fuel history).stop = .illegal query → after query = none) :
    run next after tape fuel history = run next before tape fuel history := by
  induction fuel generalizing history with
  | zero =>
    cases hnext : next tape history <;> simp [hnext]
  | succ fuel ih =>
    cases hnext : next tape history with
    | returned output => simp [hnext]
    | diverge => simp [hnext]
    | ask query =>
      cases horacle : before query with
      | none =>
        have hafter := hillegal query (by simp [hnext, horacle])
        simp [hnext, horacle, hafter]
      | some reply =>
        have hafter := hanswers query reply (by simp [hnext, horacle])
        have htail := ih (history ++ [(query, reply)])
          (fun q r h => hanswers q r (by simp [hnext, horacle, h]))
          (fun q h => hillegal q (by simpa [hnext, horacle] using h))
        simp [hnext, horacle, hafter, htail]

theorem answers_sound (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (query : Query) (reply : Reply)
    (hmem : (query, reply) ∈ (run next oracle tape fuel history).answered) :
    oracle query = some reply := by
  induction fuel generalizing history with
  | zero =>
    cases hnext : next tape history <;> simp [hnext] at hmem
  | succ fuel ih =>
    cases hnext : next tape history with
    | returned output => simp [hnext] at hmem
    | diverge => simp [hnext] at hmem
    | ask q =>
      cases ho : oracle q with
      | none => simp [hnext, ho] at hmem
      | some r =>
        simp only [run_succ_some _ _ _ _ _ _ _ hnext ho,
          List.mem_cons, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | hmem
        · exact ho
        · exact ih _ hmem

theorem illegal_sound (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (query : Query)
    (hstop : (run next oracle tape fuel history).stop = .illegal query) :
    oracle query = none := by
  induction fuel generalizing history with
  | zero =>
    cases hnext : next tape history <;> simp [hnext] at hstop
  | succ fuel ih =>
    cases hnext : next tape history with
    | returned output => simp [hnext] at hstop
    | diverge => simp [hnext] at hstop
    | ask q =>
      cases ho : oracle q with
      | none =>
        have hq : q = query := by simpa [hnext, ho] using hstop
        simpa [hq] using ho
      | some r =>
        exact ih _ (by simpa [hnext, ho] using hstop)

/-- This equality-of-oracles version chooses all requests from the baseline
execution, never by conditioning an adaptive next query on nondetection. -/
theorem replay_of_oracle_eq (next : Protocol Tape Query Reply Output)
    (before after : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply)
    (hpreserve : ∀ query,
      (∃ reply, (query, reply) ∈ (run next before tape fuel history).answered) ∨
        (run next before tape fuel history).stop = .illegal query →
      after query = before query) :
    run next after tape fuel history = run next before tape fuel history := by
  apply replay
  · intro query reply hmem
    rw [hpreserve query (Or.inl ⟨reply, hmem⟩)]
    exact answers_sound next before tape fuel history query reply hmem
  · intro query hstop
    rw [hpreserve query (Or.inr hstop)]
    exact illegal_sound next before tape fuel history query hstop

theorem answered_length_le (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) :
    (run next oracle tape fuel history).answered.length ≤ fuel := by
  induction fuel generalizing history with
  | zero =>
    cases hnext : next tape history <;> simp [hnext]
  | succ fuel ih =>
    cases hnext : next tape history with
    | returned output => simp [hnext]
    | diverge => simp [hnext]
    | ask query =>
      cases ho : oracle query with
      | none => simp [hnext, ho]
      | some reply =>
        simpa [hnext, ho] using Nat.succ_le_succ (ih (history ++ [(query, reply)]))

/-- Every stop except the fuel cap is a genuine all-outcome terminal behavior. -/
def Terminal (stop : Stop Query Output) : Prop := ∀ query, stop ≠ .exhausted query

/-- Increasing the cap after a genuine return, illegal call, or query-free
divergence leaves the entire execution unchanged. -/
theorem run_add_of_terminal (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel extra : ℕ)
    (history : History Query Reply)
    (hterminal : Terminal (run next oracle tape fuel history).stop) :
    run next oracle tape (fuel + extra) history = run next oracle tape fuel history := by
  induction fuel generalizing history with
  | zero =>
    cases hnext : next tape history with
    | returned output => simp [hnext]
    | diverge => simp [hnext]
    | ask query =>
      exact False.elim (hterminal query (by simp [hnext]))
  | succ fuel ih =>
    cases hnext : next tape history with
    | returned output => simp [hnext]
    | diverge => simp [hnext]
    | ask query =>
      have harith : fuel + 1 + extra = fuel + extra + 1 := by omega
      rw [harith]
      cases ho : oracle query with
      | none => simp [hnext, ho]
      | some reply =>
        have htail : Terminal
            (run next oracle tape fuel (history ++ [(query, reply)])).stop := by
          simpa [hnext, ho] using hterminal
        simp [hnext, ho, ih _ htail]

theorem run_eq_of_terminal_of_le (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (small large : ℕ)
    (history : History Query Reply) (hle : small ≤ large)
    (hterminal : Terminal (run next oracle tape small history).stop) :
    run next oracle tape large history = run next oracle tape small history := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact run_add_of_terminal next oracle tape small extra history hterminal

theorem answered_length_mono (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (history : History Query Reply) :
    Monotone (fun fuel => (run next oracle tape fuel history).answered.length) := by
  apply monotone_nat_of_le_succ
  intro fuel
  induction fuel generalizing history with
  | zero =>
    cases hnext : next tape history <;> simp [hnext]
  | succ fuel ih =>
    cases hnext : next tape history with
    | returned output => simp [hnext]
    | diverge => simp [hnext]
    | ask query =>
      cases ho : oracle query with
      | none => simp [hnext, ho]
      | some reply =>
        simpa [hnext, ho] using Nat.succ_le_succ (ih (history ++ [(query, reply)]))

/-- An exhausted cap has supplied precisely its allowed number of answers. -/
theorem answered_length_of_exhausted (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (query : Query)
    (hstop : (run next oracle tape fuel history).stop = .exhausted query) :
    (run next oracle tape fuel history).answered.length = fuel := by
  induction fuel generalizing history with
  | zero => exact Nat.eq_zero_of_le_zero (answered_length_le next oracle tape 0 history)
  | succ fuel ih =>
    cases hnext : next tape history with
    | returned output => simp [hnext] at hstop
    | diverge => simp [hnext] at hstop
    | ask q =>
      cases ho : oracle q with
      | none => simp [hnext, ho] at hstop
      | some reply =>
        have htail := ih (history ++ [(q, reply)]) (by simpa [hnext, ho] using hstop)
        simp [hnext, ho, htail]

/-- Unconditional answered-query cost, including infinite querying. -/
noncomputable def queryCost (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (history : History Query Reply) : ℕ∞ :=
  ⨆ fuel : ℕ, ((run next oracle tape fuel history).answered.length : ℕ∞)

theorem queryCost_of_terminal (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply)
    (hterminal : Terminal (run next oracle tape fuel history).stop) :
    queryCost next oracle tape history =
      ((run next oracle tape fuel history).answered.length : ℕ∞) := by
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hle : k ≤ fuel
    · exact_mod_cast answered_length_mono next oracle tape history hle
    · have heq := run_eq_of_terminal_of_le next oracle tape fuel k history
        (le_of_not_ge hle) hterminal
      rw [heq]
  · exact le_iSup (fun k : ℕ => ((run next oracle tape k history).answered.length : ℕ∞)) fuel

/-- A finite answered-query cost has an actual terminal behavior at some
finite cap. In particular, finite-query divergence is represented explicitly,
whereas an endless sequence of asks has infinite cost. -/
theorem exists_terminal_of_queryCost_ne_top (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (history : History Query Reply)
    (hfinite : queryCost next oracle tape history ≠ ⊤) :
    ∃ fuel, Terminal (run next oracle tape fuel history).stop := by
  by_contra hnone
  have hexhausted : ∀ fuel, ∃ query,
      (run next oracle tape fuel history).stop = .exhausted query := by
    simpa only [not_exists, Terminal, not_forall, not_not] using hnone
  have hcost : queryCost next oracle tape history = ⊤ := by
    apply top_unique
    calc
      (⊤ : ℕ∞) = ⨆ fuel : ℕ, (fuel : ℕ∞) := ENat.iSup_natCast.symm
      _ ≤ queryCost next oracle tape history := by
        apply iSup_le
        intro fuel
        obtain ⟨query, hquery⟩ := hexhausted fuel
        have hlen := answered_length_of_exhausted next oracle tape fuel history query hquery
        rw [← hlen]
        exact le_iSup (fun k : ℕ => ((run next oracle tape k history).answered.length : ℕ∞)) fuel
  exact hfinite hcost

/-- Resume only a cap-exhausted execution. Genuine terminal outcomes remain
unchanged. The resumed call receives the actual accumulated answered history. -/
def resume (next : Protocol Tape Query Reply Output) (oracle : Query → Option Reply)
    (tape : Tape) (extra : ℕ) (history : History Query Reply)
    (initial : Execution Query Reply Output) : Execution Query Reply Output :=
  match initial.stop with
  | .exhausted _ =>
    let suffix := run next oracle tape extra (history ++ initial.answered)
    ⟨initial.answered ++ suffix.answered, suffix.stop⟩
  | _ => initial

private theorem resume_cons (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (extra : ℕ)
    (history : History Query Reply) (query : Query) (reply : Reply)
    (tail : Execution Query Reply Output) :
    resume next oracle tape extra history ⟨(query, reply) :: tail.answered, tail.stop⟩ =
      ⟨(query, reply) :: (resume next oracle tape extra
          (history ++ [(query, reply)]) tail).answered,
        (resume next oracle tape extra (history ++ [(query, reply)]) tail).stop⟩ := by
  cases tail with
  | mk answered stop =>
    cases stop <;> simp [resume, List.append_assoc]

/-- Exact adaptive run splitting. This exposes the next request after a
frozen prefix without assuming the request is independent of earlier answers. -/
theorem run_add_eq_resume (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel extra : ℕ)
    (history : History Query Reply) :
    run next oracle tape (fuel + extra) history =
      resume next oracle tape extra history (run next oracle tape fuel history) := by
  induction fuel generalizing history with
  | zero =>
    cases hnext : next tape history <;> simp [hnext, resume]
  | succ fuel ih =>
    cases hnext : next tape history with
    | returned output => simp [hnext, resume]
    | diverge => simp [hnext, resume]
    | ask query =>
      have harith : fuel + 1 + extra = fuel + extra + 1 := by omega
      rw [harith]
      cases ho : oracle query with
      | none => simp [hnext, ho, resume]
      | some reply =>
        rw [run_succ_some _ _ _ _ _ _ _ hnext ho,
          run_succ_some _ _ _ _ _ _ _ hnext ho, resume_cons, ih]

/-- A genuine return is visible at exactly its answered-query count, since
the cap does not suppress query-free output after the last permitted answer. -/
theorem run_answered_length_of_returned (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (output : Output)
    (hreturned : (run next oracle tape fuel history).stop = .returned output) :
    run next oracle tape (run next oracle tape fuel history).answered.length history =
      run next oracle tape fuel history := by
  induction fuel generalizing history with
  | zero =>
    cases hnext : next tape history <;> simp [hnext] at hreturned ⊢
  | succ fuel ih =>
    cases hnext : next tape history with
    | returned result => simp [hnext]
    | diverge => simp [hnext] at hreturned
    | ask query =>
      cases ho : oracle query with
      | none => simp [hnext, ho] at hreturned
      | some reply =>
        have htail : (run next oracle tape fuel (history ++ [(query, reply)])).stop = .returned output := by
          simpa [hnext, ho] using hreturned
        have hsame := ih (history ++ [(query, reply)]) htail
        simp [hnext, ho, hsame]

/-- At most one additional determining request is needed for terminal
illegality. It does not enter the count of answered calls. -/
def determiningRequests (execution : Execution Query Reply Output) : List Query :=
  execution.answered.map Prod.fst ++
    match execution.stop with
    | .illegal query => [query]
    | _ => []

def illegalIndicator (execution : Execution Query Reply Output) : ℕ :=
  match execution.stop with
  | .illegal _ => 1
  | _ => 0

theorem determiningRequests_length (execution : Execution Query Reply Output) :
    (determiningRequests execution).length =
      execution.answered.length + illegalIndicator execution := by
  cases execution with
  | mk answered stop => cases stop <;> simp [determiningRequests, illegalIndicator]

theorem illegalIndicator_eq_zero_of_returned (execution : Execution Query Reply Output)
    (output : Output) (h : execution.stop = .returned output) :
    illegalIndicator execution = 0 := by
  simp [illegalIndicator, h]

end EnvyFreeResearch.Full.OracleProtocol

#print axioms EnvyFreeResearch.Full.OracleProtocol.replay
#print axioms EnvyFreeResearch.Full.OracleProtocol.replay_of_oracle_eq
#print axioms EnvyFreeResearch.Full.OracleProtocol.answered_length_le
#print axioms EnvyFreeResearch.Full.OracleProtocol.determiningRequests_length
#print axioms EnvyFreeResearch.Full.OracleProtocol.queryCost_of_terminal
#print axioms EnvyFreeResearch.Full.OracleProtocol.exists_terminal_of_queryCost_ne_top
#print axioms EnvyFreeResearch.Full.OracleProtocol.run_add_eq_resume
#print axioms EnvyFreeResearch.Full.OracleProtocol.run_answered_length_of_returned
