import EnvyFreeResearch.Full.ChoresRecordSearch

/-!
# Composing physical query programs without losing their actual trace

The finite query-program type has ordinary asks, pure returns, and an explicit
failure branch. Its compiler is a fixed next-action function on the complete
answered history. The execution relation records actual policy replies, and
composition appends complete traces. No valuation or fairness conclusion is
part of this interface.
-/

namespace EnvyFreeResearch.Full.Chores.QueryProgram

open OracleProtocol

inductive Program (Query Reply Output : Type*)
  | returned (value : Output)
  | ask (query : Query) (next : Reply → Program Query Reply Output)
  | failed

variable {Query Reply A B Tape : Type*}

def Program.bind (p : Program Query Reply A) (f : A → Program Query Reply B) : Program Query Reply B :=
  match p with
  | .returned a => f a
  | .ask q k => .ask q (fun r => (k r).bind f)
  | .failed => .failed

def Program.action : Program Query Reply A → Action Query A
  | .returned a => .returned a
  | .ask q _ => .ask q
  | .failed => .diverge

/-- Replay reads answers already in the supplied history; new asks are still
answered only by the actual full-history policy. -/
def Program.after (p : Program Query Reply A) : History Query Reply → Program Query Reply A
  | [] => p
  | (_, r) :: rest => match p with
    | .ask _ k => (k r).after rest
    | .returned a => .returned a
    | .failed => .failed

lemma Program.after_append (p : Program Query Reply A) (xs ys : History Query Reply) :
    p.after (xs ++ ys) = (p.after xs).after ys := by
  induction xs generalizing p with
  | nil => simp [Program.after]
  | cons x xs ih =>
    cases p with
    | returned a => cases ys <;> rfl
    | failed => cases ys <;> rfl
    | ask q k => exact ih (k x.2)

def Program.protocol (p : Program Query Reply A) : Protocol Unit Query Reply A :=
  fun _ history => (p.after history).action

/-- Every ask in this derivation has an actual response from the policy at the
precise full history preceding it. -/
inductive Executes (oracle : AdaptiveOracle.Policy Query Reply) :
    Program Query Reply A → History Query Reply → A → History Query Reply → Prop
  | returned (a : A) (history : History Query Reply) : Executes oracle (.returned a) history a []
  | ask (q : Query) (k : Reply → Program Query Reply A) (history : History Query Reply)
      (reply : Reply) (a : A) (tail : History Query Reply)
      (hreply : oracle history q = some reply)
      (hnext : Executes oracle (k reply) (history ++ [(q, reply)]) a tail) :
      Executes oracle (.ask q k) history a ((q, reply) :: tail)

/-- Program composition preserves the entire actual history and appends every
query from both parts, including exploratory requests. -/
theorem Executes.bind {oracle : AdaptiveOracle.Policy Query Reply}
    {p : Program Query Reply A} {history : History Query Reply} {a : A} {first : History Query Reply}
    (hp : Executes oracle p history a first) (f : A → Program Query Reply B)
    {b : B} {second : History Query Reply}
    (hf : Executes oracle (f a) (history ++ first) b second) :
    Executes oracle (p.bind f) history b (first ++ second) := by
  induction hp with
  | returned a history => simpa only [Program.bind, List.nil_append, List.append_nil] using hf
  | ask q k history reply a tail hreply hnext ih =>
    apply Executes.ask q (fun r => (k r).bind f) history reply b (tail ++ second) hreply
    apply ih
    simpa only [List.append_assoc, List.singleton_append] using hf

/-- A successful query-program derivation gives the exact run of its compiled
next-action protocol under any sufficient fuel, not merely a trace certificate. -/
theorem Executes.compiled_run {oracle : AdaptiveOracle.Policy Query Reply}
    {p : Program Query Reply A} {history : History Query Reply} {a : A} {trace : History Query Reply}
    (hp : Executes oracle p history a trace) (initial : Program Query Reply A)
    (hafter : initial.after history = p) (fuel : ℕ) (hbudget : trace.length ≤ fuel) :
    AdaptiveOracle.run initial.protocol oracle () fuel history = ⟨trace, .returned a⟩ := by
  induction hp generalizing initial fuel with
  | returned a history =>
    apply AdaptiveOracle.run_returned
    simp only [Program.protocol, hafter, Program.action]
  | ask q k history reply a tail hreply hnext ih =>
    have haction : initial.protocol () history = .ask q := by
      simp only [Program.protocol, hafter, Program.action]
    cases fuel with
    | zero => simp at hbudget
    | succ fuel =>
      have hbudget' : tail.length ≤ fuel := by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hbudget
      have hafter' : initial.after (history ++ [(q, reply)]) = k reply := by
        rw [Program.after_append, hafter]
        simp [Program.after]
      rw [AdaptiveOracle.run_succ_some _ _ _ _ _ _ _ haction hreply,
        ih initial hafter' fuel hbudget']

/-- The compiler begins with an empty local history and has exactly the same
full trace and output as the actual ordinary-query program. -/
theorem Executes.run {oracle : AdaptiveOracle.Policy Query Reply}
    {p : Program Query Reply A} {a : A} {trace : History Query Reply}
    (hp : Executes oracle p [] a trace) (fuel : ℕ) (hbudget : trace.length ≤ fuel) :
    AdaptiveOracle.run p.protocol oracle () fuel [] = ⟨trace, .returned a⟩ :=
  hp.compiled_run p (by simp [Program.after]) fuel hbudget

/-- Embed a bounded next-action subprotocol. Its failure branch is explicit;
proved successful subprotocols never reach it. -/
def ofProtocol (next : Protocol Unit Query Reply A) :
    ℕ → History Query Reply → Program Query Reply A
  | fuel, history => match next () history with
    | .returned a => .returned a
    | .diverge => .failed
    | .ask q => match fuel with
      | 0 => .failed
      | fuel + 1 => .ask q (fun r => ofProtocol next fuel (history ++ [(q, r)]))

/-- Successful actual subprotocol runs embed into query programs with every
reply and query preserved, even with a nonempty enclosing global history. -/
theorem ofProtocol_executes (next : Protocol Unit Query Reply A)
    (oracle : AdaptiveOracle.Policy Query Reply) (prior : History Query Reply)
    (fuel : ℕ) (history : History Query Reply) (a : A)
    (hreturn : (AdaptiveOracle.run next (fun h => oracle (prior ++ h)) () fuel history).stop = .returned a) :
    Executes oracle (ofProtocol next fuel history) (prior ++ history) a
      (AdaptiveOracle.run next (fun h => oracle (prior ++ h)) () fuel history).answered := by
  induction fuel generalizing history with
  | zero =>
    cases hn : next () history with
    | returned b =>
      have hab : b = a := by simpa [hn] using hreturn
      subst b
      simpa [ofProtocol, hn] using Executes.returned (oracle := oracle) a (prior ++ history)
    | diverge => simp [hn] at hreturn
    | ask q => simp [hn] at hreturn
  | succ fuel ih =>
    cases hn : next () history with
    | returned b =>
      have hab : b = a := by simpa [hn] using hreturn
      subst b
      simpa [ofProtocol, hn] using Executes.returned (oracle := oracle) a (prior ++ history)
    | diverge => simp [hn] at hreturn
    | ask q =>
      cases ho : oracle (prior ++ history) q with
      | none => simp [hn, ho] at hreturn
      | some reply =>
        have hstep := AdaptiveOracle.run_succ_some next (fun h => oracle (prior ++ h)) () fuel history q reply hn ho
        rw [hstep] at hreturn ⊢
        rw [ofProtocol, hn]
        apply Executes.ask _ _ _ _ _ _ ho
        simpa only [List.append_assoc] using ih (history ++ [(q, reply)]) hreturn

/-- A fixed full-history policy determines every successful program trace and
output uniquely. This lets replay use the constructed operational contracts. -/
theorem Executes.deterministic {oracle : AdaptiveOracle.Policy Query Reply}
    {p : Program Query Reply A} {history : History Query Reply} {a b : A}
    {first second : History Query Reply} (hfirst : Executes oracle p history a first)
    (hsecond : Executes oracle p history b second) : a = b ∧ first = second := by
  induction hfirst generalizing b second with
  | returned a history =>
    cases hsecond
    exact ⟨rfl, rfl⟩
  | ask q k history reply a tail hreply hnext ih =>
    cases hsecond with
    | ask _ _ _ reply' b tail' hreply' hnext' =>
      have heq : reply = reply' := Option.some.inj (hreply.symm.trans hreply')
      subst reply'
      obtain ⟨rfl, rfl⟩ := ih hnext'
      exact ⟨rfl, rfl⟩

/-- Successful sequential executions split at the actual intermediate return,
with no omitted query between the two component histories. -/
theorem Executes.split_bind {oracle : AdaptiveOracle.Policy Query Reply}
    (p : Program Query Reply A) (f : A → Program Query Reply B)
    {history : History Query Reply} {b : B} {trace : History Query Reply}
    (h : Executes oracle (p.bind f) history b trace) :
    ∃ a first second, Executes oracle p history a first ∧
      Executes oracle (f a) (history ++ first) b second ∧ trace = first ++ second := by
  induction p generalizing history b trace with
  | returned a =>
    exact ⟨a, [], trace, Executes.returned a history, by simpa only [Program.bind, List.append_nil] using h,
      by simp⟩
  | failed => cases h
  | ask q k ih =>
    cases h with
    | ask _ _ _ reply b tail hreply hnext =>
      obtain ⟨a, first, second, hfirst, hsecond, heq⟩ := ih reply hnext
      refine ⟨a, (q, reply) :: first, second,
        Executes.ask q k history reply a first hreply hfirst, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using hsecond
      · simp only [List.cons_append, heq]

end EnvyFreeResearch.Full.Chores.QueryProgram
