import EnvyFreeResearch.Full.UpperQueryPrograms

/-! Whole-trace legality from a universally truthful execution.

The modified policy agrees with the original policy on every legal request.
For an illegal Eval (including bad endpoint geometry) it returns the true
cumulative difference plus one; for an illegal Cut it returns right+1.
Both violate the exact ValidReply predicate retained by Truthful. Thus a
truthful complete trace against this admissible modified policy consists only
of legal requests and replays unchanged against the original policy.
This pathwise argument requires no measurable-policy assumption. -/

noncomputable section
open scoped Classical

namespace EnvyFreeResearch.Full.UpperQueryLegality

open IntervalOracle UpperCircularStage UpperQueryPrograms Chores.QueryProgram

variable {n : ℕ}

def invalidReply (P : Profile (Fin n)) : Query n → ℝ
  | .eval i a b => P.cumulative i b - P.cumulative i a + 1
  | .cut _ _ b _ => b + 1

theorem invalidReply_not_valid (P : Profile (Fin n)) (q : Query n) :
    ¬ ValidReply P q (invalidReply P q) := by
  cases q with
  | eval i a b =>
    simp only [invalidReply, ValidReply]
    linarith
  | cut i a b t =>
    intro h
    have hright : b + 1 ≤ b := h.1.2
    linarith

def rejectingPolicy (P : Profile (Fin n)) (policy : Policy n) : Policy n :=
  fun history q => if Legal P q then policy history q else invalidReply P q

theorem rejectingPolicy_admissible (P : Profile (Fin n)) (policy : Policy n)
    (hpolicy : Admissible P policy) : Admissible P (rejectingPolicy P policy) := by
  intro history q hq
  simpa only [rejectingPolicy, hq, ite_true] using hpolicy history q hq

theorem truthful_replay {Output : Type} (P : Profile (Fin n)) (policy : Policy n)
    {program : QProgram n Output} {prior : History n} {output : Output} {trace : History n}
    (hexec : Executes (totalPolicy (rejectingPolicy P policy)) program prior output trace)
    (htruth : ∀ entry ∈ trace, ValidReply P entry.1 entry.2) :
    Executes (totalPolicy policy) program prior output trace ∧
      ∀ entry ∈ trace, Legal P entry.1 := by
  induction hexec with
  | returned a history =>
    exact ⟨Executes.returned a history, by simp⟩
  | ask q next history reply a tail hreply hnext ih =>
    have hr : rejectingPolicy P policy history q = reply := Option.some.inj hreply
    have hv := htruth (q, reply) (by simp)
    have hlegal : Legal P q := by
      by_contra hn
      rw [rejectingPolicy, ite_eq_right hn] at hr
      rw [← hr] at hv
      exact invalidReply_not_valid P q hv
    have hanswer : totalPolicy policy history q = some reply := by
      rw [rejectingPolicy, ite_eq_left hlegal] at hr
      exact congrArg some hr
    obtain ⟨htail, htailLegal⟩ := ih (fun entry he => htruth entry (List.mem_cons_of_mem _ he))
    refine ⟨Executes.ask q next history reply a tail hanswer htail, ?_⟩
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact hlegal
    · exact htailLegal entry he

theorem answer_admissible (P : Profile (Fin n)) (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy P oracle) : Admissible P (AdaptiveOracle.answer oracle) :=
  fun history q hq => (AdaptiveOracle.answer_spec P oracle horacle history q hq).2

/-- No invalid request is silently assigned the default real answer: every
entry in this execution has a genuine Option-oracle reply at its full history. -/
theorem option_replay {Output : Type} (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query n) ℝ) (horacle : AdaptiveOracle.IsLegalPolicy P oracle)
    {program : QProgram n Output} {prior : History n} {output : Output} {trace : History n}
    (hexec : Executes (totalPolicy (AdaptiveOracle.answer oracle)) program prior output trace)
    (hlegal : ∀ entry ∈ trace, Legal P entry.1) : Executes oracle program prior output trace := by
  induction hexec with
  | returned a history => exact Executes.returned a history
  | ask q next history reply a tail hreply hnext ih =>
    have hq := hlegal (q, reply) (by simp)
    have hr := (AdaptiveOracle.answer_spec P oracle horacle history q hq).1
    refine Executes.ask q next history reply a tail (hr.trans hreply) ?_
    exact ih (fun entry he => hlegal entry (List.mem_cons_of_mem _ he))

/-- A nonempty enclosing history is passed to the oracle; local replay starts
at the beginning of the subprogram rather than replaying the enclosing calls. -/
theorem shift_execution {Output : Type} (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    {program : QProgram n Output} {history : History n} {output : Output} {trace : History n}
    (hexec : Executes oracle program history output trace) (prior localHistory : History n)
    (heq : history = prior ++ localHistory) :
    Executes (fun h => oracle (prior ++ h)) program localHistory output trace := by
  induction hexec generalizing localHistory with
  | returned a history => exact Executes.returned a localHistory
  | ask q next history reply a tail hreply hnext ih =>
    apply Executes.ask q next localHistory reply a tail
    · simpa only [← heq] using hreply
    · apply ih (localHistory ++ [(q, reply)])
      simp only [heq, List.append_assoc]

theorem compiled_from_prior {Output : Type} (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    {program : QProgram n Output} {prior : History n} {output : Output} {trace : History n}
    (hexec : Executes oracle program prior output trace) (fuel : ℕ) (hbudget : trace.length ≤ fuel) :
    AdaptiveOracle.run program.protocol (fun history => oracle (prior ++ history)) () fuel [] =
      ⟨trace, .returned output⟩ :=
  (shift_execution oracle hexec prior [] (List.append_nil prior).symm).run fuel hbudget

end EnvyFreeResearch.Full.UpperQueryLegality
