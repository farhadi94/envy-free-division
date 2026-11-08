import EnvyFreeResearch.Full.UpperRepairHistory
import EnvyFreeResearch.Full.UpperQueryLegality
import EnvyFreeResearch.Full.UpperRepairOutputMeasurable

/-! Every attempted ordinary query of concrete Repair is legal, including
all rejected attempts. The actual program therefore executes without default
answers against every full-history Option-valued legal oracle. Its finite
bounded run returns the exact physical output and preserves all query charges.
Only the final probability statement needs joint oracle measurability. -/

noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal

namespace EnvyFreeResearch.Full.UpperRepairLegality

open IntervalOracle UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperEndpointCache UpperRepairPreparationChecks UpperQueryPrograms Chores.QueryProgram UpperQueryLegality

variable {n k : ℕ} [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (hk : 2 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (old : Fin k → State n) (hold : ∀ j, WellFormed μ (old j))
  (hnear : Near chores μ active origin old (UpperRepair.nearError n))

include hinj hgood hpositive hold hnear in
theorem all_attempts (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (p : UpperRepair.Tape n k) :
    ∃ trace, Executes (totalPolicy policy) (UpperRepair.program hk chores active origin old p) origin.history
      (UpperRepair.execute policy hk chores active origin old p) trace ∧
      (UpperRepair.execute policy hk chores active origin old p).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 6 * n * UpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 3 * UpperRepair.fine n ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧ ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  let testPolicy := rejectingPolicy (Chores.measureProfile μ) policy
  have ht : Admissible (Chores.measureProfile μ) testPolicy := rejectingPolicy_admissible _ policy hpolicy
  obtain ⟨testTrace, hexec, hhistory, _, _⟩ := UpperRepair.program_cost testPolicy hk chores active hinj origin old p
  have htruth := UpperRepairHistory.original_history_truthful μ testPolicy ht hk chores active hinj
    origin hgood hpositive old hold hnear p
  rw [hhistory] at htruth
  have hnew : ∀ entry ∈ testTrace, ValidReply (Chores.measureProfile μ) entry.1 entry.2 :=
    fun entry he => htruth entry (List.mem_append_right _ he)
  obtain ⟨hreplay, hlegal⟩ := truthful_replay (Chores.measureProfile μ) policy hexec hnew
  obtain ⟨trace, hrun, hh, hq, hc⟩ := UpperRepair.program_cost policy hk chores active hinj origin old p
  have heq := hreplay.deterministic hrun
  refine ⟨trace, hrun, hh, hq, hc, ?_⟩
  intro entry he
  rw [← heq.2] at he
  exact ⟨hlegal entry he, hnew entry he⟩

include hinj hgood hpositive hold hnear in
theorem option_executes (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle) (p : UpperRepair.Tape n k) :
    ∃ trace, Executes oracle (UpperRepair.program hk chores active origin old p) origin.history
      (UpperRepair.execute (AdaptiveOracle.answer oracle) hk chores active origin old p) trace ∧
      (UpperRepair.execute (AdaptiveOracle.answer oracle) hk chores active origin old p).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 6 * n * UpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 3 * UpperRepair.fine n ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧ ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  obtain ⟨trace, he, hh, hq, hc, hl⟩ := all_attempts μ hk chores active hinj origin hgood hpositive old hold hnear
    (AdaptiveOracle.answer oracle) (UpperQueryLegality.answer_admissible _ oracle horacle) p
  exact ⟨trace, option_replay _ oracle horacle he (fun entry hm => (hl entry hm).1), hh, hq, hc, hl⟩

include hinj hgood hpositive hold hnear in
theorem option_run (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle) (p : UpperRepair.Tape n k) :
    ∃ trace, AdaptiveOracle.run (UpperRepair.program hk chores active origin old p).protocol
      (fun history => oracle (origin.history ++ history)) () (6 * n * UpperRepair.fine n) [] =
        ⟨trace, .returned (UpperRepair.execute (AdaptiveOracle.answer oracle) hk chores active origin old p)⟩ ∧
      (UpperRepair.execute (AdaptiveOracle.answer oracle) hk chores active origin old p).2.1.history = origin.history ++ trace ∧
      trace.length ≤ 6 * n * UpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 3 * UpperRepair.fine n ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧ ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  obtain ⟨trace, he, hh, hq, hc, hl⟩ := option_executes μ hk chores active hinj origin hgood hpositive old hold hnear oracle horacle p
  exact ⟨trace, compiled_from_prior oracle he _ hq, hh, hq, hc, hl⟩

theorem answer_measurable (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (hmeas : Measurable (fun p : History n × Query n => oracle p.1 p.2)) :
    MeasurablePolicy (AdaptiveOracle.answer oracle) :=
  UpperCorrectionOutputMeasurable.getD_measurable (fun p : History n × Query n => oracle p.1 p.2) hmeas 0

include hinj hgood hpositive hold hnear in
theorem option_failure_lt (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (hmeas : Measurable (fun p : History n × Query n => oracle p.1 p.2)) :
    UpperRepair.law n k {p | (UpperRepair.execute (AdaptiveOracle.answer oracle) hk chores active origin old p).2.2 = true} < 1 / 64 :=
  UpperRepair.failure_lt μ (AdaptiveOracle.answer oracle) (UpperQueryLegality.answer_admissible _ oracle horacle)
    hk chores active hinj origin hgood hpositive old hold hnear (answer_measurable oracle hmeas)

include hinj hgood hpositive hold hnear in
theorem option_success_facts (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle)
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ j, Disjoint (domain (old j).cells) (domain origin.cells))
    (holdHistory : ∀ j, (old j).history ⊆ origin.history) (p : UpperRepair.Tape n k)
    (hsuccess : (UpperRepair.execute (AdaptiveOracle.answer oracle) hk chores active origin old p).2.2 = false) :
    UpperRepairProgram.SuccessFacts μ chores active origin old
      (UpperRepair.execute (AdaptiveOracle.answer oracle) hk chores active origin old p) :=
  UpperRepair.success_facts μ (AdaptiveOracle.answer oracle) (UpperQueryLegality.answer_admissible _ oracle horacle)
    hk chores active hinj origin hgood hpositive old hold hnear holdpair holdbuffer holdHistory p hsuccess

end EnvyFreeResearch.Full.UpperRepairLegality
