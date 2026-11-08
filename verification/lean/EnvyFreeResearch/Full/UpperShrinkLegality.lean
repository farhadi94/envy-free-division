import EnvyFreeResearch.Full.UpperShrinkCorrectness
import EnvyFreeResearch.Full.UpperRepairLegality

/-! The actual prescribed Shrink executes against Option-valued ordinary
oracles, including rejected attempts. No invalid query receives a default reply. -/
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace EnvyFreeResearch.Full.UpperShrink
open IntervalOracle UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperEndpointCache UpperQueryPrograms Chores.QueryProgram UpperQueryLegality
variable {n k : ℕ} [Nonempty (Fin k)] (μ : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (hk : 3 ≤ k) (chores : Bool) (active : Fin k → Fin n) (hinj : Function.Injective active)
  (origin : State n) (ho : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
  (G : ℝ) (hG : 1 ≤ G)
  (hmax : G ≤ (2/UpperShrinkPrecision.theta n)*(8/UpperRepair.nearError n)^(k-1))

include hinj ho hpositive hG hmax in
theorem final_history_truthful (policy : Policy n)
    (hp : Admissible (Chores.measureProfile μ) policy) (p : UpperRepair.Tape n k) :
    Truthful μ (execute policy (by omega) chores active origin G p).2.1.history := by
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective active hinj
  have valid := carving_valid μ policy hp hk active hinj origin ho hpositive G hG hmax
  have hgp : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have ht := (nearError_positive n).le
  have hkt := population_nearError_le_two n k hkn
  apply UpperRepairHistory.original_history_truthful μ policy hp (by omega) chores active hinj
    (carvingExecute policy active origin G).buffer valid.buffer_wellFormed
    (repair_buffer_positive μ (by omega) active origin hpositive G hgp _ valid ht hkt)
    (carvingExecute policy active origin G).old valid.old_wellFormed
    (carved_near μ active origin G _ _ valid (by omega) hgp ht hkt chores) p

include hinj ho hpositive hG hmax in
theorem all_attempts (policy : Policy n) (hp : Admissible (Chores.measureProfile μ) policy)
    (p : UpperRepair.Tape n k) :
    ∃ trace, Executes (totalPolicy policy) (program (by omega) chores active origin G p) origin.history
      (execute policy (by omega) chores active origin G p) trace ∧
      (execute policy (by omega) chores active origin G p).2.1.history=origin.history++trace ∧
      trace.length ≤ 8*n*UpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 4*UpperRepair.fine n ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧ ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  let testPolicy := rejectingPolicy (Chores.measureProfile μ) policy
  have ht : Admissible (Chores.measureProfile μ) testPolicy := rejectingPolicy_admissible _ policy hp
  obtain ⟨testTrace,hexec,hhistory,_,_⟩ := program_cost testPolicy (by omega) chores active hinj origin G hG p
  have htruth := final_history_truthful μ hk chores active hinj origin ho hpositive G hG hmax testPolicy ht p
  rw [hhistory] at htruth
  have hnew : ∀ entry ∈ testTrace, ValidReply (Chores.measureProfile μ) entry.1 entry.2 :=
    fun entry he => htruth entry (List.mem_append_right _ he)
  obtain ⟨hreplay,hlegal⟩ := truthful_replay (Chores.measureProfile μ) policy hexec hnew
  obtain ⟨trace,hrun,hh,hq,hc⟩ := program_cost policy (by omega) chores active hinj origin G hG p
  have heq := hreplay.deterministic hrun
  refine ⟨trace,hrun,hh,hq,hc,?_⟩
  intro entry he
  rw [←heq.2] at he
  exact ⟨hlegal entry he,hnew entry he⟩

include hinj ho hpositive hG hmax in
theorem option_executes (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle) (p : UpperRepair.Tape n k) :
    ∃ trace, Executes oracle (program (by omega) chores active origin G p) origin.history
      (execute (AdaptiveOracle.answer oracle) (by omega) chores active origin G p) trace ∧
      (execute (AdaptiveOracle.answer oracle) (by omega) chores active origin G p).2.1.history=origin.history++trace ∧
      trace.length ≤ 8*n*UpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 4*UpperRepair.fine n ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧ ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  obtain ⟨trace,he,hh,hq,hc,hl⟩ := all_attempts μ hk chores active hinj origin ho hpositive G hG hmax
    (AdaptiveOracle.answer oracle) (UpperQueryLegality.answer_admissible _ oracle horacle) p
  exact ⟨trace,option_replay _ oracle horacle he (fun entry hm => (hl entry hm).1),hh,hq,hc,hl⟩

include hinj ho hpositive hG hmax in
theorem option_run (oracle : AdaptiveOracle.Policy (Query n) ℝ)
    (horacle : AdaptiveOracle.IsLegalPolicy (Chores.measureProfile μ) oracle) (p : UpperRepair.Tape n k) :
    ∃ trace, AdaptiveOracle.run (program (by omega) chores active origin G p).protocol
      (fun history => oracle (origin.history++history)) () (8*n*UpperRepair.fine n) [] =
        ⟨trace,.returned (execute (AdaptiveOracle.answer oracle) (by omega) chores active origin G p)⟩ ∧
      (execute (AdaptiveOracle.answer oracle) (by omega) chores active origin G p).2.1.history=origin.history++trace ∧
      trace.length ≤ 8*n*UpperRepair.fine n ∧ (trace.map Prod.fst).countP isCut ≤ 4*UpperRepair.fine n ∧
      ∀ entry ∈ trace, Legal (Chores.measureProfile μ) entry.1 ∧ ValidReply (Chores.measureProfile μ) entry.1 entry.2 := by
  obtain ⟨trace,he,hh,hq,hc,hl⟩ := option_executes μ hk chores active hinj origin ho hpositive G hG hmax oracle horacle p
  exact ⟨trace,compiled_from_prior oracle he _ hq,hh,hq,hc,hl⟩

end EnvyFreeResearch.Full.UpperShrink
