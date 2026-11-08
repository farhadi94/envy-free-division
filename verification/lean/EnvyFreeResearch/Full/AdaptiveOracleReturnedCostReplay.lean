import EnvyFreeResearch.Full.AdaptiveOracleReturnedCost

/-! A returned run replays under any policy preserving its defined replies.
The totalized reply policy need not be globally legal on other requests. -/
namespace EnvyFreeResearch.Full.AdaptiveOracle
open OracleProtocol
universe u v w t
variable {Tape : Type t} {Query : Type u} {Reply : Type v} {Output : Type w}

theorem run_returned_replay (next : Protocol Tape Query Reply Output)
    (oracle other : Policy Query Reply)
    (hext : ∀ history q r, oracle history q=some r → other history q=some r)
    (tape : Tape) (fuel : ℕ) (history : History Query Reply) (out : Output)
    (h : (run next oracle tape fuel history).stop=.returned out) :
    run next other tape fuel history=run next oracle tape fuel history := by
  induction fuel generalizing history with
  | zero =>
    cases hn : next tape history with
    | returned o => simp [hn]
    | diverge => simp [hn] at h
    | ask q => simp [hn] at h
  | succ fuel ih =>
    cases hn : next tape history with
    | returned o => simp [hn]
    | diverge => simp [hn] at h
    | ask q =>
      cases ho : oracle history q with
      | none => simp [hn,ho] at h
      | some r =>
        have ht : (run next oracle tape fuel (history++[(q,r)])).stop=.returned out := by
          simpa only [run_succ_some _ _ _ _ _ _ _ hn ho] using h
        rw [run_succ_some _ _ _ _ _ _ _ hn (hext history q r ho),
          run_succ_some _ _ _ _ _ _ _ hn ho,ih (history++[(q,r)]) ht]

theorem run_total_answer_of_returned (next : Protocol Tape Query Reply Output)
    (oracle : Policy Query Reply) (default : Reply) (tape : Tape) (fuel : ℕ)
    (history : History Query Reply) (trace : History Query Reply) (out : Output)
    (h : run next oracle tape fuel history=⟨trace,.returned out⟩) :
    run next (fun history q => some ((oracle history q).getD default)) tape fuel history=⟨trace,.returned out⟩ := by
  rw [run_returned_replay next oracle _ (fun history q r hr => by simp [hr])
    tape fuel history out (congrArg Execution.stop h),h]

end EnvyFreeResearch.Full.AdaptiveOracle
