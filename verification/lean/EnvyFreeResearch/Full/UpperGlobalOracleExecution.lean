import EnvyFreeResearch.Full.UpperGlobalOracleNext
import EnvyFreeResearch.Full.UpperGlobalOracleExecutionCounts

/-! A single next-action protocol executes an observable returned finite
prefix with exactly the same ordinary queries, replies and output. -/
noncomputable section
namespace EnvyFreeResearch.Full.UpperGlobalPhysical
open UpperCircularStage UpperQueryPrograms Chores.QueryProgram OracleProtocol
open UpperGlobalRun.OracleNext
variable {n : ℕ} {Tape : Type*}

theorem executes_observable_run (next : Protocol Tape (Query n) ℝ (Phase n)) (omega : Tape)
    {oracle : AdaptiveOracle.Policy (Query n) ℝ} {p : QProgram n (Phase n)}
    {history : History n} {out : Phase n} {trace : History n}
    (he : Executes oracle p history out trace) (initial : QProgram n (Phase n))
    (hafter : initial.after history=p) (hterminal : out.finished=true)
    (hmatch : ∀ h, observable ((initial.after h).action)=true → next omega h=(initial.after h).action)
    (fuel : ℕ) (hbudget : trace.length ≤ fuel) :
    AdaptiveOracle.run next oracle omega fuel history=⟨trace,.returned out⟩ := by
  induction he generalizing initial fuel with
  | returned out history =>
    apply AdaptiveOracle.run_returned
    have ho : observable ((initial.after history).action)=true := by
      rw [hafter]
      exact hterminal
    rw [hmatch history ho,hafter]
    rfl
  | ask q k history reply out tail hreply hrest ih =>
    have hn : next omega history=.ask q := by
      rw [hmatch history (by rw [hafter]; rfl),hafter]
      rfl
    cases fuel with
    | zero => simp at hbudget
    | succ fuel =>
      have hb : tail.length ≤ fuel := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hbudget
      have ha : initial.after (history++[(q,reply)])=k reply := by
        rw [Program.after_append,hafter]
        simp [Program.after]
      rw [AdaptiveOracle.run_succ_some _ _ _ _ _ _ _ hn hreply,
        ih initial ha hterminal hmatch fuel hb]

end EnvyFreeResearch.Full.UpperGlobalPhysical
