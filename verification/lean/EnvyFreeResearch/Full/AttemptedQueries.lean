import EnvyFreeResearch.Full.OracleProtocol

/-! Attempted query counts include the possible final illegal request.
All other terminal outcomes incur exactly their answered-call count. -/

namespace EnvyFreeResearch.Full.AttemptedQueries
open OracleProtocol

variable {Tape Query Reply Output : Type*}

def attempts (e : Execution Query Reply Output) : ℕ :=
  e.answered.length + match e.stop with
    | .illegal _ => 1
    | _ => 0

theorem answered_le_attempts (e : Execution Query Reply Output) : e.answered.length ≤ attempts e :=
  Nat.le_add_right _ _

noncomputable def attemptedCost (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (history : History Query Reply) : ℕ∞ :=
  ⨆ fuel, (attempts (run next oracle tape fuel history) : ℕ∞)

theorem queryCost_le_attemptedCost (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (history : History Query Reply) :
    queryCost next oracle tape history ≤ attemptedCost next oracle tape history := by
  apply iSup_le
  intro fuel
  apply le_iSup_of_le fuel
  exact_mod_cast answered_le_attempts (run next oracle tape fuel history)

theorem attemptedCost_of_terminal (next : Protocol Tape Query Reply Output)
    (oracle : Query → Option Reply) (tape : Tape) (fuel : ℕ) (history : History Query Reply)
    (ht : Terminal (run next oracle tape fuel history).stop) :
    attemptedCost next oracle tape history = (attempts (run next oracle tape fuel history) : ℕ∞) := by
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hk : fuel ≤ k
    · rw [run_eq_of_terminal_of_le next oracle tape fuel k history hk ht]
    · have hk' : k ≤ fuel := le_of_not_ge hk
      by_cases htk : Terminal (run next oracle tape k history).stop
      · rw [← run_eq_of_terminal_of_le next oracle tape k fuel history hk' htk]
      · obtain ⟨q,hq⟩ : ∃ q, (run next oracle tape k history).stop = .exhausted q := by
          simpa only [Terminal, not_forall, not_not] using htk
        have hl := answered_length_mono next oracle tape history hk'
        have ha := answered_le_attempts (run next oracle tape fuel history)
        change ((attempts (run next oracle tape k history) : ℕ) : ℕ∞) ≤ _
        rw [attempts, hq]
        exact_mod_cast (by simpa using hl.trans ha)
  · exact le_iSup (fun k => (attempts (run next oracle tape k history) : ℕ∞)) fuel

end EnvyFreeResearch.Full.AttemptedQueries
