import EnvyFreeResearch.Full.ChoresOuterDriverTransitions

/-! Uniform actual group budgets and telescoping query ledgers. These
bounds count entire executed groups, including all retained-piece Evals. -/
namespace EnvyFreeResearch.Full.Chores.Outer

theorem source_budget_mono : Monotone SubCore.sourceBudget := by
  apply monotone_nat_of_le_succ
  intro k
  rw [SubCore.sourceBudget]
  omega

theorem recorded_budget_mono (n : ℕ) : Monotone (ComponentRecording.budget n) := by
  intro a b hab
  rw [ComponentRecording.budget_eq,ComponentRecording.budget_eq]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (source_budget_mono hab)) (Nat.mul_le_mul_left n hab)

theorem append_group_budget (old next final groups unit first second : ℕ)
    (hfinal : final ≤ next) (hcharge : groups+next ≤ old)
    (hfirst : first ≤ groups*unit) (hsecond : second ≤ (next-final)*unit) :
    first+second ≤ (old-final)*unit := by
  have hnext : next ≤ old := by omega
  have hfinold : final ≤ old := hfinal.trans hnext
  have hsubnext := Nat.sub_add_cancel hfinal
  have hsubold := Nat.sub_add_cancel hfinold
  nlinarith

theorem filter_query_budget (old next final unit q : ℕ)
    (hsize : next ≤ old) (hq : q ≤ (next-final)*unit) : q ≤ (old-final)*unit :=
  hq.trans (Nat.mul_le_mul_right unit (Nat.sub_le_sub_right hsize final))

theorem add_terminal_budget (old final unit prior terminal : ℕ)
    (hsize : final ≤ old) (hpositive : 0 < final)
    (hprior : prior ≤ (old-final)*unit) (hterminal : terminal ≤ unit) :
    prior+terminal ≤ old*unit := by
  have hsub := Nat.sub_add_cancel hsize
  nlinarith

end EnvyFreeResearch.Full.Chores.Outer
