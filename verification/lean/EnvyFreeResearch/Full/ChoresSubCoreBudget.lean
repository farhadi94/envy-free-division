import EnvyFreeResearch.Full.ChoresSubCoreLoop

/-!
# The recursive source envelope and the selected-loop sum

These identities are used by the proof of the actual recursive program.
Alone they make no claim that a physical SubCore implementation meets them.
-/

namespace EnvyFreeResearch.Full.Chores.SubCore

def sourceBudget : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * sourceBudget k + 2 * k

theorem sourceBudget_recurrence (k : ℕ) :
    sourceBudget (k + 1) = sourceBudget k + (k + 1) * k + ∑ j ∈ Finset.range k, sourceBudget j := by
  induction k with
  | zero => simp [sourceBudget]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    simp only [sourceBudget]
    simp only [sourceBudget] at ih
    nlinarith

theorem sourceBudget_closed (k : ℕ) : sourceBudget k + 2 * k + 2 = 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num [sourceBudget]
  | succ k ih =>
    rw [sourceBudget, pow_succ]
    omega

theorem sourceBudget_eq (k : ℕ) : sourceBudget k = 2 ^ (k + 1) - 2 * k - 2 := by
  have h := sourceBudget_closed k
  omega

theorem loopBudget_eq_sum (bound : ℕ → ℕ) (start count : ℕ) :
    loopBudget bound start count = ∑ j ∈ Finset.range count, bound (start + j) := by
  induction count generalizing start with
  | zero => simp [loopBudget]
  | succ count ih =>
    rw [loopBudget, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem loopBudget_add_prefix (bound : ℕ → ℕ) (start count : ℕ) :
    (∑ j ∈ Finset.range start, bound j) + loopBudget bound start count =
      ∑ j ∈ Finset.range (start + count), bound j := by
  rw [loopBudget_eq_sum, Finset.sum_range_add]

theorem loopBudget_le_full_sum (bound : ℕ → ℕ) (start count total : ℕ) (h : start + count = total) :
    loopBudget bound start count ≤ ∑ j ∈ Finset.range total, bound j := by
  rw [← h, ← loopBudget_add_prefix]
  omega

end EnvyFreeResearch.Full.Chores.SubCore
