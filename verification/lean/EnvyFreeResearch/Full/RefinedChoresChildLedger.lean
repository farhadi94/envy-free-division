import EnvyFreeResearch.Full.RefinedChoresBudgets
import EnvyFreeResearch.Full.ChoresComponentPopulationGroups

/-! Exact residual child allowances in the proper-population recurrence. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresParameters
open Chores.Population

def childQueries (n : ℕ) : ℕ := (totalCapacity n).queries-envelope n
def childCuts (n : ℕ) : ℕ := (totalCapacity n).cuts-envelope n

theorem local_child_queries {n : ℕ} (hn : 0 < n) :
    envelope n+childQueries n=(totalCapacity n).queries := by
  exact Nat.add_sub_of_le (capacity_local envelope envelope hn).1

theorem local_child_cuts {n : ℕ} (hn : 0 < n) :
    envelope n+childCuts n=(totalCapacity n).cuts := by
  exact Nat.add_sub_of_le (capacity_local envelope envelope hn).2

theorem child_allowance_one {n k : ℕ} (hk : k < n) :
    (totalCapacity k).queries+n*(totalCapacity k).cuts ≤ childQueries n ∧
      (totalCapacity k).cuts ≤ childCuts n := by
  have h := capacity_one envelope envelope hk
  constructor
  · apply Nat.le_sub_of_add_le
    simpa only [totalCapacity,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.1
  · apply Nat.le_sub_of_add_le
    simpa only [totalCapacity,Nat.add_comm] using h.2

theorem child_allowance_two {n b d : ℕ} (hb : 0 < b) (hd : 0 < d) (hs : b+d=n) :
    (totalCapacity b).queries+n*(totalCapacity b).cuts+
      ((totalCapacity d).queries+n*(totalCapacity d).cuts) ≤ childQueries n ∧
    (totalCapacity b).cuts+(totalCapacity d).cuts ≤ childCuts n := by
  have h := capacity_two envelope envelope hb hd hs
  constructor
  · apply Nat.le_sub_of_add_le
    simpa only [totalCapacity,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.1
  · apply Nat.le_sub_of_add_le
    simpa only [totalCapacity,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2

end EnvyFreeResearch.Full.RefinedChoresParameters

namespace EnvyFreeResearch.Full.RefinedChoresParameters
open Chores.Population
variable {n : ℕ} (group : Finset (Fin n))
    (hpositive : group.Nonempty) (hproper : group ≠ Finset.univ)
include hpositive hproper

theorem atomic_child_allowance :
    (totalCapacity groupᶜ.card).queries+n*(totalCapacity groupᶜ.card).cuts+
      ((totalCapacity group.card).queries+n*(totalCapacity group.card).cuts) ≤ childQueries n ∧
    (totalCapacity groupᶜ.card).cuts+(totalCapacity group.card).cuts ≤ childCuts n := by
  apply child_allowance_two (Finset.card_pos.mpr (complement_nonempty hproper))
    (Finset.card_pos.mpr hpositive)
  have h := group_sizes group
  omega

theorem atomic_completion_allowance {queries cuts : ℕ}
    (hQ : queries ≤ 19*2^n*n+
      ((totalCapacity groupᶜ.card).queries+n*(totalCapacity groupᶜ.card).cuts)+
      ((totalCapacity group.card).queries+n*(totalCapacity group.card).cuts))
    (hC : cuts ≤ 19*2^n+(totalCapacity groupᶜ.card).cuts+(totalCapacity group.card).cuts) :
    queries ≤ 19*n*2^n+childQueries n ∧ cuts ≤ 19*2^n+childCuts n := by
  have h := atomic_child_allowance group hpositive hproper
  have he : 19*2^n*n=19*n*2^n := by ring
  rw [he] at hQ
  constructor <;> omega

omit hproper in
theorem exhausted_child_allowance :
    (totalCapacity groupᶜ.card).queries+n*(totalCapacity groupᶜ.card).cuts ≤ childQueries n ∧
    (totalCapacity groupᶜ.card).cuts ≤ childCuts n :=
  child_allowance_one (group_card_lt (complement_proper hpositive))

omit hproper in
theorem exhausted_completion_allowance {queries cuts : ℕ}
    (hQ : queries ≤ (totalCapacity groupᶜ.card).queries+n*(totalCapacity groupᶜ.card).cuts)
    (hC : cuts ≤ (totalCapacity groupᶜ.card).cuts) :
    queries ≤ 19*n*2^n+childQueries n ∧ cuts ≤ 19*2^n+childCuts n := by
  have h := exhausted_child_allowance group hpositive
  constructor <;> omega


end EnvyFreeResearch.Full.RefinedChoresParameters
