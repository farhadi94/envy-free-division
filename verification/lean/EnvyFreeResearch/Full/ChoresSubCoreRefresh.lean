import EnvyFreeResearch.Full.ChoresSubCoreFinish

/-!
# Refreshing enlarged parents before a smaller recursive SubCore call

Only unassigned parent records are replaced by the newly computed cached
caps. Assigned suffixes and their own values are unchanged. The next inherited
assignment is therefore coherent and envy-free with exact updated benchmarks.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set

variable {Agent Parent Coord Value : Type*}

def refreshUnused (selected : Finset Agent) (assigned : selected ↪ Parent)
    (state newCap : Parent → Coord) (p : Parent) : Coord := by
  classical
  exact if ∃ i, assigned i = p then state p else newCap p

theorem refreshUnused_assigned (selected : Finset Agent) (assigned : selected ↪ Parent)
    (state newCap : Parent → Coord) (i : selected) :
    refreshUnused selected assigned state newCap (assigned i) = state (assigned i) := by
  classical
  have h : ∃ j, assigned j = assigned i := ⟨i, rfl⟩
  simp only [refreshUnused, ite_eq_left h]

theorem refreshUnused_free (selected : Finset Agent) (assigned : selected ↪ Parent)
    (state newCap : Parent → Coord) (p : Parent) (hp : ∀ i, assigned i ≠ p) :
    refreshUnused selected assigned state newCap p = newCap p := by
  classical
  have h : ¬∃ j, assigned j = p := by simpa only [not_exists] using hp
  simp only [refreshUnused, ite_eq_right h]

variable [Preorder Coord] [Preorder Value]

/-- This exact inherited state is passed to the next smaller recursive call.
No additional target, utility equation or geometric inclusion is assumed. -/
theorem refresh_inherited (selected : Finset Agent) (assigned : selected ↪ Parent)
    (value : Agent → Parent → Coord → Value) (feasible : Set Coord)
    (state oldCap newCap : Parent → Coord)
    (hstate : ∀ p, state p ∈ feasible) (hcap : ∀ p, newCap p ∈ feasible)
    (hinside : ∀ p, state p ≤ oldCap p) (henlarge : ∀ p, oldCap p ≤ newCap p)
    (hEF : ∀ i j : selected, value i.val (assigned j) (state (assigned j)) ≤
      value i.val (assigned i) (state (assigned i))) :
    let updated := refreshUnused selected assigned state newCap
    (∀ p, updated p ∈ feasible ∧ updated p ≤ newCap p) ∧
    (∀ i : selected, updated (assigned i) = state (assigned i)) ∧
    (∀ i : selected, value i.val (assigned i) (updated (assigned i)) =
      value i.val (assigned i) (state (assigned i))) ∧
    (∀ i j : selected, value i.val (assigned j) (updated (assigned j)) ≤
      value i.val (assigned i) (updated (assigned i))) ∧
    (∀ p, (∀ i, assigned i ≠ p) → updated p = newCap p) := by
  classical
  dsimp only
  refine ⟨?_, refreshUnused_assigned selected assigned state newCap, ?_, ?_,
    refreshUnused_free selected assigned state newCap⟩
  · intro p
    unfold refreshUnused
    split_ifs
    · exact ⟨hstate p, (hinside p).trans (henlarge p)⟩
    · exact ⟨hcap p, le_rfl⟩
  · intro i
    rw [refreshUnused_assigned]
  · intro i j
    rw [refreshUnused_assigned, refreshUnused_assigned]
    exact hEF i j

end EnvyFreeResearch.Full.Chores.SubCore
