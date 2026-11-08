import EnvyFreeResearch.Full.ChoresSubCoreSelection

/-!
# The growing-selected-set transition of SubCore

Giving a free cached whole parent to its outside trimmer adds exactly one
selected agent. Old ownership and all suffix records remain fixed. The
transition proves injectivity, cake preference, benchmarks and the literal
whole-unused invariant, so it can be composed after the equal-value chain.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

variable {Agent Parent Coord Value : Type*} [DecidableEq Agent] [Preorder Value]

def insertOwner (selected : Finset Agent) (assigned : selected ↪ Parent)
    (i : Agent) (p : Parent) (newOwner : ↑(insert i selected)) : Parent :=
  if h : newOwner.val = i then p
  else assigned ⟨newOwner.val, (Finset.mem_insert.mp newOwner.property).resolve_left h⟩

lemma insertOwner_new (selected : Finset Agent) (assigned : selected ↪ Parent)
    (i : Agent) (p : Parent) : insertOwner selected assigned i p ⟨i, Finset.mem_insert_self _ _⟩ = p := by
  simp [insertOwner]

lemma insertOwner_old (selected : Finset Agent) (assigned : selected ↪ Parent)
    (i : Agent) (p : Parent) (hi : i ∉ selected) (j : selected) :
    insertOwner selected assigned i p ⟨j.val, Finset.mem_insert_of_mem j.property⟩ = assigned j := by
  have hji : j.val ≠ i := fun h => hi (h ▸ j.property)
  simp only [insertOwner, dite_eq_right hji]

theorem insertOwner_injective (selected : Finset Agent) (assigned : selected ↪ Parent)
    (i : Agent) (p : Parent) (hfree : ∀ j, assigned j ≠ p) :
    Function.Injective (insertOwner selected assigned i p) := by
  intro j k heq
  by_cases hj : j.val = i <;> by_cases hk : k.val = i
  · exact Subtype.ext (hj.trans hk.symm)
  · simp only [insertOwner, dite_eq_left hj, dite_eq_right hk] at heq
    exact (hfree _ heq.symm).elim
  · simp only [insertOwner, dite_eq_right hj, dite_eq_left hk] at heq
    exact (hfree _ heq).elim
  · simp only [insertOwner, dite_eq_right hj, dite_eq_right hk] at heq
    exact Subtype.ext (congrArg (fun x : selected => x.val) (assigned.injective heq))

def insertedAssignment (selected : Finset Agent) (assigned : selected ↪ Parent)
    (i : Agent) (p : Parent) (hfree : ∀ j, assigned j ≠ p) : ↑(insert i selected) ↪ Parent :=
  ⟨insertOwner selected assigned i p, insertOwner_injective selected assigned i p hfree⟩

/-- This is the actual query-free transition after a recursive call and,
when needed, its ownership chain. The cardinality strictly increases by one. -/
theorem grow_selected (selected : Finset Agent) (assigned : selected ↪ Parent)
    (i : Agent) (p : Parent) (hi : i ∉ selected) (hfree : ∀ j, assigned j ≠ p)
    (value : Agent → Parent → Coord → Value) (state cap : Parent → Coord) (benchmark : Agent → Value)
    (hbest : ∀ j : selected, ∀ q, value j.val q (state q) ≤ value j.val (assigned j) (state (assigned j)))
    (hbenchmark : ∀ j : selected, benchmark j.val ≤ value j.val (assigned j) (state (assigned j)))
    (hwhole : ∀ q, (∀ j, assigned j ≠ q) → state q = cap q)
    (hnew : ∀ q, value i q (state q) ≤ value i p (state p))
    (hnewBenchmark : benchmark i ≤ value i p (state p)) :
    let newAssignment := insertedAssignment selected assigned i p hfree
    (insert i selected).card = selected.card + 1 ∧
    (∀ j : ↑(insert i selected), ∀ q, value j.val q (state q) ≤
      value j.val (newAssignment j) (state (newAssignment j))) ∧
    (∀ j : ↑(insert i selected), benchmark j.val ≤ value j.val (newAssignment j) (state (newAssignment j))) ∧
    (∀ q, (∀ j, newAssignment j ≠ q) → state q = cap q) ∧
    newAssignment ⟨i, Finset.mem_insert_self _ _⟩ = p ∧
    (∀ j : selected, newAssignment ⟨j.val, Finset.mem_insert_of_mem j.property⟩ = assigned j) := by
  dsimp only
  refine ⟨Finset.card_insert_of_notMem hi, ?_, ?_, ?_, insertOwner_new selected assigned i p,
    insertOwner_old selected assigned i p hi⟩
  · intro j q
    by_cases hj : j.val = i
    · change value j.val q (state q) ≤ value j.val (insertOwner selected assigned i p j) (state (insertOwner selected assigned i p j))
      rw [insertOwner, dite_eq_left hj, hj]
      exact hnew q
    · have hmem := (Finset.mem_insert.mp j.property).resolve_left hj
      change value j.val q (state q) ≤ value j.val (insertOwner selected assigned i p j) (state (insertOwner selected assigned i p j))
      rw [insertOwner, dite_eq_right hj]
      exact hbest ⟨j.val, hmem⟩ q
  · intro j
    by_cases hj : j.val = i
    · change benchmark j.val ≤ value j.val (insertOwner selected assigned i p j) (state (insertOwner selected assigned i p j))
      rw [insertOwner, dite_eq_left hj, hj]
      exact hnewBenchmark
    · have hmem := (Finset.mem_insert.mp j.property).resolve_left hj
      change benchmark j.val ≤ value j.val (insertOwner selected assigned i p j) (state (insertOwner selected assigned i p j))
      rw [insertOwner, dite_eq_right hj]
      exact hbenchmark ⟨j.val, hmem⟩
  · intro q hq
    apply hwhole q
    intro j hj
    apply hq ⟨j.val, Finset.mem_insert_of_mem j.property⟩
    exact (insertOwner_old selected assigned i p hi j).trans hj

/-- A rightmost remaining trim gives the new owner's global comparison by
an exact target equation and the proved cap on all current suffix values. -/
theorem grow_at_target (selected : Finset Agent) (assigned : selected ↪ Parent)
    (i : Agent) (p : Parent) (hi : i ∉ selected) (hfree : ∀ j, assigned j ≠ p)
    (value : Agent → Parent → Coord → Value) (state cap : Parent → Coord) (benchmark : Agent → Value)
    (target : Value) (hcap : ∀ q, value i q (state q) ≤ target) (htarget : value i p (state p) = target)
    (hnewBenchmark : benchmark i ≤ target)
    (hbest : ∀ j : selected, ∀ q, value j.val q (state q) ≤ value j.val (assigned j) (state (assigned j)))
    (hbenchmark : ∀ j : selected, benchmark j.val ≤ value j.val (assigned j) (state (assigned j)))
    (hwhole : ∀ q, (∀ j, assigned j ≠ q) → state q = cap q) :
    let newAssignment := insertedAssignment selected assigned i p hfree
    (insert i selected).card = selected.card + 1 ∧
    (∀ j : ↑(insert i selected), ∀ q, value j.val q (state q) ≤
      value j.val (newAssignment j) (state (newAssignment j))) ∧
    (∀ j : ↑(insert i selected), benchmark j.val ≤ value j.val (newAssignment j) (state (newAssignment j))) := by
  obtain ⟨hc, hbest', hbench', _⟩ := grow_selected selected assigned i p hi hfree value state cap benchmark
    hbest hbenchmark hwhole (fun q => (hcap q).trans_eq htarget.symm) (hnewBenchmark.trans_eq htarget.symm)
  exact ⟨hc, hbest', hbench'⟩

end EnvyFreeResearch.Full.Chores.SubCore
