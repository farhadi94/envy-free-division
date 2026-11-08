import EnvyFreeResearch.Full.ChoresSubCoreNecessity

/-!
# Completing a SubCore assignment on all current participants

These data operations insert the last participant using only an actual free
parent and the selected matching. Their definitions do not inspect an envy
predicate. The correctness theorem supplies the full recursive output type.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set

variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]

structure Allocation (Agent Parent Coord : Type*) where
  assigned : Agent ↪ Parent
  point : Parent → Coord

def AllocationCorrect (value : Agent → Parent → Coord → Value) (feasible : Set Coord)
    (whole : Parent → Coord) (benchmark : Agent → Value) (out : Allocation Agent Parent Coord) : Prop :=
  (∀ p, out.point p ∈ feasible ∧ out.point p ≤ whole p) ∧
  (∀ i p, value i p (out.point p) ≤ value i (out.assigned i) (out.point (out.assigned i))) ∧
  (∀ i, benchmark i ≤ value i (out.assigned i) (out.point (out.assigned i))) ∧
  (∀ p, (∀ i, out.assigned i ≠ p) → out.point p = whole p) ∧
  (∃ i, out.point (out.assigned i) = whole (out.assigned i))

def InheritedAllocation (value : Agent → Parent → Coord → Value) (feasible : Set Coord)
    (whole : Parent → Coord) (benchmark : Agent → Value) (inherited : Allocation Agent Parent Coord) : Prop :=
  (∀ i, inherited.point (inherited.assigned i) ∈ feasible ∧ inherited.point (inherited.assigned i) ≤ whole (inherited.assigned i)) ∧
  (∀ i, value i (inherited.assigned i) (inherited.point (inherited.assigned i)) = benchmark i) ∧
  (∀ i j, value i (inherited.assigned j) (inherited.point (inherited.assigned j)) ≤ benchmark i)

theorem exists_outside (selected : Finset Agent) (hcard : selected.card < Fintype.card Agent) :
    ∃ i, i ∉ selected := by
  obtain ⟨i, hi⟩ := exists_free_parent selected hcard
    (⟨Subtype.val, Subtype.val_injective⟩ : selected ↪ Agent)
  exact ⟨i, fun h => hi ⟨i, h⟩ rfl⟩

def lastAgent (selected : Finset Agent) (hcard : selected.card + 1 = Fintype.card Agent) : Agent :=
  Classical.choose (exists_outside selected (by omega))

theorem lastAgent_outside (selected : Finset Agent) (hcard : selected.card + 1 = Fintype.card Agent) :
    lastAgent selected hcard ∉ selected :=
  Classical.choose_spec (exists_outside selected (by omega))

theorem insert_last_eq_univ (selected : Finset Agent) (i : Agent) (hi : i ∉ selected)
    (hcard : selected.card + 1 = Fintype.card Agent) : insert i selected = Finset.univ :=
  Finset.eq_univ_of_card _ ((Finset.card_insert_of_notMem hi).trans hcard)

def allAsInserted (selected : Finset Agent) (i : Agent) (hi : i ∉ selected)
    (hcard : selected.card + 1 = Fintype.card Agent) : Agent ↪ ↑(insert i selected) :=
  ⟨fun j => ⟨j, by rw [insert_last_eq_univ selected i hi hcard]; exact Finset.mem_univ j⟩,
    fun _ _ h => congrArg (fun j : ↑(insert i selected) => j.val) h⟩

def completeNode (selected : Finset Agent) (node : Node selected Parent Coord)
    (i : Agent) (p : Parent) (hi : i ∉ selected)
    (hcard : selected.card + 1 = Fintype.card Agent) (hfree : ∀ j, node.assigned j ≠ p) :
    Allocation Agent Parent Coord :=
  ⟨(allAsInserted selected i hi hcard).trans (insertedAssignment selected node.assigned i p hfree), node.point⟩

/-- The precise data operation used by both the easy branch and the final
uncontested assignment. All old records remain fixed. -/
theorem completeNode_correct (selected : Finset Agent) (node : Node selected Parent Coord)
    (i : Agent) (p : Parent) (hi : i ∉ selected)
    (hcard : selected.card + 1 = Fintype.card Agent) (hfree : ∀ j, node.assigned j ≠ p)
    (value : Agent → Parent → Coord → Value) (feasible : Set Coord)
    (whole : Parent → Coord) (benchmark : Agent → Value)
    (hpoint : ∀ p, node.point p ∈ feasible ∧ node.point p ≤ whole p)
    (hbest : ∀ j : selected, ∀ q, value j.val q (node.point q) ≤ ownValue selected node value j)
    (hbench : ∀ j : selected, benchmark j.val ≤ ownValue selected node value j)
    (hunused : ∀ q, (∀ j, node.assigned j ≠ q) → node.point q = whole q)
    (hnew : ∀ q, value i q (node.point q) ≤ value i p (node.point p))
    (hnewBench : benchmark i ≤ value i p (node.point p)) :
    AllocationCorrect value feasible whole benchmark (completeNode selected node i p hi hcard hfree) := by
  obtain ⟨_, hb, hbm, hu, hn, _⟩ := grow_selected selected node.assigned i p hi hfree value node.point whole benchmark
    hbest hbench hunused hnew hnewBench
  refine ⟨hpoint, ?_, ?_, ?_, ⟨i, ?_⟩⟩
  · intro j q
    exact hb (allAsInserted selected i hi hcard j) q
  · intro j
    exact hbm (allAsInserted selected i hi hcard j)
  · intro q hq
    apply hu q
    intro j hj
    exact hq j.val hj
  · change node.point (insertOwner selected node.assigned i p (allAsInserted selected i hi hcard i)) =
      whole (insertOwner selected node.assigned i p (allAsInserted selected i hi hcard i))
    have heq : insertOwner selected node.assigned i p (allAsInserted selected i hi hcard i) = p := by
      exact hn
    rw [heq]
    exact hunused p hfree

end EnvyFreeResearch.Full.Chores.SubCore
