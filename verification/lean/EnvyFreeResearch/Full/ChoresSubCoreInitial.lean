import EnvyFreeResearch.Full.ChoresSubCoreTargets

/-!
# The actual initial selected-state construction

Selected agents receive their chosen winner records. Unassigned contested
parents are refreshed to the actual remaining-trim caps. The entire inherited
interface of the selected-set loop follows from the legal trim table.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set

variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]
    {value : Agent → Parent → Coord → Value} {feasible : Set Coord}
    {whole : Parent → Coord} {target : Agent → Value}

def initialLoopState (table : TrimTable value feasible whole target)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) : LoopState Agent Parent Coord :=
  let selected := table.selected hne preferred
  let assigned := table.assigned hne preferred
  let winners := fun p => table.point (table.winner hne preferred p) p
  ⟨selected, assigned, refreshUnused selected assigned winners (table.remainingCap selected)⟩

theorem winner_inside_remainingCap (table : TrimTable value feasible whole target)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent)
    (selected : Finset Agent) (p : Parent) :
    table.point (table.winner hne preferred p) p ≤ table.remainingCap selected p := by
  by_cases hrem : (table.remaining selected p).Nonempty
  · obtain ⟨i, hi, _, heq, _⟩ := table.cap_attained selected p hrem
    rw [heq]
    exact (table.winner_spec hne preferred p).2 i hi
  · rw [table.cap_whole_of_empty selected p hrem]
    exact (table.point_spec _ p (table.winner_spec hne preferred p).1).2.1

theorem initialLoopState_inherited (table : TrimTable value feasible whole target)
    (hmono : ∀ i p, MonotoneOn (value i p) feasible) (hwhole : ∀ p, whole p ∈ feasible)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) :
    Inherited table (initialLoopState table hne preferred) ∧
      (initialLoopState table hne preferred).selected.card ≤ Fintype.card Parent := by
  let selected := table.selected hne preferred
  let assigned := table.assigned hne preferred
  let winners := fun p => table.point (table.winner hne preferred p) p
  obtain ⟨hcard, hown, hEF⟩ := table.initial_selection_correct hmono hwhole hne preferred
  have hfeasible : ∀ p, winners p ∈ feasible :=
    fun p => (table.point_spec _ p (table.winner_spec hne preferred p).1).1
  obtain ⟨hvalid, _, hsame, hEF', hunused⟩ := refresh_inherited selected assigned value feasible
    winners winners (table.remainingCap selected) hfeasible (fun p => (table.cap_feasible hwhole selected p).1)
    (fun _ => le_rfl) (winner_inside_remainingCap table hne preferred selected) hEF
  refine ⟨⟨hvalid, ?_, hEF', hunused⟩, hcard⟩
  intro i
  change target i.val ≤ value i.val (assigned i)
    (refreshUnused selected assigned winners (table.remainingCap selected) (assigned i))
  rw [hsame i, hown i]

/-- All initial own values are exactly the stage targets, so these are the
first recursive call's actual recorded benchmarks. -/
theorem initialLoopState_own (table : TrimTable value feasible whole target)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) :
    ∀ i : (initialLoopState table hne preferred).selected,
      ownValue _ (initialLoopState table hne preferred).node value i = target i.val := by
  intro i
  change ↥(table.selected hne preferred) at i
  change value i.val (table.assigned hne preferred i)
    (refreshUnused _ (table.assigned hne preferred) (fun p => table.point (table.winner hne preferred p) p)
      (table.remainingCap (table.selected hne preferred)) (table.assigned hne preferred i)) = target i.val
  rw [refreshUnused_assigned]
  have h := (table.point_spec _ (table.assigned hne preferred i)
    (table.winner_spec hne preferred (table.assigned hne preferred i)).1).2.2
  simpa only [table.assigned_winner hne preferred i] using h

end EnvyFreeResearch.Full.Chores.SubCore
