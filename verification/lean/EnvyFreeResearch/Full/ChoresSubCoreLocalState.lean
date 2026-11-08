import EnvyFreeResearch.Full.ChoresSubCoreLocalStep

/-! Coherent recursive states on each parent's permanent record domain. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore.Local
open Set QueryProgram
variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]
    {value : Agent → Parent → Coord → Value} {feasible : Parent → Set Coord}
    {whole : Parent → Coord} {target : Agent → Value}

theorem refresh_inherited (selected : Finset Agent) (assigned : selected ↪ Parent)
    (value : Agent → Parent → Coord → Value) (feasible : Parent → Set Coord)
    (state oldCap newCap : Parent → Coord)
    (hstate : ∀ p, state p ∈ feasible p) (hcap : ∀ p, newCap p ∈ feasible p)
    (hinside : ∀ p, state p ≤ oldCap p) (henlarge : ∀ p, oldCap p ≤ newCap p)
    (hEF : ∀ i j : selected, value i.val (assigned j) (state (assigned j)) ≤
      value i.val (assigned i) (state (assigned i))) :
    let updated := refreshUnused selected assigned state newCap
    (∀ p, updated p ∈ feasible p ∧ updated p ≤ newCap p) ∧
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

def Inherited (table : TrimTable value feasible whole target) (s : LoopState Agent Parent Coord) : Prop :=
  (∀ p, s.node.point p ∈ feasible p ∧ s.node.point p ≤ table.remainingCap s.selected p) ∧
  (∀ i : s.selected, target i.val ≤ ownValue s.selected s.node value i) ∧
  (∀ i j : s.selected, value i.val (s.node.assigned j) (s.node.point (s.node.assigned j)) ≤
    ownValue s.selected s.node value i) ∧
  (∀ p, (∀ i, s.node.assigned i ≠ p) → s.node.point p = table.remainingCap s.selected p)

def RecursiveCorrect (table : TrimTable value feasible whole target) (selected : Finset Agent)
    (before returned : Node selected Parent Coord) : Prop :=
  (∀ p, returned.point p ∈ feasible p ∧ returned.point p ≤ table.remainingCap selected p) ∧
  (∀ i : selected, ∀ p, value i.val p (returned.point p) ≤ ownValue selected returned value i) ∧
  (∀ i : selected, ownValue selected before value i ≤ ownValue selected returned value i) ∧
  (∀ p, (∀ i, returned.assigned i ≠ p) → returned.point p = table.remainingCap selected p)

/-- The exact output of growth-and-refresh is the coherent inherited input
for the next smaller call, with assigned records and own costs preserved. -/
theorem nextLoopState_inherited (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p)
    (hstrict : ∀ i p, StrictMonoOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (old : Parent → Coord) (hold : ∀ p, old p ∈ feasible p) (holdCap : ∀ p, old p ≤ whole p)
    (hOldEF : ∀ p q, value (oldOwner p) q (old q) ≤ value (oldOwner p) p (old p))
    (hOldTarget : ∀ p, target (oldOwner p) ≤ value (oldOwner p) p (old p))
    (selected : Finset Agent) (hcard : selected.card < Fintype.card Parent)
    (before returned : Node selected Parent Coord)
    (hbefore : Inherited table ⟨selected, before⟩) (hreturn : RecursiveCorrect table selected before returned) :
    Inherited table (nextLoopState table.erase oldOwner hOwner selected hcard returned) := by
  classical
  let benchmark := loopBenchmark selected before value target
  let growth := growthStep table.erase oldOwner hOwner selected hcard returned.assigned
  let enlarged := insert growth.entrant selected
  have hbench : ∀ i : selected, benchmark i.val ≤ ownValue selected returned value i := by
    intro i
    simpa only [benchmark, loopBenchmark, dite_eq_left i.property] using hreturn.2.2.1 i
  have houtBench : ∀ i, i ∉ selected → benchmark i ≤ target i := by
    intro i hi
    simp only [benchmark, loopBenchmark, dite_eq_right hi, le_refl]
  have htargetBench : ∀ i, target i ≤ benchmark i := by
    intro i
    unfold benchmark loopBenchmark
    split_ifs with hi
    · exact hbefore.2.1 ⟨i, hi⟩
    · exact le_rfl
  obtain ⟨_, hbest, hnewBench, _⟩ := growthStep_correct table oldOwner hOwner selected hcard returned.assigned
    hstrict hwhole old returned.point benchmark hold holdCap hOldEF hOldTarget
    (fun p => (hreturn.1 p).1) (fun p => (hreturn.1 p).2) hreturn.2.1 hbench houtBench hreturn.2.2.2
  have hEF : ∀ i j : enlarged, value i.val (growth.assigned j) (returned.point (growth.assigned j)) ≤
      value i.val (growth.assigned i) (returned.point (growth.assigned i)) :=
    fun i j => hbest i (growth.assigned j)
  obtain ⟨hvalid, _, hown, hEF', hunused⟩ := refresh_inherited enlarged growth.assigned value feasible
    returned.point (table.remainingCap selected) (table.remainingCap enlarged)
    (fun p => (hreturn.1 p).1) (fun p => (table.cap_feasible hwhole enlarged p).1)
    (fun p => (hreturn.1 p).2) (fun p => table.cap_mono hwhole selected enlarged (Finset.subset_insert _ _) p) hEF
  refine ⟨hvalid, ?_, hEF', hunused⟩
  intro i
  change target i.val ≤ value i.val (growth.assigned i)
    (refreshUnused enlarged growth.assigned returned.point (table.remainingCap enlarged) (growth.assigned i))
  rw [hown i]
  exact (htargetBench i.val).trans (hnewBench i)

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
    (hmono : ∀ i p, MonotoneOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) :
    Inherited table (initialLoopState table.erase hne preferred) ∧
      (initialLoopState table.erase hne preferred).selected.card ≤ Fintype.card Parent := by
  let selected := table.selected hne preferred
  let assigned := table.assigned hne preferred
  let winners := fun p => table.point (table.winner hne preferred p) p
  obtain ⟨hcard, hown, hEF⟩ := table.initial_selection_correct hmono hwhole hne preferred
  have hfeasible : ∀ p, winners p ∈ feasible p :=
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
    ∀ i : (initialLoopState table.erase hne preferred).selected,
      ownValue _ (initialLoopState table.erase hne preferred).node value i = target i.val := by
  intro i
  change ↥(table.selected hne preferred) at i
  change value i.val (table.assigned hne preferred i)
    (refreshUnused _ (table.assigned hne preferred) (fun p => table.point (table.winner hne preferred p) p)
      (table.remainingCap (table.selected hne preferred)) (table.assigned hne preferred i)) = target i.val
  rw [refreshUnused_assigned]
  have h := (table.point_spec _ (table.assigned hne preferred i)
    (table.winner_spec hne preferred (table.assigned hne preferred i)).1).2.2
  simpa only [table.assigned_winner hne preferred i] using h

theorem inherited_full_best (table : TrimTable value feasible whole target) (s : LoopState Agent Parent Coord)
    (h : Inherited table s) (hfull : s.selected.card = Fintype.card Parent) :
    ∀ i : s.selected, ∀ p, value i.val p (s.node.point p) ≤ ownValue s.selected s.node value i := by
  have hsurj : Function.Surjective s.node.assigned := by
    by_contra hs
    have hlt := Fintype.card_lt_of_injective_not_surjective s.node.assigned s.node.assigned.injective hs
    simp only [Fintype.card_coe, hfull, lt_self_iff_false] at hlt
  intro i p
  obtain ⟨j, rfl⟩ := hsurj p
  exact h.2.2.1 i j

end EnvyFreeResearch.Full.Chores.SubCore.Local
