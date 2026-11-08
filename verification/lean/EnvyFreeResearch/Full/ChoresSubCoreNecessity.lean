import EnvyFreeResearch.Full.ChoresSubCoreInitial

/-!
# Inherited-owner necessity for the actual contested-stage data

The preferred trimmer is obtained from the inherited injective assignment.
An agent whose inherited benchmark exceeds every uncontested whole is then
selected by the concrete initial winner matching. No selection premise is
assumed for that agent.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set QueryProgram

variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]

def inheritedPreferred (inherited : Agent ↪ Parent) (p : Parent) : Option Agent :=
  if h : ∃ i, inherited i = p then some (Classical.choose h) else none

theorem inheritedPreferred_own (inherited : Agent ↪ Parent) (i : Agent) :
    inheritedPreferred inherited (inherited i) = some i := by
  have hex : ∃ j, inherited j = inherited i := ⟨i, rfl⟩
  unfold inheritedPreferred
  rw [dite_eq_left hex]
  exact congrArg some (inherited.injective (Classical.choose_spec hex))

theorem high_benchmark_initial_selected
    (value : Agent → Parent → Coord → Value) (feasible : Set Coord) (whole : Parent → Coord)
    (hstrict : ∀ i p, StrictMonoOn (value i p) feasible) (hwhole : ∀ p, whole p ∈ feasible)
    (processed : Finset Agent) (oldAssignment : processed ↪ Parent)
    (hcard : processed.card < Fintype.card Parent)
    (inherited : Agent ↪ Parent) (inheritedPoint : Parent → Coord) (benchmark : Agent → Value)
    (hpoint : ∀ i, inheritedPoint (inherited i) ∈ feasible)
    (hcap : ∀ i, inheritedPoint (inherited i) ≤ whole (inherited i))
    (hbenchmark : ∀ i, value i (inherited i) (inheritedPoint (inherited i)) = benchmark i)
    (hEF : ∀ i j, value i (inherited j) (inheritedPoint (inherited j)) ≤ benchmark i)
    (table : TrimTable (fun i (p : contestedParents processed oldAssignment) => value i p.val)
      feasible (fun p => whole p.val)
      (stageTarget processed oldAssignment hcard (fun i p => value i p (whole p)) benchmark))
    (hne : ∀ p, (table.available p).Nonempty)
    (i : Agent)
    (hhigh : value i (favoriteUncontested processed oldAssignment hcard (fun i p => value i p (whole p)) i)
      (whole (favoriteUncontested processed oldAssignment hcard (fun i p => value i p (whole p)) i)) < benchmark i) :
    i ∈ (initialLoopState table hne (fun p => inheritedPreferred inherited p.val)).selected := by
  letI : Nonempty Parent := Fintype.card_pos_iff.mp (lt_of_le_of_lt (Nat.zero_le _) hcard)
  have hall : ∀ p ∈ uncontestedParents processed oldAssignment,
      value i p (whole p) < benchmark i := fun p hp =>
    ((favoriteUncontested_spec processed oldAssignment hcard (fun i p => value i p (whole p)) i).2 p hp).trans_lt hhigh
  have hc : inherited i ∈ contestedParents processed oldAssignment :=
    inherited_parent_contested value feasible whole (fun i p => (hstrict i p).monotoneOn) hwhole
      (contestedParents processed oldAssignment) i (inherited i) (inheritedPoint (inherited i))
      (hpoint i) (hcap i) (benchmark i) (hbenchmark i).symm (fun p hp =>
        hall p (by simp only [uncontestedParents, Finset.mem_sdiff, Finset.mem_univ, true_and]; exact hp))
  let p : contestedParents processed oldAssignment := ⟨inherited i, hc⟩
  have htarget : stageTarget processed oldAssignment hcard (fun i p => value i p (whole p)) benchmark i = benchmark i :=
    high_benchmark_target processed oldAssignment hcard (fun i p => value i p (whole p)) benchmark i hall
  have hw := table.inherited_owner_selected (fun j q => hstrict j q.val) (fun q => hwhole q.val) hne
    (fun q => inheritedPreferred inherited q.val) i p (inheritedPoint (inherited i)) (hpoint i) (hcap i)
    ((hbenchmark i).trans htarget.symm)
    (fun j => (hEF j i).trans (stageTarget_benchmark processed oldAssignment hcard
      (fun i p => value i p (whole p)) benchmark j)) (inheritedPreferred_own inherited i)
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hw⟩

/-- Every old tentative owner really has an eligible trim on her own
contested parent; hence the actual initial trim table has no empty column. -/
theorem contested_owner_eligible
    (value : Agent → Parent → Coord → Value) (feasible : Set Coord) (whole : Parent → Coord)
    (hmono : ∀ i p, MonotoneOn (value i p) feasible) (hwhole : ∀ p, whole p ∈ feasible)
    (processed : Finset Agent) (old : Node processed Parent Coord)
    (hcard : processed.card < Fintype.card Parent) (benchmark : Agent → Value)
    (hpoint : ∀ p, old.point p ∈ feasible) (hcap : ∀ p, old.point p ≤ whole p)
    (hbest : ∀ i : processed, ∀ p, value i.val p (old.point p) ≤ ownValue processed old value i)
    (hbench : ∀ i : processed, benchmark i.val ≤ ownValue processed old value i)
    (hunused : ∀ p, (∀ i, old.assigned i ≠ p) → old.point p = whole p)
    (table : TrimTable (fun i (p : contestedParents processed old.assigned) => value i p.val)
      feasible (fun p => whole p.val)
      (stageTarget processed old.assigned hcard (fun i p => value i p (whole p)) benchmark)) :
    ∀ p, contestedOwner processed old.assigned p ∈ table.available p := by
  intro p
  let i : processed := ⟨contestedOwner processed old.assigned p, contestedOwner_mem processed old.assigned p⟩
  have hp : old.assigned i = p.val := contestedOwner_parent processed old.assigned p
  apply table.eligible_of_old_value (fun i p => hmono i p.val) (fun p => hwhole p.val)
    i.val p (old.point p.val) (hpoint p.val) (hcap p.val)
  have ht := old_own_meets_target processed old.assigned hcard (fun i p => value i p (whole p))
    benchmark (fun j => if hj : j ∈ processed then ownValue processed old value ⟨j, hj⟩ else benchmark j)
    (fun j => by simpa only [dite_eq_left j.property] using hbench j)
    (fun j q hq => by
      have heq := hunused q ((mem_uncontestedParents processed old.assigned q).mp hq)
      simpa only [dite_eq_left j.property, heq] using hbest j q) i
  simpa only [dite_eq_left i.property, ownValue, hp] using ht

/-- The selected-set loop never drops an already selected owner. This is a
property of its actual execution, independently of semantic correctness. -/
theorem loop_selected_mono {Query Reply : Type*}
    {value : Agent → Parent → Coord → Value} {feasible : Set Coord}
    {whole : Parent → Coord} {target : Agent → Value}
    (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p)
    (recurse : ∀ selected : Finset Agent, Node selected Parent Coord → Program Query Reply (Node selected Parent Coord))
    (oracle : AdaptiveOracle.Policy Query Reply) (fuel : ℕ) (s out : LoopState Agent Parent Coord)
    (prior trace : OracleProtocol.History Query Reply)
    (hexec : Executes oracle (loopProgram table oldOwner hOwner recurse fuel s) prior out trace) :
    s.selected ⊆ out.selected := by
  induction fuel generalizing s prior trace with
  | zero =>
    by_cases hfull : s.selected.card = Fintype.card Parent
    · rw [loopProgram_full table oldOwner hOwner recurse 0 s hfull] at hexec
      cases hexec
      exact Finset.Subset.refl _
    · simp only [loopProgram, ite_eq_right hfull] at hexec
      cases hexec
  | succ fuel ih =>
    by_cases hfull : s.selected.card = Fintype.card Parent
    · rw [loopProgram_full table oldOwner hOwner recurse (fuel + 1) s hfull] at hexec
      cases hexec
      exact Finset.Subset.refl _
    · by_cases hcard : s.selected.card < Fintype.card Parent
      · rw [loopProgram, ite_eq_right hfull, dite_eq_left hcard] at hexec
        obtain ⟨returned, first, tail, _, htail, _⟩ := hexec.split_bind _ _
        exact (nextLoopState_contains table oldOwner hOwner s.selected hcard returned).trans
          (ih _ (prior ++ first) tail htail)
      · simp only [loopProgram, ite_eq_right hfull, dite_eq_right hcard] at hexec
        cases hexec

end EnvyFreeResearch.Full.Chores.SubCore
