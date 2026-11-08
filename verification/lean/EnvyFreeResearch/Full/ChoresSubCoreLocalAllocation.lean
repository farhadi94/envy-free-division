import EnvyFreeResearch.Full.ChoresSubCoreLocalState

/-! Allocation invariants and final insertion with separate parent domains. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore.Local
open Set
variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]

def AllocationCorrect (value : Agent → Parent → Coord → Value) (feasible : Parent → Set Coord)
    (whole : Parent → Coord) (benchmark : Agent → Value) (out : Allocation Agent Parent Coord) : Prop :=
  (∀ p, out.point p ∈ feasible p ∧ out.point p ≤ whole p) ∧
  (∀ i p, value i p (out.point p) ≤ value i (out.assigned i) (out.point (out.assigned i))) ∧
  (∀ i, benchmark i ≤ value i (out.assigned i) (out.point (out.assigned i))) ∧
  (∀ p, (∀ i, out.assigned i ≠ p) → out.point p = whole p) ∧
  (∃ i, out.point (out.assigned i) = whole (out.assigned i))

def InheritedAllocation (value : Agent → Parent → Coord → Value) (feasible : Parent → Set Coord)
    (whole : Parent → Coord) (benchmark : Agent → Value) (inherited : Allocation Agent Parent Coord) : Prop :=
  (∀ i, inherited.point (inherited.assigned i) ∈ feasible (inherited.assigned i) ∧ inherited.point (inherited.assigned i) ≤ whole (inherited.assigned i)) ∧
  (∀ i, value i (inherited.assigned i) (inherited.point (inherited.assigned i)) = benchmark i) ∧
  (∀ i j, value i (inherited.assigned j) (inherited.point (inherited.assigned j)) ≤ benchmark i)
theorem completeNode_correct (selected : Finset Agent) (node : Node selected Parent Coord)
    (i : Agent) (p : Parent) (hi : i ∉ selected)
    (hcard : selected.card + 1 = Fintype.card Agent) (hfree : ∀ j, node.assigned j ≠ p)
    (value : Agent → Parent → Coord → Value) (feasible : Parent → Set Coord)
    (whole : Parent → Coord) (benchmark : Agent → Value)
    (hpoint : ∀ p, node.point p ∈ feasible p ∧ node.point p ≤ whole p)
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

theorem inherited_parent_contested
    (value : Agent → Parent → Coord → Value) (feasible : Parent → Set Coord) (whole : Parent → Coord)
    (hmono : ∀ i p, MonotoneOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (contested : Finset Parent) (i : Agent) (p : Parent) (x : Coord)
    (hx : x ∈ feasible p) (hxcap : x ≤ whole p) (benchmark : Value)
    (hvalue : benchmark = value i p x)
    (hstrict : ∀ q, q ∉ contested → value i q (whole q) < benchmark) : p ∈ contested := by
  by_contra hp
  have hlarge : benchmark ≤ value i p (whole p) := hvalue.le.trans ((hmono i p) hx (hwhole p) hxcap)
  exact (not_lt_of_ge hlarge) (hstrict p hp)

theorem high_benchmark_initial_selected
    (value : Agent → Parent → Coord → Value) (feasible : Parent → Set Coord) (whole : Parent → Coord)
    (hstrict : ∀ i p, StrictMonoOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (processed : Finset Agent) (oldAssignment : processed ↪ Parent)
    (hcard : processed.card < Fintype.card Parent)
    (inherited : Agent ↪ Parent) (inheritedPoint : Parent → Coord) (benchmark : Agent → Value)
    (hpoint : ∀ i, inheritedPoint (inherited i) ∈ feasible (inherited i))
    (hcap : ∀ i, inheritedPoint (inherited i) ≤ whole (inherited i))
    (hbenchmark : ∀ i, value i (inherited i) (inheritedPoint (inherited i)) = benchmark i)
    (hEF : ∀ i j, value i (inherited j) (inheritedPoint (inherited j)) ≤ benchmark i)
    (table : TrimTable (fun i (p : contestedParents processed oldAssignment) => value i p.val)
      (fun p => feasible p.val) (fun p => whole p.val)
      (stageTarget processed oldAssignment hcard (fun i p => value i p (whole p)) benchmark))
    (hne : ∀ p, (table.available p).Nonempty)
    (i : Agent)
    (hhigh : value i (favoriteUncontested processed oldAssignment hcard (fun i p => value i p (whole p)) i)
      (whole (favoriteUncontested processed oldAssignment hcard (fun i p => value i p (whole p)) i)) < benchmark i) :
    i ∈ (initialLoopState table.erase hne (fun p => inheritedPreferred inherited p.val)).selected := by
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
    (value : Agent → Parent → Coord → Value) (feasible : Parent → Set Coord) (whole : Parent → Coord)
    (hmono : ∀ i p, MonotoneOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (processed : Finset Agent) (old : Node processed Parent Coord)
    (hcard : processed.card < Fintype.card Parent) (benchmark : Agent → Value)
    (hpoint : ∀ p, old.point p ∈ feasible p) (hcap : ∀ p, old.point p ≤ whole p)
    (hbest : ∀ i : processed, ∀ p, value i.val p (old.point p) ≤ ownValue processed old value i)
    (hbench : ∀ i : processed, benchmark i.val ≤ ownValue processed old value i)
    (hunused : ∀ p, (∀ i, old.assigned i ≠ p) → old.point p = whole p)
    (table : TrimTable (fun i (p : contestedParents processed old.assigned) => value i p.val)
      (fun p => feasible p.val) (fun p => whole p.val)
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

end EnvyFreeResearch.Full.Chores.SubCore.Local
