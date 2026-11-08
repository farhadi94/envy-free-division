import EnvyFreeResearch.Full.ChoresSubCoreAllocation

/-!
# The final data operation of a contested SubCore stage

The completed selected matching is lifted from the contested parents to the
original offered parents. The unique outside agent receives her computed
favorite uncontested whole. All comparisons and the whole-parent guarantee
are derived from the loop invariant and the inherited-owner necessity.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set

variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]

def extendPoint (contested : Finset Parent) (point : contested → Coord) (whole : Parent → Coord) (p : Parent) : Coord :=
  if hp : p ∈ contested then point ⟨p, hp⟩ else whole p

theorem extendPoint_inside (contested : Finset Parent) (point : contested → Coord) (whole : Parent → Coord)
    (p : contested) : extendPoint contested point whole p.val = point p := by
  simp only [extendPoint, dite_eq_left p.property]

theorem extendPoint_outside (contested : Finset Parent) (point : contested → Coord) (whole : Parent → Coord)
    (p : Parent) (hp : p ∉ contested) : extendPoint contested point whole p = whole p := by
  simp only [extendPoint, dite_eq_right hp]

def liftNode (selected : Finset Agent) (contested : Finset Parent) (node : Node selected contested Coord)
    (whole : Parent → Coord) : Node selected Parent Coord :=
  ⟨node.assigned.trans ⟨Subtype.val, Subtype.val_injective⟩, extendPoint contested node.point whole⟩

theorem liftNode_own (selected : Finset Agent) (contested : Finset Parent) (node : Node selected contested Coord)
    (whole : Parent → Coord) (value : Agent → Parent → Coord → Value) (i : selected) :
    ownValue selected (liftNode selected contested node whole) value i =
      ownValue selected node (fun i p => value i p.val) i := by
  exact congrArg (value i.val (node.assigned i).val) (extendPoint_inside contested node.point whole (node.assigned i))

theorem full_assignment_surjective (selected : Finset Agent) (contested : Finset Parent)
    (assigned : selected ↪ contested) (hfull : selected.card = Fintype.card contested) : Function.Surjective assigned := by
  by_contra hs
  have hlt := Fintype.card_lt_of_injective_not_surjective assigned assigned.injective hs
  simpa only [Fintype.card_coe, hfull, lt_self_iff_false] using hlt

theorem stage_last_count (processed : Finset Agent) (oldAssignment : processed ↪ Parent)
    (hstage : processed.card + 1 = Fintype.card Agent)
    (out : LoopState Agent (contestedParents processed oldAssignment) Coord)
    (hfull : out.selected.card = Fintype.card (contestedParents processed oldAssignment)) :
    out.selected.card + 1 = Fintype.card Agent := by
  rw [Fintype.card_coe, contestedParents_card] at hfull
  omega

theorem stage_favorite_free (processed : Finset Agent) (oldAssignment : processed ↪ Parent)
    (hcard : processed.card < Fintype.card Parent) (wholeValue : Agent → Parent → Value)
    (out : LoopState Agent (contestedParents processed oldAssignment) Coord)
    (whole : Parent → Coord) (i : Agent) :
    ∀ j, (liftNode out.selected _ out.node whole).assigned j ≠
      favoriteUncontested processed oldAssignment hcard wholeValue i := by
  intro j heq
  have hp := (favoriteUncontested_spec processed oldAssignment hcard wholeValue i).1
  have hnot : favoriteUncontested processed oldAssignment hcard wholeValue i ∉ contestedParents processed oldAssignment :=
    (Finset.mem_sdiff.mp hp).2
  exact hnot (heq ▸ (out.node.assigned j).property)

def finishStage (processed : Finset Agent) (oldAssignment : processed ↪ Parent)
    (hcard : processed.card < Fintype.card Parent) (hstage : processed.card + 1 = Fintype.card Agent)
    (value : Agent → Parent → Coord → Value) (whole : Parent → Coord)
    (out : LoopState Agent (contestedParents processed oldAssignment) Coord)
    (hfull : out.selected.card = Fintype.card (contestedParents processed oldAssignment)) : Allocation Agent Parent Coord :=
  let hc := stage_last_count processed oldAssignment hstage out hfull
  let i := lastAgent out.selected hc
  let p := favoriteUncontested processed oldAssignment hcard (fun i p => value i p (whole p)) i
  completeNode out.selected (liftNode out.selected _ out.node whole) i p (lastAgent_outside out.selected hc) hc
    (stage_favorite_free processed oldAssignment hcard (fun i p => value i p (whole p)) out whole i)

theorem finishStage_correct
    (value : Agent → Parent → Coord → Value) (feasible : Set Coord) (whole : Parent → Coord)
    (hmono : ∀ i p, MonotoneOn (value i p) feasible) (hwhole : ∀ p, whole p ∈ feasible)
    (processed : Finset Agent) (oldAssignment : processed ↪ Parent)
    (hcard : processed.card < Fintype.card Parent) (hstage : processed.card + 1 = Fintype.card Agent)
    (benchmark : Agent → Value)
    (table : TrimTable (fun i (p : contestedParents processed oldAssignment) => value i p.val)
      feasible (fun p => whole p.val)
      (stageTarget processed oldAssignment hcard (fun i p => value i p (whole p)) benchmark))
    (out : LoopState Agent (contestedParents processed oldAssignment) Coord)
    (hout : Inherited table out)
    (hfull : out.selected.card = Fintype.card (contestedParents processed oldAssignment))
    (hforced : ∀ i, value i (favoriteUncontested processed oldAssignment hcard (fun i p => value i p (whole p)) i)
      (whole (favoriteUncontested processed oldAssignment hcard (fun i p => value i p (whole p)) i)) < benchmark i → i ∈ out.selected) :
    AllocationCorrect value feasible whole benchmark
      (finishStage processed oldAssignment hcard hstage value whole out hfull) := by
  let contested := contestedParents processed oldAssignment
  let target := stageTarget processed oldAssignment hcard (fun i p => value i p (whole p)) benchmark
  let hc := stage_last_count processed oldAssignment hstage out hfull
  let i := lastAgent out.selected hc
  let p := favoriteUncontested processed oldAssignment hcard (fun i p => value i p (whole p)) i
  have hi : i ∉ out.selected := lastAgent_outside out.selected hc
  have hp : p ∉ contested := (Finset.mem_sdiff.mp
    (favoriteUncontested_spec processed oldAssignment hcard (fun i p => value i p (whole p)) i).1).2
  have htarget : target i = value i p (whole p) := outside_target_is_whole processed oldAssignment hcard
    (fun i p => value i p (whole p)) benchmark out.selected i hi hforced
  have hbestC := inherited_full_best table out hout hfull
  have hpoint : ∀ q, (liftNode out.selected contested out.node whole).point q ∈ feasible ∧
      (liftNode out.selected contested out.node whole).point q ≤ whole q := by
    intro q
    change extendPoint contested out.node.point whole q ∈ feasible ∧ extendPoint contested out.node.point whole q ≤ whole q
    by_cases hq : q ∈ contested
    · rw [show extendPoint contested out.node.point whole q = out.node.point ⟨q, hq⟩ from
        extendPoint_inside contested out.node.point whole ⟨q, hq⟩]
      exact ⟨(hout.1 ⟨q, hq⟩).1, (hout.1 ⟨q, hq⟩).2.trans (table.cap_feasible (fun q => hwhole q.val) out.selected ⟨q, hq⟩).2⟩
    · rw [extendPoint_outside contested out.node.point whole q hq]
      exact ⟨hwhole q, le_rfl⟩
  have hbest : ∀ j : out.selected, ∀ q, value j.val q ((liftNode out.selected contested out.node whole).point q) ≤
      ownValue out.selected (liftNode out.selected contested out.node whole) value j := by
    intro j q
    rw [liftNode_own]
    change value j.val q (extendPoint contested out.node.point whole q) ≤ _
    by_cases hq : q ∈ contested
    · rw [show extendPoint contested out.node.point whole q = out.node.point ⟨q, hq⟩ from
        extendPoint_inside contested out.node.point whole ⟨q, hq⟩]
      exact hbestC j ⟨q, hq⟩
    · rw [extendPoint_outside contested out.node.point whole q hq]
      exact (stageTarget_whole processed oldAssignment hcard (fun i p => value i p (whole p)) benchmark j.val q
        (by simp only [uncontestedParents, Finset.mem_sdiff, Finset.mem_univ, true_and]; exact hq)).trans (hout.2.1 j)
  have hbench : ∀ j : out.selected, benchmark j.val ≤ ownValue out.selected (liftNode out.selected contested out.node whole) value j := by
    intro j
    rw [liftNode_own]
    exact (stageTarget_benchmark processed oldAssignment hcard (fun i p => value i p (whole p)) benchmark j.val).trans (hout.2.1 j)
  have hunused : ∀ q, (∀ j, (liftNode out.selected contested out.node whole).assigned j ≠ q) →
      (liftNode out.selected contested out.node whole).point q = whole q := by
    intro q hq
    apply extendPoint_outside
    intro hm
    obtain ⟨j, hj⟩ := full_assignment_surjective out.selected contested out.node.assigned hfull ⟨q, hm⟩
    exact hq j (congrArg (fun r : contested => r.val) hj)
  have hnew : ∀ q, value i q ((liftNode out.selected contested out.node whole).point q) ≤
      value i p ((liftNode out.selected contested out.node whole).point p) := by
    intro q
    change value i q (extendPoint contested out.node.point whole q) ≤ value i p (extendPoint contested out.node.point whole p)
    rw [extendPoint_outside contested out.node.point whole p hp, ← htarget]
    by_cases hq : q ∈ contested
    · rw [show extendPoint contested out.node.point whole q = out.node.point ⟨q, hq⟩ from
        extendPoint_inside contested out.node.point whole ⟨q, hq⟩]
      exact ((hmono i q) (hout.1 ⟨q, hq⟩).1 (table.cap_feasible (fun q => hwhole q.val) out.selected ⟨q, hq⟩).1
        (hout.1 ⟨q, hq⟩).2).trans (table.outside_cap_value (fun i q => hmono i q.val)
          (fun q => hwhole q.val) out.selected i hi ⟨q, hq⟩)
    · rw [extendPoint_outside contested out.node.point whole q hq]
      exact stageTarget_whole processed oldAssignment hcard (fun i p => value i p (whole p)) benchmark i q
        (by simp only [uncontestedParents, Finset.mem_sdiff, Finset.mem_univ, true_and]; exact hq)
  have hnewBench : benchmark i ≤ value i p ((liftNode out.selected contested out.node whole).point p) := by
    change benchmark i ≤ value i p (extendPoint contested out.node.point whole p)
    rw [extendPoint_outside contested out.node.point whole p hp, ← htarget]
    exact stageTarget_benchmark processed oldAssignment hcard (fun i p => value i p (whole p)) benchmark i
  exact completeNode_correct out.selected (liftNode out.selected contested out.node whole) i p hi hc
    (stage_favorite_free processed oldAssignment hcard (fun i p => value i p (whole p)) out whole i)
    value feasible whole benchmark hpoint hbest hbench hunused hnew hnewBench

end EnvyFreeResearch.Full.Chores.SubCore
