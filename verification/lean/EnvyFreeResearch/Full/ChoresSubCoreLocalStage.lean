import EnvyFreeResearch.Full.ChoresSubCoreLocalAllocation

/-! The exact source finishStage function satisfies all allocation conclusions
using strictness only within each parent's retained record domain. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore.Local
open Set
variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]

theorem finishStage_correct
    (value : Agent → Parent → Coord → Value) (feasible : Parent → Set Coord) (whole : Parent → Coord)
    (hmono : ∀ i p, MonotoneOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (processed : Finset Agent) (oldAssignment : processed ↪ Parent)
    (hcard : processed.card < Fintype.card Parent) (hstage : processed.card + 1 = Fintype.card Agent)
    (benchmark : Agent → Value)
    (table : TrimTable (fun i (p : contestedParents processed oldAssignment) => value i p.val)
      (fun p => feasible p.val) (fun p => whole p.val)
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
  have hpoint : ∀ q, (liftNode out.selected contested out.node whole).point q ∈ feasible q ∧
      (liftNode out.selected contested out.node whole).point q ≤ whole q := by
    intro q
    change extendPoint contested out.node.point whole q ∈ feasible q ∧ extendPoint contested out.node.point whole q ≤ whole q
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

end EnvyFreeResearch.Full.Chores.SubCore.Local
