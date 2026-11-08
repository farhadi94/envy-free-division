import EnvyFreeResearch.Full.ChoresSubCoreStage

/-! Parent-specific feasible domains for the exact source chain argument.
Only records of the same parent enter any strictness or injectivity step.
The ownership-path and rotation functions are the existing source functions. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore.Local
open Set
variable {Agent Parent Coord Value : Type*} [LinearOrder Coord] [LinearOrder Value]

theorem equal_value_chain (value : Agent → Parent → Coord → Value) (feasible : Parent → Set Coord)
    (hstrict : ∀ i p, StrictMonoOn (value i p) (feasible p))
    (h : ℕ) (hh : 0 < h) (agent : ℕ → Agent) (parent : ℕ → Parent)
    (old cap : Parent → Coord) (current : ℕ → Coord)
    (hold : ∀ r ≤ h, old (parent r) ∈ feasible (parent r))
    (hcap : ∀ r ≤ h, cap (parent r) ∈ feasible (parent r))
    (hcurrent : ∀ r < h, current r ∈ feasible (parent (r+1)))
    (hinside : ∀ r < h, current r ≤ cap (parent (r + 1)))
    (hstart : old (parent 0) ≤ cap (parent 0))
    (hlast : cap (parent h) ≤ old (parent h))
    (hOldEF : ∀ r < h, value (agent r) (parent (r + 1)) (old (parent (r + 1))) ≤
      value (agent r) (parent r) (old (parent r)))
    (hCurrentEF : ∀ r < h, ∀ s < h,
      value (agent r) (parent (s + 1)) (current s) ≤
        value (agent r) (parent (r + 1)) (current r))
    (hUnused : value (agent 0) (parent 0) (cap (parent 0)) ≤
      value (agent 0) (parent 1) (current 0)) :
    (∀ r < h, current r = old (parent (r + 1)) ∧
      value (agent r) (parent (r + 1)) (current r) = value (agent r) (parent r) (old (parent r))) ∧
    cap (parent 0) = old (parent 0) ∧ cap (parent h) = old (parent h) := by
  have backward : ∀ d r : ℕ, r + d = h → 0 < d → current r ≤ old (parent (r + 1)) := by
    intro d
    induction d with
    | zero => intro r heq hd; omega
    | succ d ih =>
      intro r heq hd
      have hr : r < h := by omega
      by_cases hz : d = 0
      · have hrh : r + 1 = h := by omega
        exact (hinside r hr).trans (hrh ▸ hlast)
      · have hr1 : r + 1 < h := by omega
        have hnext : current (r + 1) ≤ old (parent (r + 1 + 1)) := ih (r + 1) (by omega) (by omega)
        have hcompare := (hCurrentEF (r + 1) hr1 r hr).trans
          (((hstrict (agent (r + 1)) (parent (r + 1 + 1))).monotoneOn
            (hcurrent (r + 1) hr1) (hold (r + 1 + 1) (by omega)) hnext).trans (hOldEF (r + 1) hr1))
        exact ((hstrict (agent (r + 1)) (parent (r + 1))).le_iff_le
          (hcurrent r hr) (hold (r + 1) (by omega))).mp hcompare
  have hback : ∀ r < h, current r ≤ old (parent (r + 1)) :=
    fun r hr => backward (h - r) r (by omega) (by omega)
  have hupper : ∀ r < h, value (agent r) (parent (r + 1)) (current r) ≤
      value (agent r) (parent r) (old (parent r)) := by
    intro r hr
    exact ((hstrict (agent r) (parent (r + 1))).monotoneOn (hcurrent r hr)
      (hold (r + 1) (by omega)) (hback r hr)).trans (hOldEF r hr)
  have conclude : ∀ r < h,
      value (agent r) (parent r) (old (parent r)) ≤ value (agent r) (parent (r + 1)) (current r) →
      current r = old (parent (r + 1)) ∧
      value (agent r) (parent (r + 1)) (current r) = value (agent r) (parent r) (old (parent r)) := by
    intro r hr hlower
    have heq := le_antisymm ((hstrict (agent r) (parent (r + 1))).monotoneOn
      (hcurrent r hr) (hold (r + 1) (by omega)) (hback r hr)) ((hOldEF r hr).trans hlower)
    exact ⟨(hstrict (agent r) (parent (r + 1))).injOn (hcurrent r hr) (hold (r + 1) (by omega)) heq,
      le_antisymm (hupper r hr) hlower⟩
  have forward : ∀ r < h, current r = old (parent (r + 1)) ∧
      value (agent r) (parent (r + 1)) (current r) = value (agent r) (parent r) (old (parent r)) := by
    intro r
    induction r with
    | zero =>
      intro hr
      apply conclude 0 hr
      exact ((hstrict (agent 0) (parent 0)).monotoneOn (hold 0 (by omega))
        (hcap 0 (by omega)) hstart).trans hUnused
    | succ r ih =>
      intro hr
      obtain ⟨heq, _⟩ := ih (by omega)
      apply conclude (r + 1) hr
      have h := hCurrentEF (r + 1) hr r (by omega)
      simpa only [heq] using h
  refine ⟨forward, ?_, ?_⟩
  · apply le_antisymm ?_ hstart
    exact ((hstrict (agent 0) (parent 0)).le_iff_le (hcap 0 (by omega)) (hold 0 (by omega))).mp
      (hUnused.trans (forward 0 hh).2.le)
  · have hend := hinside (h - 1) (by omega)
    rw [(forward (h - 1) (by omega)).1, Nat.sub_add_cancel hh] at hend
    exact le_antisymm hlast hend

variable [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]

theorem path_reassignment_correct (selected : Finset Agent) (oldOwner : Parent ↪ Agent)
    (assigned : selected ↪ Parent) (start : Parent)
    (hfree : ∀ i, assigned i ≠ start) (path : OwnerPath selected oldOwner assigned start)
    (value : Agent → Parent → Coord → Value) (feasible : Parent → Set Coord)
    (hstrict : ∀ i p, StrictMonoOn (value i p) (feasible p))
    (old state cap : Parent → Coord) (benchmark : selected → Value)
    (hold : ∀ p, old p ∈ feasible p) (hstate : ∀ p, state p ∈ feasible p) (hcap : ∀ p, cap p ∈ feasible p)
    (hinside : ∀ p, state p ≤ cap p) (hstart : old start ≤ cap start)
    (houtside : ∀ p, oldOwner p ∉ selected → cap p ≤ old p)
    (hOldEF : ∀ p q, value (oldOwner p) q (old q) ≤ value (oldOwner p) p (old p))
    (hbest : ∀ i : selected, ∀ p, value i.val p (state p) ≤ value i.val (assigned i) (state (assigned i)))
    (hbenchmark : ∀ i : selected, benchmark i ≤ value i.val (assigned i) (state (assigned i)))
    (hwhole : ∀ p, (∀ i, assigned i ≠ p) → state p = cap p) :
    let newAssignment := path.reassigned hfree
    let freed := path.parents (Fin.last path.length)
    (∀ i : selected, ∀ p, value i.val p (state p) ≤ value i.val (newAssignment i) (state (newAssignment i))) ∧
    (∀ i : selected, benchmark i ≤ value i.val (newAssignment i) (state (newAssignment i))) ∧
    (∀ p, (∀ i, newAssignment i ≠ p) → state p = cap p) ∧
    (∃ i, newAssignment i = start) ∧ (∀ i, newAssignment i ≠ freed) ∧ oldOwner freed ∉ selected := by
  have howner : ∀ r (hr : r < path.length), oldOwner (path.at r) = (path.owners ⟨r, hr⟩).val := by
    intro r hr
    rw [path.at_castSucc ⟨r, hr⟩]
    exact path.oldOwner_eq _
  have hnext : ∀ r (hr : r < path.length), assigned (path.owners ⟨r, hr⟩) = path.at (r + 1) := by
    intro r hr
    rw [path.at_succ ⟨r, hr⟩]
    exact path.assigned_eq _
  have hstartState : state (path.at 0) = cap (path.at 0) := by
    rw [path.at_zero]
    exact hwhole start hfree
  have hCurrentEF : ∀ r < path.length, ∀ s < path.length,
      value (oldOwner (path.at r)) (path.at (s + 1)) (state (path.at (s + 1))) ≤
        value (oldOwner (path.at r)) (path.at (r + 1)) (state (path.at (r + 1))) := by
    intro r hr s _
    simpa only [hnext r hr, ← howner r hr] using hbest (path.owners ⟨r, hr⟩) (path.at (s + 1))
  have hUnused : value (oldOwner (path.at 0)) (path.at 0) (cap (path.at 0)) ≤
      value (oldOwner (path.at 0)) (path.at 1) (state (path.at 1)) := by
    have h := hbest (path.owners ⟨0, path.positive⟩) (path.at 0)
    simpa only [hnext 0 path.positive, ← howner 0 path.positive, hstartState] using h
  obtain ⟨hforward, hfirstEq, hlastEq⟩ := equal_value_chain value feasible hstrict path.length path.positive
    (fun r => oldOwner (path.at r)) path.at old cap (fun r => state (path.at (r + 1)))
    (fun r _ => hold _) (fun r _ => hcap _) (fun r _ => hstate _) (fun r _ => hinside _)
    (by simpa only [path.at_zero] using hstart)
    (by simpa only [path.at_last] using houtside _ path.last_outside)
    (fun r _ => hOldEF _ _) hCurrentEF hUnused
  have hpathState : ∀ r ≤ path.length, state (path.at r) = old (path.at r) := by
    intro r hr
    by_cases hz : r = 0
    · subst r
      exact hstartState.trans hfirstEq
    · have hprev : r - 1 < path.length := by omega
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using (hforward (r - 1) hprev).1
  have htie : ∀ r : Fin path.length,
      value (path.owners r).val (path.parents r.castSucc) (state (path.parents r.castSucc)) =
      value (path.owners r).val (path.parents r.succ) (state (path.parents r.succ)) := by
    intro r
    have h := (hforward r.val r.isLt).2.symm
    rw [← hpathState r.val (Nat.le_of_lt r.isLt)] at h
    simpa only [path.at_castSucc r, path.at_succ r, path.oldOwner_eq r] using h
  have hlastWhole : state (path.parents (Fin.last path.length)) = cap (path.parents (Fin.last path.length)) := by
    simpa only [path.at_last] using (hpathState path.length le_rfl).trans hlastEq.symm
  obtain ⟨hbest', hbench', hwhole', hfirst', hlast'⟩ := rotation_correct path.positive
    path.owners path.parents assigned path.assigned_eq (fun i => by simpa only [path.first] using hfree i)
    (fun i p x => value i.val p x) state cap benchmark hbest hbenchmark hwhole hlastWhole htie
  obtain ⟨i, hi⟩ := hfirst'
  exact ⟨hbest', hbench', hwhole',
    ⟨i, hi.trans path.first⟩, hlast', path.last_outside⟩

end EnvyFreeResearch.Full.Chores.SubCore.Local
