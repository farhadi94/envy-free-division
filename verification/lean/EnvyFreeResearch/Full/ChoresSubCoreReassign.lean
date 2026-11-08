import EnvyFreeResearch.Full.ChoresSubCoreOwnerPath

/-!
# The closed equal-value-chain transition

The finite path is constructed from the old and current assignments. All
record equalities are derived from strict within-parent value order, old EF,
current EF and the unused-parent guarantee. The resulting reassignment keeps
every physical suffix record and benchmark, and frees a parent whose old
owner remains outside the selected set.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set

variable {Agent Parent : Type*}

def OwnerPath.at {selected : Finset Agent} {oldOwner : Parent ↪ Agent}
    {assigned : selected ↪ Parent} {start : Parent}
    (path : OwnerPath selected oldOwner assigned start) (r : ℕ) : Parent :=
  path.parents ⟨min r path.length, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma OwnerPath.at_castSucc {selected : Finset Agent} {oldOwner : Parent ↪ Agent}
    {assigned : selected ↪ Parent} {start : Parent}
    (path : OwnerPath selected oldOwner assigned start) (r : Fin path.length) :
    path.at r.val = path.parents r.castSucc := by
  apply congrArg path.parents
  apply Fin.ext
  exact min_eq_left (Nat.le_of_lt r.isLt)

lemma OwnerPath.at_succ {selected : Finset Agent} {oldOwner : Parent ↪ Agent}
    {assigned : selected ↪ Parent} {start : Parent}
    (path : OwnerPath selected oldOwner assigned start) (r : Fin path.length) :
    path.at (r.val + 1) = path.parents r.succ := by
  apply congrArg path.parents
  apply Fin.ext
  exact min_eq_left r.isLt

lemma OwnerPath.at_zero {selected : Finset Agent} {oldOwner : Parent ↪ Agent}
    {assigned : selected ↪ Parent} {start : Parent}
    (path : OwnerPath selected oldOwner assigned start) : path.at 0 = start := by
  change path.parents ⟨min 0 path.length, _⟩ = start
  exact path.first

lemma OwnerPath.at_last {selected : Finset Agent} {oldOwner : Parent ↪ Agent}
    {assigned : selected ↪ Parent} {start : Parent}
    (path : OwnerPath selected oldOwner assigned start) : path.at path.length = path.parents (Fin.last path.length) := by
  apply congrArg path.parents
  apply Fin.ext
  exact min_self _

variable [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent]
    {Coord Value : Type*} [LinearOrder Coord] [LinearOrder Value]

omit [Fintype Agent] in
/-- The complete source equal-value-chain operation. All equalities needed by
the physical ownership rotation are conclusions, not premises. -/
theorem path_reassignment_correct (selected : Finset Agent) (oldOwner : Parent ↪ Agent)
    (assigned : selected ↪ Parent) (start : Parent)
    (hfree : ∀ i, assigned i ≠ start) (path : OwnerPath selected oldOwner assigned start)
    (value : Agent → Parent → Coord → Value) (feasible : Set Coord)
    (hstrict : ∀ i p, StrictMonoOn (value i p) feasible)
    (old state cap : Parent → Coord) (benchmark : selected → Value)
    (hold : ∀ p, old p ∈ feasible) (hstate : ∀ p, state p ∈ feasible) (hcap : ∀ p, cap p ∈ feasible)
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

omit [Fintype Agent] in
/-- The complete source equal-value-chain operation. All equalities needed by
the physical ownership rotation are conclusions, not premises. -/
theorem equal_value_reassignment (selected : Finset Agent) (oldOwner : Parent ↪ Agent)
    (assigned : selected ↪ Parent) (start : Parent)
    (hselected : oldOwner start ∈ selected) (hfree : ∀ i, assigned i ≠ start)
    (value : Agent → Parent → Coord → Value) (feasible : Set Coord)
    (hstrict : ∀ i p, StrictMonoOn (value i p) feasible)
    (old state cap : Parent → Coord) (benchmark : selected → Value)
    (hold : ∀ p, old p ∈ feasible) (hstate : ∀ p, state p ∈ feasible) (hcap : ∀ p, cap p ∈ feasible)
    (hinside : ∀ p, state p ≤ cap p) (hstart : old start ≤ cap start)
    (houtside : ∀ p, oldOwner p ∉ selected → cap p ≤ old p)
    (hOldEF : ∀ p q, value (oldOwner p) q (old q) ≤ value (oldOwner p) p (old p))
    (hbest : ∀ i : selected, ∀ p, value i.val p (state p) ≤ value i.val (assigned i) (state (assigned i)))
    (hbenchmark : ∀ i : selected, benchmark i ≤ value i.val (assigned i) (state (assigned i)))
    (hwhole : ∀ p, (∀ i, assigned i ≠ p) → state p = cap p) :
    ∃ newAssignment : selected ↪ Parent, ∃ freed : Parent,
      (∀ i : selected, ∀ p, value i.val p (state p) ≤ value i.val (newAssignment i) (state (newAssignment i))) ∧
      (∀ i : selected, benchmark i ≤ value i.val (newAssignment i) (state (newAssignment i))) ∧
      (∀ p, (∀ i, newAssignment i ≠ p) → state p = cap p) ∧
      (∃ i, newAssignment i = start) ∧ (∀ i, newAssignment i ≠ freed) ∧ oldOwner freed ∉ selected := by
  obtain ⟨path⟩ := exists_owner_path selected oldOwner assigned start hselected hfree
  exact ⟨path.reassigned hfree, path.parents (Fin.last path.length),
    path_reassignment_correct selected oldOwner assigned start hfree path value feasible hstrict
      old state cap benchmark hold hstate hcap hinside hstart houtside hOldEF hbest hbenchmark hwhole⟩

end EnvyFreeResearch.Full.Chores.SubCore
