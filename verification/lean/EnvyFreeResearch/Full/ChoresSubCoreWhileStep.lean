import EnvyFreeResearch.Full.ChoresSubCoreCaps
import EnvyFreeResearch.Full.ChoresSubCoreGrowth

/-!
# The closed SubCore while-loop growth step

After a smaller recursive call, an unused parent exists by cardinality. If
it has no remaining trim, the proved owner chain frees a parent that does.
An actual outside minimum trimmer then receives that cached whole suffix.
This step strictly grows the selected set and makes no additional query.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set Function

variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]

theorem grow_after_recursive
    (value : Agent → Parent → Coord → Value) (feasible : Set Coord)
    (whole : Parent → Coord) (target benchmark : Agent → Value)
    (table : TrimTable value feasible whole target)
    (hstrict : ∀ i p, StrictMonoOn (value i p) feasible) (hwhole : ∀ p, whole p ∈ feasible)
    (oldOwner : Parent ↪ Agent) (old : Parent → Coord)
    (hold : ∀ p, old p ∈ feasible) (holdCap : ∀ p, old p ≤ whole p)
    (hOldEF : ∀ p q, value (oldOwner p) q (old q) ≤ value (oldOwner p) p (old p))
    (hOldTarget : ∀ p, target (oldOwner p) ≤ value (oldOwner p) p (old p))
    (selected : Finset Agent) (hcard : selected.card < Fintype.card Parent)
    (assigned : selected ↪ Parent) (state : Parent → Coord)
    (hstate : ∀ p, state p ∈ feasible)
    (hinside : ∀ p, state p ≤ table.remainingCap selected p)
    (hbest : ∀ i : selected, ∀ p, value i.val p (state p) ≤ value i.val (assigned i) (state (assigned i)))
    (hbenchmark : ∀ i : selected, benchmark i.val ≤ value i.val (assigned i) (state (assigned i)))
    (houtBenchmark : ∀ i, i ∉ selected → benchmark i ≤ target i)
    (hunused : ∀ p, (∀ i, assigned i ≠ p) → state p = table.remainingCap selected p) :
    ∃ i : Agent, i ∉ selected ∧ ∃ newAssignment : ↑(insert i selected) ↪ Parent,
      (insert i selected).card = selected.card + 1 ∧
      (∀ j : ↑(insert i selected), ∀ p, value j.val p (state p) ≤
        value j.val (newAssignment j) (state (newAssignment j))) ∧
      (∀ j : ↑(insert i selected), benchmark j.val ≤ value j.val (newAssignment j) (state (newAssignment j))) ∧
      (∀ p, (∀ j, newAssignment j ≠ p) → state p = table.remainingCap selected p) := by
  classical
  have hexUnused : ∃ p : Parent, ∀ i : selected, assigned i ≠ p := by
    by_contra h
    have hsurj : Surjective assigned := by
      intro p
      exact not_forall_not.mp (fun hp => h ⟨p, hp⟩)
    have hle := Fintype.card_le_of_surjective assigned hsurj
    simp only [Fintype.card_coe] at hle
    exact (not_le_of_gt hcard) hle
  obtain ⟨start, hfree⟩ := hexUnused
  have hready : ∃ ready : selected ↪ Parent, ∃ p : Parent,
      (∀ j, ready j ≠ p) ∧ (table.remaining selected p).Nonempty ∧
      (∀ j : selected, ∀ q, value j.val q (state q) ≤ value j.val (ready j) (state (ready j))) ∧
      (∀ j : selected, benchmark j.val ≤ value j.val (ready j) (state (ready j))) ∧
      (∀ q, (∀ j, ready j ≠ q) → state q = table.remainingCap selected q) := by
    by_cases htrim : (table.remaining selected start).Nonempty
    · exact ⟨assigned, start, hfree, htrim, hbest, hbenchmark, hunused⟩
    · have hselected : oldOwner start ∈ selected := by
        by_contra hout
        exact htrim (table.outside_old_owner hstrict hwhole selected (oldOwner start) start (old start)
          hout (hold start) (holdCap start) (hOldTarget start)).1
      have hstart : old start ≤ table.remainingCap selected start := by
        rw [table.cap_whole_of_empty selected start htrim]
        exact holdCap start
      have hcap : ∀ p, table.remainingCap selected p ∈ feasible :=
        fun p => (table.cap_feasible hwhole selected p).1
      have houtside : ∀ p, oldOwner p ∉ selected → table.remainingCap selected p ≤ old p :=
        fun p hp => (table.outside_old_owner hstrict hwhole selected (oldOwner p) p (old p)
          hp (hold p) (holdCap p) (hOldTarget p)).2
      obtain ⟨ready, freed, hbest', hbench', hwhole', _, hfree', hout⟩ :=
        equal_value_reassignment selected oldOwner assigned start hselected hfree value feasible hstrict
          old state (table.remainingCap selected) (fun i => benchmark i.val) hold hstate hcap hinside
          hstart houtside hOldEF hbest hbenchmark hunused
      have htrim' := (table.outside_old_owner hstrict hwhole selected (oldOwner freed) freed (old freed)
        hout (hold freed) (holdCap freed) (hOldTarget freed)).1
      exact ⟨ready, freed, hfree', htrim', hbest', hbench', hwhole'⟩
  obtain ⟨ready, p, hfree', htrim, hbest', hbench', hwhole'⟩ := hready
  obtain ⟨i, _, hout, _, htarget⟩ := table.cap_attained selected p htrim
  have hvalue : value i p (state p) = target i := by
    rw [hwhole' p hfree']
    exact htarget
  have hnew : ∀ q, value i q (state q) ≤ value i p (state p) := by
    intro q
    rw [hvalue]
    exact ((hstrict i q).monotoneOn (hstate q) (table.cap_feasible hwhole selected q).1 (hinside q)).trans
      (table.outside_cap_value (fun j q => (hstrict j q).monotoneOn) hwhole selected i hout q)
  have hnewBenchmark : benchmark i ≤ value i p (state p) := by
    rw [hvalue]
    exact houtBenchmark i hout
  obtain ⟨hsize, hbest'', hbench'', hwhole'', _⟩ :=
    grow_selected selected ready i p hout hfree' value state (table.remainingCap selected) benchmark
      hbest' hbench' hwhole' hnew hnewBenchmark
  exact ⟨i, hout, insertedAssignment selected ready i p hfree', hsize, hbest'', hbench'', hwhole''⟩

end EnvyFreeResearch.Full.Chores.SubCore
