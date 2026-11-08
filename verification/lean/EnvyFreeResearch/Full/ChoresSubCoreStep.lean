import EnvyFreeResearch.Full.ChoresSubCoreRefresh

/-!
# The deterministic cached-data SubCore growth operator

The chosen free parent, optional rotation path, and outside trimmer are fixed
functions of the cached trim table and assignments. No fairness predicate is
used to choose an output. The semantic theorem separately proves that this
specific operation is the source algorithm's successful growth transition.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set Function

variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]
    {value : Agent → Parent → Coord → Value} {feasible : Set Coord}
    {whole : Parent → Coord} {target : Agent → Value}

lemma exists_free_parent (selected : Finset Agent) (hcard : selected.card < Fintype.card Parent)
    (assigned : selected ↪ Parent) : ∃ p : Parent, ∀ i, assigned i ≠ p := by
  classical
  by_contra h
  have hsurj : Surjective assigned := fun p => not_forall_not.mp (fun hp => h ⟨p, hp⟩)
  have hle := Fintype.card_le_of_surjective assigned hsurj
  simp only [Fintype.card_coe] at hle
  exact (not_le_of_gt hcard) hle

def freeParent (selected : Finset Agent) (hcard : selected.card < Fintype.card Parent)
    (assigned : selected ↪ Parent) : Parent := Classical.choose (exists_free_parent selected hcard assigned)

lemma freeParent_spec (selected : Finset Agent) (hcard : selected.card < Fintype.card Parent)
    (assigned : selected ↪ Parent) : ∀ i, assigned i ≠ freeParent selected hcard assigned :=
  Classical.choose_spec (exists_free_parent selected hcard assigned)

lemma selected_of_no_remaining (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (p : Parent) (htrim : ¬(table.remaining selected p).Nonempty) : oldOwner p ∈ selected := by
  by_contra hout
  exact htrim ⟨oldOwner p, Finset.mem_sdiff.mpr ⟨hOwner p, hout⟩⟩

def repairPath (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (assigned : selected ↪ Parent) (p : Parent) (hfree : ∀ i, assigned i ≠ p)
    (htrim : ¬(table.remaining selected p).Nonempty) : OwnerPath selected oldOwner assigned p :=
  Classical.choice (exists_owner_path selected oldOwner assigned p
    (selected_of_no_remaining table oldOwner hOwner selected p htrim) hfree)

structure Preparation (table : TrimTable value feasible whole target) (selected : Finset Agent) where
  assigned : selected ↪ Parent
  parent : Parent
  free : ∀ i, assigned i ≠ parent
  hasTrim : (table.remaining selected parent).Nonempty

def prepareFrom (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (assigned : selected ↪ Parent) (p : Parent) (hfree : ∀ i, assigned i ≠ p) : Preparation table selected := by
  classical
  exact if htrim : (table.remaining selected p).Nonempty then ⟨assigned, p, hfree, htrim⟩ else
    let path := repairPath table oldOwner hOwner selected assigned p hfree htrim
    ⟨path.reassigned hfree, path.parents (Fin.last path.length),
      (path.frees_remaining_owner hfree).2.1,
      ⟨oldOwner (path.parents (Fin.last path.length)), Finset.mem_sdiff.mpr
        ⟨hOwner _, path.last_outside⟩⟩⟩

def prepare (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (hcard : selected.card < Fintype.card Parent) (assigned : selected ↪ Parent) : Preparation table selected :=
  prepareFrom table oldOwner hOwner selected assigned (freeParent selected hcard assigned)
    (freeParent_spec selected hcard assigned)

theorem prepareFrom_correct (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (assigned : selected ↪ Parent) (p : Parent) (hfree : ∀ i, assigned i ≠ p)
    (hstrict : ∀ i q, StrictMonoOn (value i q) feasible) (hwhole : ∀ q, whole q ∈ feasible)
    (old state : Parent → Coord) (benchmark : Agent → Value)
    (hold : ∀ q, old q ∈ feasible) (holdCap : ∀ q, old q ≤ whole q)
    (hOldEF : ∀ q r, value (oldOwner q) r (old r) ≤ value (oldOwner q) q (old q))
    (hOldTarget : ∀ q, target (oldOwner q) ≤ value (oldOwner q) q (old q))
    (hstate : ∀ q, state q ∈ feasible) (hinside : ∀ q, state q ≤ table.remainingCap selected q)
    (hbest : ∀ i : selected, ∀ q, value i.val q (state q) ≤ value i.val (assigned i) (state (assigned i)))
    (hbenchmark : ∀ i : selected, benchmark i.val ≤ value i.val (assigned i) (state (assigned i)))
    (hunused : ∀ q, (∀ i, assigned i ≠ q) → state q = table.remainingCap selected q) :
    let out := prepareFrom table oldOwner hOwner selected assigned p hfree
    (∀ i : selected, ∀ q, value i.val q (state q) ≤ value i.val (out.assigned i) (state (out.assigned i))) ∧
    (∀ i : selected, benchmark i.val ≤ value i.val (out.assigned i) (state (out.assigned i))) ∧
    (∀ q, (∀ i, out.assigned i ≠ q) → state q = table.remainingCap selected q) := by
  classical
  unfold prepareFrom
  split_ifs with htrim
  · exact ⟨hbest, hbenchmark, hunused⟩
  · let path := repairPath table oldOwner hOwner selected assigned p hfree htrim
    have hstart : old p ≤ table.remainingCap selected p := by
      rw [table.cap_whole_of_empty selected p htrim]
      exact holdCap p
    have houtside : ∀ q, oldOwner q ∉ selected → table.remainingCap selected q ≤ old q :=
      fun q hq => (table.outside_old_owner hstrict hwhole selected (oldOwner q) q (old q)
        hq (hold q) (holdCap q) (hOldTarget q)).2
    obtain ⟨hb, hk, hw, _⟩ := path_reassignment_correct selected oldOwner assigned p hfree path value feasible hstrict
      old state (table.remainingCap selected) (fun i => benchmark i.val) hold hstate
      (fun q => (table.cap_feasible hwhole selected q).1) hinside hstart houtside hOldEF hbest hbenchmark hunused
    exact ⟨hb, hk, hw⟩

structure GrowthResult (selected : Finset Agent) (Parent : Type*) where
  entrant : Agent
  outside : entrant ∉ selected
  assigned : ↑(insert entrant selected) ↪ Parent

def growthStep (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (hcard : selected.card < Fintype.card Parent) (assigned : selected ↪ Parent) : GrowthResult selected Parent := by
  classical
  let out := prepare table oldOwner hOwner selected hcard assigned
  let entrant := minimumWinner (table.remaining selected out.parent) out.hasTrim (fun i => table.point i out.parent)
  have hmem : entrant ∈ table.remaining selected out.parent :=
    (minimumWinner_spec (table.remaining selected out.parent) out.hasTrim (fun i => table.point i out.parent)).1
  exact ⟨entrant, (Finset.mem_sdiff.mp hmem).2,
    insertedAssignment selected out.assigned entrant out.parent out.free⟩

/-- Correctness of the specified cached-data operation, as opposed to the
existence of some improving assignment. -/
theorem growthStep_correct (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (hcard : selected.card < Fintype.card Parent) (assigned : selected ↪ Parent)
    (hstrict : ∀ i q, StrictMonoOn (value i q) feasible) (hwhole : ∀ q, whole q ∈ feasible)
    (old state : Parent → Coord) (benchmark : Agent → Value)
    (hold : ∀ q, old q ∈ feasible) (holdCap : ∀ q, old q ≤ whole q)
    (hOldEF : ∀ q r, value (oldOwner q) r (old r) ≤ value (oldOwner q) q (old q))
    (hOldTarget : ∀ q, target (oldOwner q) ≤ value (oldOwner q) q (old q))
    (hstate : ∀ q, state q ∈ feasible) (hinside : ∀ q, state q ≤ table.remainingCap selected q)
    (hbest : ∀ i : selected, ∀ q, value i.val q (state q) ≤ value i.val (assigned i) (state (assigned i)))
    (hbenchmark : ∀ i : selected, benchmark i.val ≤ value i.val (assigned i) (state (assigned i)))
    (houtBenchmark : ∀ i, i ∉ selected → benchmark i ≤ target i)
    (hunused : ∀ q, (∀ i, assigned i ≠ q) → state q = table.remainingCap selected q) :
    let out := growthStep table oldOwner hOwner selected hcard assigned
    (insert out.entrant selected).card = selected.card + 1 ∧
    (∀ i : ↑(insert out.entrant selected), ∀ q,
      value i.val q (state q) ≤ value i.val (out.assigned i) (state (out.assigned i))) ∧
    (∀ i : ↑(insert out.entrant selected), benchmark i.val ≤ value i.val (out.assigned i) (state (out.assigned i))) ∧
    (∀ q, (∀ i, out.assigned i ≠ q) → state q = table.remainingCap selected q) := by
  classical
  let prep := prepare table oldOwner hOwner selected hcard assigned
  let entrant := minimumWinner (table.remaining selected prep.parent) prep.hasTrim (fun i => table.point i prep.parent)
  have hmem : entrant ∈ table.available prep.parent ∧ entrant ∉ selected := Finset.mem_sdiff.mp
    (minimumWinner_spec (table.remaining selected prep.parent) prep.hasTrim (fun i => table.point i prep.parent)).1
  obtain ⟨hbest', hbench', hwhole'⟩ := prepareFrom_correct table oldOwner hOwner selected assigned
    (freeParent selected hcard assigned) (freeParent_spec selected hcard assigned) hstrict hwhole old state benchmark
    hold holdCap hOldEF hOldTarget hstate hinside hbest hbenchmark hunused
  have hcap : table.remainingCap selected prep.parent = table.point entrant prep.parent := by
    simp only [TrimTable.remainingCap, dite_eq_left prep.hasTrim, entrant]
  have htarget : value entrant prep.parent (state prep.parent) = target entrant := by
    rw [hwhole' prep.parent prep.free, hcap]
    exact (table.point_spec entrant prep.parent hmem.1).2.2
  have hnew : ∀ q, value entrant q (state q) ≤ value entrant prep.parent (state prep.parent) := by
    intro q
    rw [htarget]
    exact ((hstrict entrant q).monotoneOn (hstate q) (table.cap_feasible hwhole selected q).1 (hinside q)).trans
      (table.outside_cap_value (fun j q => (hstrict j q).monotoneOn) hwhole selected entrant hmem.2 q)
  have hnewBenchmark : benchmark entrant ≤ value entrant prep.parent (state prep.parent) := by
    rw [htarget]
    exact houtBenchmark entrant hmem.2
  obtain ⟨hc, hb, hk, hw, _⟩ := grow_selected selected prep.assigned entrant prep.parent hmem.2 prep.free
    value state (table.remainingCap selected) benchmark hbest' hbench' hwhole' hnew hnewBenchmark
  exact ⟨hc, hb, hk, hw⟩

end EnvyFreeResearch.Full.Chores.SubCore
