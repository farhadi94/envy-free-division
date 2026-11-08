import EnvyFreeResearch.Full.ChoresSubCoreLocalCaps

/-! The exact original ownership preparation and growth functions are valid
on separate retained-record domains. This does not alter any tie or path choice. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore.Local
open Set Function
variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]
    {value : Agent → Parent → Coord → Value} {feasible : Parent → Set Coord}
    {whole : Parent → Coord} {target : Agent → Value}

theorem prepareFrom_correct (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (assigned : selected ↪ Parent) (p : Parent) (hfree : ∀ i, assigned i ≠ p)
    (hstrict : ∀ i q, StrictMonoOn (value i q) (feasible q)) (hwhole : ∀ q, whole q ∈ feasible q)
    (old state : Parent → Coord) (benchmark : Agent → Value)
    (hold : ∀ q, old q ∈ feasible q) (holdCap : ∀ q, old q ≤ whole q)
    (hOldEF : ∀ q r, value (oldOwner q) r (old r) ≤ value (oldOwner q) q (old q))
    (hOldTarget : ∀ q, target (oldOwner q) ≤ value (oldOwner q) q (old q))
    (hstate : ∀ q, state q ∈ feasible q) (hinside : ∀ q, state q ≤ table.remainingCap selected q)
    (hbest : ∀ i : selected, ∀ q, value i.val q (state q) ≤ value i.val (assigned i) (state (assigned i)))
    (hbenchmark : ∀ i : selected, benchmark i.val ≤ value i.val (assigned i) (state (assigned i)))
    (hunused : ∀ q, (∀ i, assigned i ≠ q) → state q = table.remainingCap selected q) :
    let out := prepareFrom table.erase oldOwner hOwner selected assigned p hfree
    (∀ i : selected, ∀ q, value i.val q (state q) ≤ value i.val (out.assigned i) (state (out.assigned i))) ∧
    (∀ i : selected, benchmark i.val ≤ value i.val (out.assigned i) (state (out.assigned i))) ∧
    (∀ q, (∀ i, out.assigned i ≠ q) → state q = table.remainingCap selected q) := by
  classical
  unfold prepareFrom
  split_ifs with htrim
  · exact ⟨hbest, hbenchmark, hunused⟩
  · let path := repairPath table.erase oldOwner hOwner selected assigned p hfree htrim
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

theorem growthStep_correct (table : TrimTable value feasible whole target) (oldOwner : Parent ↪ Agent)
    (hOwner : ∀ p, oldOwner p ∈ table.available p) (selected : Finset Agent)
    (hcard : selected.card < Fintype.card Parent) (assigned : selected ↪ Parent)
    (hstrict : ∀ i q, StrictMonoOn (value i q) (feasible q)) (hwhole : ∀ q, whole q ∈ feasible q)
    (old state : Parent → Coord) (benchmark : Agent → Value)
    (hold : ∀ q, old q ∈ feasible q) (holdCap : ∀ q, old q ≤ whole q)
    (hOldEF : ∀ q r, value (oldOwner q) r (old r) ≤ value (oldOwner q) q (old q))
    (hOldTarget : ∀ q, target (oldOwner q) ≤ value (oldOwner q) q (old q))
    (hstate : ∀ q, state q ∈ feasible q) (hinside : ∀ q, state q ≤ table.remainingCap selected q)
    (hbest : ∀ i : selected, ∀ q, value i.val q (state q) ≤ value i.val (assigned i) (state (assigned i)))
    (hbenchmark : ∀ i : selected, benchmark i.val ≤ value i.val (assigned i) (state (assigned i)))
    (houtBenchmark : ∀ i, i ∉ selected → benchmark i ≤ target i)
    (hunused : ∀ q, (∀ i, assigned i ≠ q) → state q = table.remainingCap selected q) :
    let out := growthStep table.erase oldOwner hOwner selected hcard assigned
    (insert out.entrant selected).card = selected.card + 1 ∧
    (∀ i : ↑(insert out.entrant selected), ∀ q,
      value i.val q (state q) ≤ value i.val (out.assigned i) (state (out.assigned i))) ∧
    (∀ i : ↑(insert out.entrant selected), benchmark i.val ≤ value i.val (out.assigned i) (state (out.assigned i))) ∧
    (∀ q, (∀ i, out.assigned i ≠ q) → state q = table.remainingCap selected q) := by
  classical
  let prep := prepare table.erase oldOwner hOwner selected hcard assigned
  let entrant := minimumWinner (table.remaining selected prep.parent) prep.hasTrim (fun i => table.point i prep.parent)
  have hmem : entrant ∈ table.available prep.parent ∧ entrant ∉ selected := Finset.mem_sdiff.mp
    (minimumWinner_spec (table.remaining selected prep.parent) prep.hasTrim (fun i => table.point i prep.parent)).1
  obtain ⟨hbest', hbench', hwhole'⟩ := prepareFrom_correct table oldOwner hOwner selected assigned
    (freeParent selected hcard assigned) (freeParent_spec selected hcard assigned) hstrict hwhole old state benchmark
    hold holdCap hOldEF hOldTarget hstate hinside hbest hbenchmark hunused
  have hcap : table.remainingCap selected prep.parent = table.point entrant prep.parent := by
    have hhas : (table.remaining selected prep.parent).Nonempty := prep.hasTrim
    simp only [TrimTable.remainingCap, dite_eq_left hhas, entrant]
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

end EnvyFreeResearch.Full.Chores.SubCore.Local
