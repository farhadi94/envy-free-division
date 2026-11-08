import EnvyFreeResearch.Full.ChoresSubCoreLocalTable

/-! Remaining caps and their semantic bounds on each parent's retained domain. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore.Local
open Set

variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]
    {value : Agent → Parent → Coord → Value} {feasible : Parent → Set Coord}
    {whole : Parent → Coord} {target : Agent → Value}

def TrimTable.remaining (table : TrimTable value feasible whole target) (selected : Finset Agent)
    (p : Parent) : Finset Agent := table.available p \ selected

def TrimTable.remainingCap (table : TrimTable value feasible whole target) (selected : Finset Agent)
    (p : Parent) : Coord := by
  classical
  exact if h : (table.remaining selected p).Nonempty then
    table.point (minimumWinner (table.remaining selected p) h (fun i => table.point i p)) p
  else whole p

theorem TrimTable.cap_attained (table : TrimTable value feasible whole target) (selected : Finset Agent)
    (p : Parent) (hne : (table.remaining selected p).Nonempty) :
    ∃ i, i ∈ table.available p ∧ i ∉ selected ∧ table.remainingCap selected p = table.point i p ∧
      value i p (table.remainingCap selected p) = target i := by
  classical
  let i := minimumWinner (table.remaining selected p) hne (fun j => table.point j p)
  have hi := (minimumWinner_spec (table.remaining selected p) hne (fun j => table.point j p)).1
  have hmem : i ∈ table.available p ∧ i ∉ selected := Finset.mem_sdiff.mp hi
  have heq : table.remainingCap selected p = table.point i p := by
    simp only [TrimTable.remainingCap, dite_eq_left hne, i]
  exact ⟨i, hmem.1, hmem.2, heq, heq ▸ (table.point_spec i p hmem.1).2.2⟩

theorem TrimTable.cap_whole_of_empty (table : TrimTable value feasible whole target) (selected : Finset Agent)
    (p : Parent) (hne : ¬(table.remaining selected p).Nonempty) : table.remainingCap selected p = whole p := by
  classical
  simp only [TrimTable.remainingCap, dite_eq_right hne]

theorem TrimTable.cap_feasible (table : TrimTable value feasible whole target)
    (hwhole : ∀ p, whole p ∈ feasible p) (selected : Finset Agent) (p : Parent) :
    table.remainingCap selected p ∈ feasible p ∧ table.remainingCap selected p ≤ whole p := by
  by_cases h : (table.remaining selected p).Nonempty
  · obtain ⟨i, hi, _, heq, _⟩ := table.cap_attained selected p h
    rw [heq]
    exact ⟨(table.point_spec i p hi).1, (table.point_spec i p hi).2.1⟩
  · rw [table.cap_whole_of_empty selected p h]
    exact ⟨hwhole p, le_rfl⟩

theorem TrimTable.cap_le_remaining_trim (table : TrimTable value feasible whole target)
    (selected : Finset Agent) (p : Parent) (i : Agent)
    (hi : i ∈ table.available p) (hout : i ∉ selected) : table.remainingCap selected p ≤ table.point i p := by
  classical
  have hmem : i ∈ table.remaining selected p := Finset.mem_sdiff.mpr ⟨hi, hout⟩
  have hne : (table.remaining selected p).Nonempty := ⟨i, hmem⟩
  simp only [TrimTable.remainingCap, dite_eq_left hne]
  exact (minimumWinner_spec (table.remaining selected p) hne (fun j => table.point j p)).2 i hmem

/-- Removing more original trims enlarges parents without making any query. -/
theorem TrimTable.cap_mono (table : TrimTable value feasible whole target)
    (hwhole : ∀ p, whole p ∈ feasible p) (selected enlarged : Finset Agent) (hsub : selected ⊆ enlarged)
    (p : Parent) : table.remainingCap selected p ≤ table.remainingCap enlarged p := by
  by_cases h : (table.remaining enlarged p).Nonempty
  · obtain ⟨i, hi, hout, heq, _⟩ := table.cap_attained enlarged p h
    rw [heq]
    exact table.cap_le_remaining_trim selected p i hi (fun hs => hout (hsub hs))
  · rw [table.cap_whole_of_empty enlarged p h]
    exact (table.cap_feasible hwhole selected p).2

/-- All outside agents retain their original target cap on every remaining
parent, including ineligible agents and parents with no remaining trim. -/
theorem TrimTable.outside_cap_value (table : TrimTable value feasible whole target)
    (hmono : ∀ i p, MonotoneOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (selected : Finset Agent) (i : Agent) (hout : i ∉ selected) (p : Parent) :
    value i p (table.remainingCap selected p) ≤ target i := by
  obtain ⟨hx, hxcap⟩ := table.cap_feasible hwhole selected p
  cases he : table.endpoint i p with
  | none => exact ((hmono i p) hx (hwhole p) hxcap).trans (le_of_lt ((table.unavailable i p).mp he))
  | some x =>
    have hi : i ∈ table.available p := by simp [TrimTable.available, he]
    exact ((hmono i p) hx (table.point_spec i p hi).1
      (table.cap_le_remaining_trim selected p i hi hout)).trans_eq (table.point_spec i p hi).2.2

theorem TrimTable.eligible_of_old_value (table : TrimTable value feasible whole target)
    (hmono : ∀ i p, MonotoneOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (i : Agent) (p : Parent) (x : Coord) (hx : x ∈ feasible p) (hxcap : x ≤ whole p)
    (htarget : target i ≤ value i p x) : i ∈ table.available p := by
  cases he : table.endpoint i p with
  | none => exact ((not_lt_of_ge (htarget.trans ((hmono i p) hx (hwhole p) hxcap)))
      ((table.unavailable i p).mp he)).elim
  | some x => simp [TrimTable.available, he]

/-- An outside old owner supplies both a remaining trim and the terminal cap
containment needed by the proved equal-value chain. -/
theorem TrimTable.outside_old_owner (table : TrimTable value feasible whole target)
    (hstrict : ∀ i p, StrictMonoOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (selected : Finset Agent) (i : Agent) (p : Parent) (x : Coord)
    (hout : i ∉ selected) (hx : x ∈ feasible p) (hxcap : x ≤ whole p)
    (htarget : target i ≤ value i p x) :
    (table.remaining selected p).Nonempty ∧ table.remainingCap selected p ≤ x := by
  have hi := table.eligible_of_old_value (fun i p => (hstrict i p).monotoneOn) hwhole i p x hx hxcap htarget
  refine ⟨⟨i, Finset.mem_sdiff.mpr ⟨hi, hout⟩⟩, ?_⟩
  apply (table.cap_le_remaining_trim selected p i hi hout).trans
  exact ((hstrict i p).le_iff_le (table.point_spec i p hi).1 hx).mp
    ((table.point_spec i p hi).2.2.le.trans htarget)

end EnvyFreeResearch.Full.Chores.SubCore.Local
