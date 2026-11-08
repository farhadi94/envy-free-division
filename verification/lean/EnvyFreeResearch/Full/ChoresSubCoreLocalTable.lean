import EnvyFreeResearch.Full.ChoresSubCoreLocalChain

/-! The existing trim-table operations with parent-specific row domains.
Erasure changes only proof fields, and gives the exact original source table. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore.Local
open Set
variable {Agent Parent Coord Value : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent] [LinearOrder Coord] [LinearOrder Value]

structure TrimTable (value : Agent → Parent → Coord → Value) (feasible : Parent → Set Coord)
    (whole : Parent → Coord) (target : Agent → Value) where
  endpoint : Agent → Parent → Option Coord
  unavailable : ∀ i p, endpoint i p = none ↔ value i p (whole p) < target i
  legal : ∀ i p x, endpoint i p = some x → x ∈ feasible p ∧ x ≤ whole p ∧ value i p x = target i

def TrimTable.erase {value : Agent → Parent → Coord → Value} {feasible : Parent → Set Coord}
    {whole : Parent → Coord} {target : Agent → Value} (table : TrimTable value feasible whole target) :
    SubCore.TrimTable value Set.univ whole target :=
  ⟨table.endpoint, table.unavailable, fun i p x hx => ⟨Set.mem_univ _, (table.legal i p x hx).2⟩⟩


variable {value : Agent → Parent → Coord → Value} {feasible : Parent → Set Coord}
    {whole : Parent → Coord} {target : Agent → Value}

def TrimTable.available (table : TrimTable value feasible whole target) (p : Parent) : Finset Agent :=
  Finset.univ.filter (fun i => (table.endpoint i p).isSome)

def TrimTable.point (table : TrimTable value feasible whole target) (i : Agent) (p : Parent) : Coord :=
  (table.endpoint i p).getD (whole p)

lemma TrimTable.point_spec (table : TrimTable value feasible whole target) (i : Agent) (p : Parent)
    (hi : i ∈ table.available p) :
    table.point i p ∈ feasible p ∧ table.point i p ≤ whole p ∧ value i p (table.point i p) = target i := by
  have hs : (table.endpoint i p).isSome := (Finset.mem_filter.mp hi).2
  cases he : table.endpoint i p with
  | none => simp [he] at hs
  | some x => simpa only [TrimTable.point, he, Option.getD_some] using table.legal i p x he

def TrimTable.winner (table : TrimTable value feasible whole target)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) (p : Parent) : Agent :=
  chooseWinner (table.available p) (hne p) (fun i => table.point i p) (preferred p)

lemma TrimTable.winner_spec (table : TrimTable value feasible whole target)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) (p : Parent) :
    table.winner hne preferred p ∈ table.available p ∧
      ∀ j ∈ table.available p, table.point (table.winner hne preferred p) p ≤ table.point j p :=
  chooseWinner_spec (table.available p) (hne p) (fun i => table.point i p) (preferred p)

/-- Every selected rightmost suffix is worth at most each participant's
target, including a participant who was ineligible to trim that parent. -/
theorem TrimTable.winner_value_le (table : TrimTable value feasible whole target)
    (hmono : ∀ i p, MonotoneOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) :
    ∀ i p, value i p (table.point (table.winner hne preferred p) p) ≤ target i := by
  intro i p
  obtain ⟨hw, hmin⟩ := table.winner_spec hne preferred p
  obtain ⟨hx, hxcap, _⟩ := table.point_spec _ p hw
  cases he : table.endpoint i p with
  | none =>
    exact ((hmono i p) hx (hwhole p) hxcap).trans (le_of_lt ((table.unavailable i p).mp he))
  | some x =>
    have hi : i ∈ table.available p := by simp [TrimTable.available, he]
    obtain ⟨hix, _, hiv⟩ := table.point_spec i p hi
    exact ((hmono i p) hx hix (hmin i hi)).trans_eq hiv

def TrimTable.selected (table : TrimTable value feasible whole target)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) : Finset Agent :=
  Finset.univ.image (table.winner hne preferred)

def TrimTable.assigned (table : TrimTable value feasible whole target)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) :
    (table.selected hne preferred) ↪ Parent := by
  classical
  have hex : ∀ i : table.selected hne preferred, ∃ p, table.winner hne preferred p = i.val := by
    intro i
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp i.property
    exact ⟨p, hp⟩
  refine ⟨fun i => Classical.choose (hex i), ?_⟩
  intro i j hij
  apply Subtype.ext
  exact (Classical.choose_spec (hex i)).symm.trans ((congrArg (table.winner hne preferred) hij).trans
    (Classical.choose_spec (hex j)))

lemma TrimTable.assigned_winner (table : TrimTable value feasible whole target)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent)
    (i : table.selected hne preferred) : table.winner hne preferred (table.assigned hne preferred i) = i.val := by
  have hex : ∃ p, table.winner hne preferred p = i.val := by
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp i.property
    exact ⟨p, hp⟩
  change table.winner hne preferred (Classical.choose hex) = i.val
  exact Classical.choose_spec hex

/-- The selected agents receive distinct actual winner suffixes, attain their
targets exactly, and satisfy all pairwise cake-EF comparisons. -/
theorem TrimTable.initial_selection_correct (table : TrimTable value feasible whole target)
    (hmono : ∀ i p, MonotoneOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent) :
    (table.selected hne preferred).card ≤ Fintype.card Parent ∧
    (∀ i : table.selected hne preferred,
      value i.val (table.assigned hne preferred i)
        (table.point (table.winner hne preferred (table.assigned hne preferred i)) (table.assigned hne preferred i)) = target i.val) ∧
    (∀ i j : table.selected hne preferred,
      value i.val (table.assigned hne preferred j)
        (table.point (table.winner hne preferred (table.assigned hne preferred j)) (table.assigned hne preferred j)) ≤
      value i.val (table.assigned hne preferred i)
        (table.point (table.winner hne preferred (table.assigned hne preferred i)) (table.assigned hne preferred i))) := by
  have hown : ∀ i : table.selected hne preferred,
      value i.val (table.assigned hne preferred i)
        (table.point (table.winner hne preferred (table.assigned hne preferred i)) (table.assigned hne preferred i)) = target i.val := by
    intro i
    have hs := table.point_spec _ (table.assigned hne preferred i)
      (table.winner_spec hne preferred (table.assigned hne preferred i)).1
    simpa only [table.assigned_winner hne preferred i] using hs.2.2
  refine ⟨?_, hown, ?_⟩
  · exact (Finset.card_image_le).trans_eq (Finset.card_univ)
  · intro i j
    rw [hown i]
    exact table.winner_value_le hmono hwhole hne preferred i.val (table.assigned hne preferred j)

/-- An inherited suffix at its owner's target is selected when all other rows
value it below their targets. This proves the source tie-rule necessity. -/
theorem TrimTable.inherited_owner_selected (table : TrimTable value feasible whole target)
    (hstrict : ∀ i p, StrictMonoOn (value i p) (feasible p)) (hwhole : ∀ p, whole p ∈ feasible p)
    (hne : ∀ p, (table.available p).Nonempty) (preferred : Parent → Option Agent)
    (i : Agent) (p : Parent) (x : Coord) (hx : x ∈ feasible p) (hxcap : x ≤ whole p)
    (hown : value i p x = target i) (hother : ∀ j, value j p x ≤ target j)
    (hpreferred : preferred p = some i) : table.winner hne preferred p = i := by
  classical
  have hi : i ∈ table.available p := by
    have hnot : table.endpoint i p ≠ none := by
      intro h
      have hsmall := (table.unavailable i p).mp h
      have hlarge := (hstrict i p).monotoneOn hx (hwhole p) hxcap
      rw [hown] at hlarge
      exact (not_lt_of_ge hlarge) hsmall
    simp only [TrimTable.available, Finset.mem_filter, Finset.mem_univ, true_and,
      Option.isSome_iff_ne_none]
    exact hnot
  have hix : table.point i p = x := (hstrict i p).injOn (table.point_spec i p hi).1 hx
    ((table.point_spec i p hi).2.2.trans hown.symm)
  unfold TrimTable.winner
  rw [hpreferred]
  apply chooseWinner_preferred _ _ _ i hi
  intro j hj
  rw [hix]
  exact ((hstrict j p).le_iff_le hx (table.point_spec j p hj).1).mp
    ((hother j).trans_eq (table.point_spec j p hj).2.2.symm)

end EnvyFreeResearch.Full.Chores.SubCore.Local
