import EnvyFreeResearch.Full.ChoresSubCoreLoop

/-!
# Actual contested labels and stage targets

The contested parents are precisely the image of the old assignment. Their
old-owner embedding is constructed from that image. Each target is the
maximum of the inherited benchmark and an actual favorite uncontested whole
parent, chosen from the finite cached values.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set Function

variable {Agent Parent : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent]

def contestedParents (selected : Finset Agent) (assigned : selected ↪ Parent) : Finset Parent :=
  Finset.univ.image assigned

lemma mem_contestedParents (selected : Finset Agent) (assigned : selected ↪ Parent) (p : Parent) :
    p ∈ contestedParents selected assigned ↔ ∃ i, assigned i = p := by
  simp only [contestedParents, Finset.mem_image, Finset.mem_univ, true_and]

def contestedOwner (selected : Finset Agent) (assigned : selected ↪ Parent) :
    (contestedParents selected assigned) ↪ Agent := by
  classical
  have hex : ∀ p : contestedParents selected assigned, ∃ i : selected, assigned i = p.val :=
    fun p => (mem_contestedParents selected assigned p.val).mp p.property
  refine ⟨fun p => (Classical.choose (hex p)).val, ?_⟩
  intro p q hpq
  apply Subtype.ext
  have heq : Classical.choose (hex p) = Classical.choose (hex q) := Subtype.ext hpq
  exact (Classical.choose_spec (hex p)).symm.trans ((congrArg assigned heq).trans (Classical.choose_spec (hex q)))

lemma contestedOwner_mem (selected : Finset Agent) (assigned : selected ↪ Parent)
    (p : contestedParents selected assigned) : contestedOwner selected assigned p ∈ selected := by
  have hex : ∃ i : selected, assigned i = p.val := (mem_contestedParents selected assigned p.val).mp p.property
  change (Classical.choose hex).val ∈ selected
  exact (Classical.choose hex).property

lemma contestedOwner_parent (selected : Finset Agent) (assigned : selected ↪ Parent)
    (p : contestedParents selected assigned) :
    assigned ⟨contestedOwner selected assigned p, contestedOwner_mem selected assigned p⟩ = p.val := by
  have hex : ∃ i : selected, assigned i = p.val := (mem_contestedParents selected assigned p.val).mp p.property
  change assigned (Classical.choose hex) = p.val
  exact Classical.choose_spec hex

theorem contestedParents_card (selected : Finset Agent) (assigned : selected ↪ Parent) :
    (contestedParents selected assigned).card = selected.card := by
  classical
  rw [contestedParents, Finset.card_image_of_injective _ assigned.injective]
  simp only [Finset.card_univ, Fintype.card_coe]

def uncontestedParents (selected : Finset Agent) (assigned : selected ↪ Parent) : Finset Parent :=
  Finset.univ \ contestedParents selected assigned

lemma mem_uncontestedParents (selected : Finset Agent) (assigned : selected ↪ Parent) (p : Parent) :
    p ∈ uncontestedParents selected assigned ↔ ∀ i, assigned i ≠ p := by
  simp only [uncontestedParents, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_contestedParents, not_exists]

theorem uncontested_nonempty (selected : Finset Agent) (assigned : selected ↪ Parent)
    (hcard : selected.card < Fintype.card Parent) : (uncontestedParents selected assigned).Nonempty := by
  obtain ⟨p, hp⟩ := exists_free_parent selected hcard assigned
  exact ⟨p, (mem_uncontestedParents selected assigned p).mpr hp⟩

variable {Value : Type*} [LinearOrder Value]

def favoriteUncontested (selected : Finset Agent) (assigned : selected ↪ Parent)
    (hcard : selected.card < Fintype.card Parent) (wholeValue : Agent → Parent → Value) (i : Agent) : Parent :=
  Classical.choose (Finset.exists_max_image (uncontestedParents selected assigned) (wholeValue i)
    (uncontested_nonempty selected assigned hcard))

theorem favoriteUncontested_spec (selected : Finset Agent) (assigned : selected ↪ Parent)
    (hcard : selected.card < Fintype.card Parent) (wholeValue : Agent → Parent → Value) (i : Agent) :
    favoriteUncontested selected assigned hcard wholeValue i ∈ uncontestedParents selected assigned ∧
    ∀ p ∈ uncontestedParents selected assigned,
      wholeValue i p ≤ wholeValue i (favoriteUncontested selected assigned hcard wholeValue i) :=
  Classical.choose_spec (Finset.exists_max_image (uncontestedParents selected assigned) (wholeValue i)
    (uncontested_nonempty selected assigned hcard))

def stageTarget (selected : Finset Agent) (assigned : selected ↪ Parent)
    (hcard : selected.card < Fintype.card Parent) (wholeValue : Agent → Parent → Value)
    (benchmark : Agent → Value) (i : Agent) : Value :=
  max (benchmark i) (wholeValue i (favoriteUncontested selected assigned hcard wholeValue i))

theorem stageTarget_benchmark (selected : Finset Agent) (assigned : selected ↪ Parent)
    (hcard : selected.card < Fintype.card Parent) (wholeValue : Agent → Parent → Value)
    (benchmark : Agent → Value) (i : Agent) :
    benchmark i ≤ stageTarget selected assigned hcard wholeValue benchmark i := le_max_left _ _

theorem stageTarget_whole (selected : Finset Agent) (assigned : selected ↪ Parent)
    (hcard : selected.card < Fintype.card Parent) (wholeValue : Agent → Parent → Value)
    (benchmark : Agent → Value) (i : Agent) (p : Parent) (hp : p ∈ uncontestedParents selected assigned) :
    wholeValue i p ≤ stageTarget selected assigned hcard wholeValue benchmark i :=
  ((favoriteUncontested_spec selected assigned hcard wholeValue i).2 p hp).trans (le_max_right _ _)

theorem old_own_meets_target (selected : Finset Agent) (assigned : selected ↪ Parent)
    (hcard : selected.card < Fintype.card Parent) (wholeValue : Agent → Parent → Value)
    (benchmark own : Agent → Value)
    (hbenchmark : ∀ i : selected, benchmark i.val ≤ own i.val)
    (houtside : ∀ i : selected, ∀ p ∈ uncontestedParents selected assigned, wholeValue i.val p ≤ own i.val) :
    ∀ i : selected, stageTarget selected assigned hcard wholeValue benchmark i.val ≤ own i.val := by
  intro i
  exact max_le (hbenchmark i) (houtside i _ (favoriteUncontested_spec selected assigned hcard wholeValue i.val).1)

theorem high_benchmark_target (selected : Finset Agent) (assigned : selected ↪ Parent)
    (hcard : selected.card < Fintype.card Parent) (wholeValue : Agent → Parent → Value)
    (benchmark : Agent → Value) (i : Agent)
    (hhigh : ∀ p ∈ uncontestedParents selected assigned, wholeValue i p < benchmark i) :
    stageTarget selected assigned hcard wholeValue benchmark i = benchmark i :=
  max_eq_left (le_of_lt (hhigh _ (favoriteUncontested_spec selected assigned hcard wholeValue i).1))

/-- Once every participant with an excessive inherited benchmark has been
selected, any remaining participant meets her target on an uncontested whole. -/
theorem outside_target_is_whole (processed : Finset Agent) (assigned : processed ↪ Parent)
    (hcard : processed.card < Fintype.card Parent) (wholeValue : Agent → Parent → Value)
    (benchmark : Agent → Value) (selected : Finset Agent) (i : Agent) (hi : i ∉ selected)
    (hforced : ∀ j, wholeValue j (favoriteUncontested processed assigned hcard wholeValue j) < benchmark j → j ∈ selected) :
    stageTarget processed assigned hcard wholeValue benchmark i =
      wholeValue i (favoriteUncontested processed assigned hcard wholeValue i) := by
  apply max_eq_right
  exact le_of_not_gt (fun h => hi (hforced i h))

end EnvyFreeResearch.Full.Chores.SubCore
