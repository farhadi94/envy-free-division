import EnvyFreeResearch.Full.ChoresSubCoreRotation

/-!
# Constructing the SubCore rotation path from actual assignments

The old owners label all contested parents injectively. The current recursive
allocation assigns selected agents injectively. Starting at an unused parent
whose old owner is selected, the finite parent walk ends at a parent whose
old owner is outside the selected set. This is the source of a remaining trim.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.SubCore

open Set Function

variable {Agent Parent : Type*} [Fintype Agent] [DecidableEq Agent]
    [Fintype Parent] [DecidableEq Parent]

structure OwnerPath (selected : Finset Agent) (oldOwner : Parent ↪ Agent)
    (assigned : selected ↪ Parent) (start : Parent) where
  length : ℕ
  positive : 0 < length
  bound : length ≤ selected.card
  owners : Fin length ↪ selected
  parents : Fin (length + 1) ↪ Parent
  first : parents 0 = start
  oldOwner_eq : ∀ r, oldOwner (parents r.castSucc) = (owners r).val
  assigned_eq : ∀ r, assigned (owners r) = parents r.succ
  last_outside : oldOwner (parents (Fin.last length)) ∉ selected

omit [Fintype Agent] in
/-- The path is derived solely from the two actual injective assignments and
the unused starting parent. Its bounded length is at most the selected set's
cardinality, even when that set includes the new stage participant. -/
theorem exists_owner_path (selected : Finset Agent) (oldOwner : Parent ↪ Agent)
    (assigned : selected ↪ Parent) (start : Parent)
    (hselected : oldOwner start ∈ selected) (hfree : ∀ i, assigned i ≠ start) :
    Nonempty (OwnerPath selected oldOwner assigned start) := by
  classical
  let active : Finset Parent := Finset.univ.filter (fun p => oldOwner p ∈ selected)
  have hactive : ∀ p, p ∈ active ↔ oldOwner p ∈ selected := by simp [active]
  let next : active → Parent := fun p => assigned ⟨oldOwner p.val, (hactive p.val).mp p.property⟩
  have hinj : Injective next := by
    intro p q hpq
    apply Subtype.ext
    apply oldOwner.injective
    exact congrArg Subtype.val (assigned.injective hpq)
  have hnopre : ∀ p, next p ≠ start := fun p => hfree _
  obtain ⟨h, hh, _, hbefore, hout, hdistinct⟩ :=
    owner_chain_bounded active next hinj start ((hactive start).mpr hselected) hnopre
  let parents : Fin (h + 1) ↪ Parent := ⟨fun r => (ownerStep active next)^[r.val] start, hdistinct⟩
  let owners : Fin h ↪ selected :=
    ⟨fun r => ⟨oldOwner (parents r.castSucc), (hactive _).mp (hbefore r.val r.isLt)⟩, by
      intro r s hrs
      have hp := oldOwner.injective (congrArg Subtype.val hrs)
      have hcast := parents.injective hp
      have hv : r.val = s.val := congrArg (fun q : Fin (h + 1) => q.val) hcast
      exact Fin.ext hv⟩
  have hbound : h ≤ selected.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective owners owners.injective
  refine ⟨⟨h, hh, hbound, owners, parents, rfl, (fun _ => rfl), ?_, ?_⟩⟩
  · intro r
    change assigned ⟨oldOwner ((ownerStep active next)^[r.val] start), _⟩ =
      (ownerStep active next)^[r.val + 1] start
    rw [iterate_succ_apply', ownerStep_of_mem active next _ (hbefore r.val r.isLt)]
  · exact fun h => hout ((hactive _).mpr h)

/-- The actual injective ownership map obtained from the constructed path. -/
def OwnerPath.reassigned {selected : Finset Agent} {oldOwner : Parent ↪ Agent}
    {assigned : selected ↪ Parent} {start : Parent}
    (path : OwnerPath selected oldOwner assigned start) (hfree : ∀ i, assigned i ≠ start) : selected ↪ Parent :=
  rotated path.owners path.parents assigned path.assigned_eq (fun i => by simpa only [path.first] using hfree i)

omit [Fintype Agent] [DecidableEq Agent] [Fintype Parent] [DecidableEq Parent] in
theorem OwnerPath.frees_remaining_owner {selected : Finset Agent} {oldOwner : Parent ↪ Agent}
    {assigned : selected ↪ Parent} {start : Parent}
    (path : OwnerPath selected oldOwner assigned start) (hfree : ∀ i, assigned i ≠ start) :
    (∃ i, path.reassigned hfree i = start) ∧
    (∀ i, path.reassigned hfree i ≠ path.parents (Fin.last path.length)) ∧
    oldOwner (path.parents (Fin.last path.length)) ∉ selected := by
  refine ⟨?_, ?_, path.last_outside⟩
  · refine ⟨path.owners ⟨0, path.positive⟩, ?_⟩
    exact (rotate_path path.owners path.parents assigned ⟨0, path.positive⟩).trans path.first
  · exact last_parent_freed path.owners path.parents assigned path.assigned_eq
      (fun i => by simpa only [path.first] using hfree i)

end EnvyFreeResearch.Full.Chores.SubCore
