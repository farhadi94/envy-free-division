import EnvyFreeResearch.Full.ChoresSubCoreAllocation

/-! A SubCore call on k+1 roots reserves every donor and exactly one survivor. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentAssignment
open SubCore
open scoped Classical

variable {Task Root Coord : Type*} [Fintype Task] [Fintype Root]

theorem exists_unused (out : Allocation Task Root Coord)
    (hmany : Fintype.card Task < Fintype.card Root) :
    ∃ s : Root, ∀ j, out.assigned j ≠ s := by
  by_contra! h
  have hsurj : Function.Surjective out.assigned := fun s => h s
  have hcard := Fintype.card_le_of_surjective out.assigned hsurj
  omega

def unused (out : Allocation Task Root Coord)
    (hmany : Fintype.card Task < Fintype.card Root) : Root :=
  (exists_unused out hmany).choose

theorem unused_spec (out : Allocation Task Root Coord)
    (hmany : Fintype.card Task < Fintype.card Root) (j : Task) :
    out.assigned j ≠ unused out hmany := (exists_unused out hmany).choose_spec j

def allRoots (out : Allocation Task Root Coord)
    (hmany : Fintype.card Task < Fintype.card Root) : Unit ⊕ Task ↪ Root where
  toFun
    | .inl _ => unused out hmany
    | .inr j => out.assigned j
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => rfl
      | inr j => exact False.elim (unused_spec out hmany j h.symm)
    | inr i =>
      cases b with
      | inl b => exact False.elim (unused_spec out hmany i h)
      | inr j => exact congrArg Sum.inr (out.assigned.injective h)

theorem allRoots_surjective (out : Allocation Task Root Coord)
    (hcard : Fintype.card Root = Fintype.card Task + 1) :
    Function.Surjective (allRoots out (by omega)) := by
  intro s
  by_contra! hnot
  have hlt := Fintype.card_lt_of_injective_of_notMem
    (allRoots out (by omega)) (allRoots out (by omega)).injective
    (show s ∉ Set.range (allRoots out (by omega)) from fun ⟨a, ha⟩ => hnot a ha)
  simp only [Fintype.card_sum, Fintype.card_unit, hcard] at hlt
  omega

theorem every_root (out : Allocation Task Root Coord)
    (hcard : Fintype.card Root = Fintype.card Task + 1) (s : Root) :
    s = unused out (by omega) ∨ ∃ j, out.assigned j = s := by
  obtain ⟨r, hr⟩ := allRoots_surjective out hcard s
  cases r with
  | inl _ => exact Or.inl hr.symm
  | inr j => exact Or.inr ⟨j, hr⟩

theorem unique_unused (out : Allocation Task Root Coord)
    (hcard : Fintype.card Root = Fintype.card Task + 1) (s : Root)
    (hs : ∀ j, out.assigned j ≠ s) : s = unused out (by omega) := by
  rcases every_root out hcard s with h | ⟨j, hj⟩
  · exact h
  · exact (hs j hj).elim

end EnvyFreeResearch.Full.Chores.ComponentAssignment
