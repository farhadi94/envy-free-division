import EnvyFreeResearch.Full.ChoresComponentGraph

/-! A concrete cycle matching merges precisely the old SCCs it meets. -/

namespace EnvyFreeResearch.Full.Chores.Components

variable {Agent : Type*} [Finite Agent] [DecidableEq Agent]

def Touched (g : Graph Agent) (cycle : List Agent) (a : Agent) : Prop :=
  ∃ x ∈ cycle, SameComponent g a x

def Merged (g : Graph Agent) (cycle : List Agent) (a b : Agent) : Prop :=
  SameComponent g a b ∨ (Touched g cycle a ∧ Touched g cycle b)

theorem touched_of_component {g : Graph Agent} {cycle : List Agent} {a b : Agent}
    (hab : SameComponent g a b) (hb : Touched g cycle b) : Touched g cycle a := by
  obtain ⟨x, hx, hbx⟩ := hb
  exact ⟨x, hx, .trans _ _ _ hab hbx⟩

theorem merged_equivalence (g : Graph Agent) (cycle : List Agent) :
    Equivalence (Merged g cycle) := by
  refine ⟨fun a => Or.inl (.refl a), ?_, ?_⟩
  · intro a b h
    rcases h with h | ⟨ha, hb⟩
    · exact Or.inl (.symm _ _ h)
    · exact Or.inr ⟨hb, ha⟩
  · intro a b c hab hbc
    rcases hab with hab | ⟨ha, hb⟩
    · rcases hbc with hbc | ⟨hb, hc⟩
      · exact Or.inl (.trans _ _ _ hab hbc)
      · exact Or.inr ⟨touched_of_component hab hb, hc⟩
    · rcases hbc with hbc | ⟨_, hc⟩
      · exact Or.inr ⟨ha, touched_of_component (.symm _ _ hbc) hb⟩
      · exact Or.inr ⟨ha, hc⟩

theorem cycle_members_component (g : Graph Agent) (cycle : List Agent)
    (hnodup : cycle.Nodup) {a b : Agent} (ha : a ∈ cycle) (hb : b ∈ cycle) :
    SameComponent (cycle.formPerm :: g) a b := by
  have hs := hnodup.isCycleOn_formPerm.2 ha hb
  obtain ⟨k, hk⟩ := hs.exists_nat_pow_eq
  apply component_iff_reach.mpr
  simpa [hk] using pow_reach cycle.formPerm (List.mem_cons_self) a k

/-- The updated relation is derived from the actual permutation added to the graph. -/
theorem cycle_component_exact (g : Graph Agent) (cycle : List Agent)
    (hnodup : cycle.Nodup) (a b : Agent) :
    SameComponent (cycle.formPerm :: g) a b ↔ Merged g cycle a b := by
  constructor
  · intro h
    induction h with
    | rel a b he =>
      rcases (edge_cons g cycle.formPerm a b).mp he with he | he
      · by_cases ha : a ∈ cycle
        · exact Or.inr ⟨⟨a, ha, .refl _⟩,
            ⟨b, he ▸ List.formPerm_apply_mem_of_mem ha, .refl _⟩⟩
        · have hab : a = b := by
            simpa only [List.formPerm_apply_of_notMem ha] using he
          exact Or.inl (hab ▸ Relation.EqvGen.refl a)
      · exact Or.inl (edge_component he)
    | refl _ => exact (merged_equivalence g cycle).refl _
    | symm _ _ _ ih => exact (merged_equivalence g cycle).symm ih
    | trans _ _ _ _ _ hab hbc => exact (merged_equivalence g cycle).trans hab hbc
  · rintro (hab | ⟨⟨x, hx, hax⟩, ⟨y, hy, hby⟩⟩)
    · exact component_cons g cycle.formPerm hab
    · exact .trans _ _ _ (component_cons g cycle.formPerm hax)
        (.trans _ _ _ (cycle_members_component g cycle hnodup hx hy)
          (.symm _ _ (component_cons g cycle.formPerm hby)))

/-- An untouched component is unchanged, including all its nonmembers. -/
theorem untouched_component_exact (g : Graph Agent) (cycle : List Agent)
    (hnodup : cycle.Nodup) {a : Agent} (ha : ¬ Touched g cycle a) (b : Agent) :
    SameComponent (cycle.formPerm :: g) a b ↔ SameComponent g a b := by
  rw [cycle_component_exact g cycle hnodup]
  simp [Merged, ha]

theorem cycle_merges_distinct (g : Graph Agent) (cycle : List Agent)
    (hnodup : cycle.Nodup) {a b : Agent} (ha : a ∈ cycle) (hb : b ∈ cycle)
    (hold : ¬ SameComponent g a b) :
    SameComponent (cycle.formPerm :: g) a b ∧ ¬ SameComponent g a b :=
  ⟨cycle_members_component g cycle hnodup ha hb, hold⟩

end EnvyFreeResearch.Full.Chores.Components
