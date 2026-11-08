import Mathlib

/-!
# The actual graph of executed chore matchings

The graph is the union of a finite list of permutations.  Thus each edge has
an actual directed return path in one of those permutations.  Its equivalence
closure is exactly its strongly connected component relation, not an assumed
partition supplied by the scheduler.
-/

namespace EnvyFreeResearch.Full.Chores.Components

variable {Agent : Type*}

abbrev Graph (Agent : Type*) := List (Equiv.Perm Agent)

def Edge (g : Graph Agent) (a b : Agent) : Prop :=
  ∃ σ ∈ g, σ a = b

abbrev Reach (g : Graph Agent) := Relation.ReflTransGen (Edge g)

abbrev SameComponent (g : Graph Agent) := Relation.EqvGen (Edge g)

theorem edge_reach {g : Graph Agent} {a b : Agent} (h : Edge g a b) : Reach g a b :=
  .single h

theorem pow_reach {g : Graph Agent} (σ : Equiv.Perm Agent) (hσ : σ ∈ g)
    (a : Agent) (k : ℕ) : Reach g a ((σ ^ k) a) := by
  induction k with
  | zero => simpa using (Relation.ReflTransGen.refl : Reach g a a)
  | succ k ih =>
      simpa [pow_succ', Equiv.Perm.mul_apply] using
        ih.tail (show Edge g ((σ ^ k) a) (σ ((σ ^ k) a)) from ⟨σ, hσ, rfl⟩)

theorem edge_reverse [Finite Agent] {g : Graph Agent} {a b : Agent}
    (h : Edge g a b) : Reach g b a := by
  obtain ⟨σ, hσ, rfl⟩ := h
  have hcycle : σ.SameCycle (σ a) a := by
    exact (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl σ a))
  obtain ⟨k, hk⟩ := hcycle.exists_nat_pow_eq
  simpa [hk] using pow_reach σ hσ (σ a) k

theorem reach_reverse [Finite Agent] {g : Graph Agent} {a b : Agent}
    (h : Reach g a b) : Reach g b a := by
  induction h with
  | refl => exact .refl
  | tail _ he ih => exact (edge_reverse he).trans ih

theorem component_iff_reach [Finite Agent] {g : Graph Agent} {a b : Agent} :
    SameComponent g a b ↔ Reach g a b := by
  constructor
  · intro h
    induction h with
    | rel _ _ he => exact edge_reach he
    | refl _ => exact .refl
    | symm _ _ _ ih => exact reach_reverse ih
    | trans _ _ _ _ _ hab hbc => exact hab.trans hbc
  · exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _

theorem component_iff_strongly_connected [Finite Agent]
    {g : Graph Agent} {a b : Agent} :
    SameComponent g a b ↔ Reach g a b ∧ Reach g b a := by
  rw [component_iff_reach]
  exact ⟨fun h => ⟨h, reach_reverse h⟩, And.left⟩

def partition (g : Graph Agent) : Setoid Agent := Relation.EqvGen.setoid (Edge g)

theorem edge_component {g : Graph Agent} {a b : Agent} (h : Edge g a b) :
    SameComponent g a b := .rel _ _ h

theorem visited_component {g : Graph Agent} (σ : Equiv.Perm Agent) (hσ : σ ∈ g)
    (a : Agent) : SameComponent g a (σ a) := edge_component ⟨σ, hσ, rfl⟩

@[simp] theorem edge_cons (g : Graph Agent) (σ : Equiv.Perm Agent) (a b : Agent) :
    Edge (σ :: g) a b ↔ σ a = b ∨ Edge g a b := by
  simp only [Edge, List.mem_cons]
  constructor
  · rintro ⟨τ, rfl | hτ, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨τ, hτ, h⟩
  · rintro (h | ⟨τ, hτ, h⟩)
    · exact ⟨σ, Or.inl rfl, h⟩
    · exact ⟨τ, Or.inr hτ, h⟩

theorem component_mono {g h : Graph Agent} (hsub : g ⊆ h) {a b : Agent}
    (hab : SameComponent g a b) : SameComponent h a b :=
  Relation.EqvGen.mono (fun _ _ ⟨σ, hσ, heq⟩ => ⟨σ, hsub hσ, heq⟩) _ _ hab

theorem component_cons (g : Graph Agent) (σ : Equiv.Perm Agent) {a b : Agent}
    (hab : SameComponent g a b) : SameComponent (σ :: g) a b :=
  component_mono (fun _ h => List.mem_cons_of_mem _ h) hab

/-- Re-executing a matching using only old component edges cannot merge SCCs. -/
theorem component_cons_eq (g : Graph Agent) (σ : Equiv.Perm Agent)
    (hσ : ∀ a, SameComponent g a (σ a)) (a b : Agent) :
    SameComponent (σ :: g) a b ↔ SameComponent g a b := by
  constructor
  · intro h
    induction h with
    | rel a b he =>
      rcases (edge_cons g σ a b).mp he with he | he
      · simpa [← he] using hσ a
      · exact edge_component he
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ hab hbc => exact .trans _ _ _ hab hbc
  · exact component_cons g σ

/-- Initially only the identity matching has been executed. -/
theorem initial_component (a b : Agent) :
    SameComponent [1] a b ↔ a = b := by
  constructor
  · intro h
    induction h with
    | rel _ _ he =>
      obtain ⟨σ, hσ, he⟩ := he
      simpa only [List.mem_singleton.mp hσ, Equiv.Perm.one_apply] using he
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ hab hbc => exact hab.trans hbc
  · rintro rfl
    exact .refl _

end EnvyFreeResearch.Full.Chores.Components
