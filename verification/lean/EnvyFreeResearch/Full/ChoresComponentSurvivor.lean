import EnvyFreeResearch.Full.ChoresComponentPath
import EnvyFreeResearch.Full.ChoresComponentMerge

/-!
# The survivor's actual complete matching

In each old component, the recorded incoming agent is connected to that
component's representative by an old simple path.  We compose these disjoint
internal path matchings with the cycle on the representatives.  The resulting
permutation uses exactly the prescribed outgoing edges and old edges elsewhere.
Its graph merges precisely the selected old components.
-/

namespace EnvyFreeResearch.Full.Chores.Components

variable {Agent Component : Type*}

/-- Componentwise permutations can be combined because each preserves its fiber. -/
def fiberPerm (component : Agent → Component) (localPerm : Component → Equiv.Perm Agent)
    (hpres : ∀ c x, component (localPerm c x) = component x) : Equiv.Perm Agent where
  toFun x := localPerm (component x) x
  invFun x := (localPerm (component x)).symm x
  left_inv x := by
    dsimp
    rw [hpres]
    exact Equiv.symm_apply_apply _ _
  right_inv x := by
    dsimp
    have h := hpres (component x) ((localPerm (component x)).symm x)
    simp only [Equiv.apply_symm_apply] at h
    rw [← h]
    exact Equiv.apply_symm_apply _ _

@[simp] theorem fiberPerm_apply (component : Agent → Component)
    (localPerm : Component → Equiv.Perm Agent)
    (hpres : ∀ c x, component (localPerm c x) = component x) (x : Agent) :
    fiberPerm component localPerm hpres x = localPerm (component x) x := rfl

def Coarsened (component : Agent → Component) (cycle : List Component) (a b : Agent) : Prop :=
  component a = component b ∨ (component a ∈ cycle ∧ component b ∈ cycle)

theorem coarsened_equivalence (component : Agent → Component) (cycle : List Component) :
    Equivalence (Coarsened component cycle) := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
  · rintro a b (h | ⟨ha, hb⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨hb, ha⟩
  · rintro a b c (hab | ⟨ha, hb⟩) (hbc | ⟨hb', hc⟩)
    · exact Or.inl (hab.trans hbc)
    · exact Or.inr ⟨hab ▸ hb', hc⟩
    · exact Or.inr ⟨ha, hbc ▸ hb⟩
    · exact Or.inr ⟨ha, hc⟩

section Survivor

variable [Finite Agent] [DecidableEq Agent] [DecidableEq Component]
variable (g : Graph Agent) (component : Agent → Component)
  (component_exact : ∀ a b, SameComponent g a b ↔ component a = component b)
  (representative : Component → Agent)
  (representative_component : ∀ c, component (representative c) = c)
  (cycle : List Component) (recipient : Component → Agent)
  (recipient_component : ∀ c, component (recipient c) = cycle.formPerm c)

def representativeEmbedding : Component ↪ Agent where
  toFun := representative
  inj' := by
    intro c d h
    simpa only [representative_component] using congrArg component h

noncomputable def incomingMatching (c : Component) : Equiv.Perm Agent :=
  donorMatching g (representative c) (recipient (cycle.formPerm.symm c))
    ((component_exact _ _).mpr (by simp only [recipient_component,
      Equiv.apply_symm_apply, representative_component]))

theorem incomingMatching_preserves (c : Component) (x : Agent) :
    component (incomingMatching g component component_exact representative
      representative_component cycle recipient recipient_component c x) = component x := by
  apply Eq.symm
  apply (component_exact _ _).mp
  unfold incomingMatching
  by_cases hx : x = representative c
  · subst x
    rw [donorMatching_recipient]
    apply (component_exact _ _).mpr
    simp only [representative_component, recipient_component, Equiv.apply_symm_apply]
  · rcases donorMatching_other g (representative c) _ _ hx with heq | he
    · exact heq.symm ▸ Relation.EqvGen.refl x
    · exact edge_component he

noncomputable def internalMatching : Equiv.Perm Agent :=
  fiberPerm component
    (incomingMatching g component component_exact representative representative_component
      cycle recipient recipient_component)
    (incomingMatching_preserves g component component_exact representative
      representative_component cycle recipient recipient_component)

noncomputable def survivorMatching : Equiv.Perm Agent :=
  internalMatching g component component_exact representative representative_component
    cycle recipient recipient_component *
  cycle.formPerm.viaEmbedding
    (representativeEmbedding component representative representative_component)

theorem survivorMatching_recipient (c : Component) :
    survivorMatching g component component_exact representative representative_component
      cycle recipient recipient_component (representative c) = recipient c := by
  unfold survivorMatching
  have hlift := Equiv.Perm.viaEmbedding_apply cycle.formPerm
    (representativeEmbedding component representative representative_component) c
  change cycle.formPerm.viaEmbedding
    (representativeEmbedding component representative representative_component)
      (representative c) = representative (cycle.formPerm c) at hlift
  rw [Equiv.Perm.mul_apply, hlift]
  change incomingMatching g component component_exact representative representative_component
    cycle recipient recipient_component (component (representative (cycle.formPerm c)))
      (representative (cycle.formPerm c)) = recipient c
  rw [representative_component]
  unfold incomingMatching
  rw [donorMatching_recipient, Equiv.symm_apply_apply]

theorem survivorMatching_other {x : Agent} (hx : x ∉ Set.range representative) :
    survivorMatching g component component_exact representative representative_component
      cycle recipient recipient_component x = x ∨
    Edge g x (survivorMatching g component component_exact representative representative_component
      cycle recipient recipient_component x) := by
  unfold survivorMatching
  rw [Equiv.Perm.mul_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx]
  change incomingMatching g component component_exact representative representative_component
    cycle recipient recipient_component (component x) x = x ∨
      Edge g x (incomingMatching g component component_exact representative representative_component
        cycle recipient recipient_component (component x) x)
  unfold incomingMatching
  exact donorMatching_other g (representative (component x)) _ _
    (fun h => hx ⟨component x, h.symm⟩)

theorem survivorMatching_untouched
    (hoff : ∀ c, c ∉ cycle → recipient c = representative c)
    (x : Agent) (hx : component x ∉ cycle) :
    survivorMatching g component component_exact representative representative_component
      cycle recipient recipient_component x = x := by
  have hself : cycle.formPerm (component x) = component x :=
    List.formPerm_apply_of_notMem hx
  have hinv : cycle.formPerm.symm (component x) = component x := by
    apply cycle.formPerm.injective
    simpa only [Equiv.apply_symm_apply] using hself.symm
  have hlift : cycle.formPerm.viaEmbedding
      (representativeEmbedding component representative representative_component) x = x := by
    by_cases hr : x ∈ Set.range representative
    · obtain ⟨c, rfl⟩ := hr
      have hc : c ∉ cycle := by simpa only [representative_component] using hx
      have h := Equiv.Perm.viaEmbedding_apply cycle.formPerm
        (representativeEmbedding component representative representative_component) c
      change cycle.formPerm.viaEmbedding
        (representativeEmbedding component representative representative_component)
          (representative c) = representative (cycle.formPerm c) at h
      rw [List.formPerm_apply_of_notMem hc] at h
      exact h
    · exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hr
  unfold survivorMatching
  rw [Equiv.Perm.mul_apply, hlift]
  change incomingMatching g component component_exact representative representative_component
    cycle recipient recipient_component (component x) x = x
  simp [incomingMatching, donorMatching, hinv, hoff (component x) hx]

theorem survivor_representative_step (c : Component) :
    SameComponent (survivorMatching g component component_exact representative
      representative_component cycle recipient recipient_component :: g)
      (representative c) (representative (cycle.formPerm c)) := by
  apply Relation.EqvGen.trans _ (recipient c) _
  · apply edge_component
    exact ⟨_, List.mem_cons_self,
      survivorMatching_recipient g component component_exact representative
        representative_component cycle recipient recipient_component c⟩
  · apply component_cons
    apply (component_exact _ _).mpr
    simp only [recipient_component, representative_component]

theorem survivor_representative_pow (c : Component) (k : ℕ) :
    SameComponent (survivorMatching g component component_exact representative
      representative_component cycle recipient recipient_component :: g)
      (representative c) (representative ((cycle.formPerm ^ k) c)) := by
  induction k with
  | zero => simpa using (Relation.EqvGen.refl (r := Edge
      (survivorMatching g component component_exact representative representative_component
        cycle recipient recipient_component :: g)) (representative c))
  | succ k ih =>
    simpa only [pow_succ', Equiv.Perm.mul_apply] using
      Relation.EqvGen.trans _ _ _ ih
        (survivor_representative_step g component component_exact representative
          representative_component cycle recipient recipient_component ((cycle.formPerm ^ k) c))

theorem survivor_representatives [Finite Component] (hnodup : cycle.Nodup)
    {c d : Component} (hc : c ∈ cycle) (hd : d ∈ cycle) :
    SameComponent (survivorMatching g component component_exact representative
      representative_component cycle recipient recipient_component :: g)
      (representative c) (representative d) := by
  obtain ⟨k, hk⟩ := (hnodup.isCycleOn_formPerm.2 hc hd).exists_nat_pow_eq
  simpa only [hk] using survivor_representative_pow g component component_exact representative
    representative_component cycle recipient recipient_component c k

theorem survivor_edge_coarsened (hoff : ∀ c, c ∉ cycle → recipient c = representative c)
    (x : Agent) :
    Coarsened component cycle x
      (survivorMatching g component component_exact representative
        representative_component cycle recipient recipient_component x) := by
  by_cases hx : x ∈ Set.range representative
  · obtain ⟨c, rfl⟩ := hx
    rw [survivorMatching_recipient]
    by_cases hc : c ∈ cycle
    · right
      simpa only [representative_component, recipient_component] using
        And.intro hc (List.formPerm_apply_mem_of_mem hc)
    · left
      rw [hoff c hc]
  · rcases survivorMatching_other g component component_exact representative
      representative_component cycle recipient recipient_component hx with heq | he
    · left
      rw [heq]
    · exact Or.inl ((component_exact _ _).mp (edge_component he))

/-- This is the exact SCC update for the executed survivor permutation. -/
theorem survivor_component_exact [Finite Component] (hnodup : cycle.Nodup)
    (hoff : ∀ c, c ∉ cycle → recipient c = representative c) (a b : Agent) :
    SameComponent (survivorMatching g component component_exact representative
      representative_component cycle recipient recipient_component :: g) a b ↔
      Coarsened component cycle a b := by
  constructor
  · intro h
    induction h with
    | rel a b he =>
      rcases (edge_cons _ _ _ _).mp he with he | he
      · exact he ▸ survivor_edge_coarsened g component component_exact representative
          representative_component cycle recipient recipient_component hoff a
      · exact Or.inl ((component_exact _ _).mp (edge_component he))
    | refl _ => exact (coarsened_equivalence component cycle).refl _
    | symm _ _ _ ih => exact (coarsened_equivalence component cycle).symm ih
    | trans _ _ _ _ _ hab hbc => exact (coarsened_equivalence component cycle).trans hab hbc
  · rintro (hab | ⟨ha, hb⟩)
    · exact component_cons _ _ ((component_exact _ _).mpr hab)
    · apply Relation.EqvGen.trans _ (representative (component a)) _
      · apply component_cons
        exact (component_exact _ _).mpr (by rw [representative_component])
      · apply Relation.EqvGen.trans _ (representative (component b)) _
        · exact survivor_representatives g component component_exact representative
            representative_component cycle recipient recipient_component hnodup ha hb
        · apply component_cons
          exact (component_exact _ _).mpr (by rw [representative_component])

end Survivor

end EnvyFreeResearch.Full.Chores.Components
