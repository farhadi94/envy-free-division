import EnvyFreeResearch.Full.ChoresComponentGraph

/-! Simple directed paths and the actual donor cycle matching. -/

namespace EnvyFreeResearch.Full.Chores.Components

variable {Agent : Type*}

theorem exists_simple_chain {r : Agent → Agent → Prop} {a b : Agent}
    (h : Relation.ReflTransGen r a b) :
    ∃ tail : List Agent, (a :: tail).Nodup ∧ (a :: tail).IsChain r ∧
      (a :: tail).getLast (List.cons_ne_nil _ _) = b := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], by simp, .singleton _, rfl⟩
  | @head c d hcd h ih =>
    obtain ⟨tail, hnodup, hchain, hlast⟩ := ih
    by_cases hc : c ∈ d :: tail
    · obtain ⟨before, after, heq⟩ := List.mem_iff_append.mp hc
      refine ⟨after, ?_, ?_, ?_⟩
      · rw [heq] at hnodup
        exact hnodup.of_append_right
      · rw [heq] at hchain
        exact hchain.right_of_append
      · have he : (before ++ c :: after).getLast (by simp) = b := by
          simpa only [← heq] using hlast
        simpa only [List.getLast_append_right (List.cons_ne_nil _ _)] using he
    · exact ⟨d :: tail, List.nodup_cons.mpr ⟨hc, hnodup⟩,
        List.isChain_cons_cons.mpr ⟨hcd, hchain⟩,
        by simpa only [List.getLast_cons_cons] using hlast⟩

structure SimplePath (g : Graph Agent) (a b : Agent) where
  tail : List Agent
  nodup : (a :: tail).Nodup
  chain : (a :: tail).IsChain (Edge g)
  last_eq : (a :: tail).getLast (List.cons_ne_nil _ _) = b

noncomputable def simplePath [Finite Agent] (g : Graph Agent) (a b : Agent)
    (hab : SameComponent g a b) : SimplePath g a b :=
  let h := exists_simple_chain (component_iff_reach.mp hab)
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2⟩

namespace SimplePath

variable {g : Graph Agent} {a b : Agent} (path : SimplePath g a b)

def vertices : List Agent := a :: path.tail

theorem vertices_nodup : path.vertices.Nodup := path.nodup

theorem member_component {x : Agent} (hx : x ∈ path.vertices) : SameComponent g a x := by
  exact path.chain.induction (SameComponent g a) (a :: path.tail)
    (fun _ _ he hr => .trans _ _ _ hr (edge_component he))
    (fun _ => .refl _) x hx

theorem length_le [Fintype Agent] : path.vertices.length ≤ Fintype.card Agent :=
  path.nodup.length_le_card

variable [DecidableEq Agent]

def cycleMatching : Equiv.Perm Agent := path.vertices.formPerm

theorem cycleMatching_last : path.cycleMatching b = a := by
  simpa only [cycleMatching, vertices, path.last_eq] using
    List.formPerm_apply_getLast a path.tail

theorem cycleMatching_outside {x : Agent} (hx : x ∉ path.vertices) :
    path.cycleMatching x = x := List.formPerm_apply_of_notMem hx

/-- Every changed edge except the closing edge is an actual old visited edge. -/
theorem cycleMatching_old {x : Agent} (hx : x ≠ b) :
    path.cycleMatching x = x ∨ Edge g x (path.cycleMatching x) := by
  by_cases hmem : x ∈ path.vertices
  · obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
    have hnext : k + 1 < path.vertices.length := by
      by_contra hn
      have hklast : k = path.vertices.length - 1 := by omega
      have hxb : x = b := by
        rw [← path.last_eq, List.getLast_eq_getElem]
        exact hget.symm.trans (by congr 1)
      exact hx hxb
    right
    have hstep := (List.isChain_iff_getElem.mp path.chain) k hnext
    have happly := List.formPerm_apply_lt_getElem path.vertices path.nodup k hnext
    change Edge g path.vertices[k] path.vertices[k + 1] at hstep
    rw [← happly, hget] at hstep
    exact hstep
  · exact Or.inl (path.cycleMatching_outside hmem)

theorem cycleMatching_internal (path : SimplePath g a b) :
    ∀ x, SameComponent g x (path.cycleMatching x) := by
  intro x
  by_cases hx : x = b
  · subst x
    rw [path.cycleMatching_last]
    exact .symm _ _ (path.member_component (by
      simpa only [vertices, path.last_eq] using
        List.getLast_mem (List.cons_ne_nil a path.tail)))
  · rcases path.cycleMatching_old hx with heq | he
    · exact heq.symm ▸ Relation.EqvGen.refl x
    · exact edge_component he

theorem cycleMatching_preserves_components (path : SimplePath g a b) (x y : Agent) :
    SameComponent (path.cycleMatching :: g) x y ↔ SameComponent g x y :=
  component_cons_eq g path.cycleMatching path.cycleMatching_internal x y

end SimplePath

/-- The complete matching used for a positive donor proposal to recipient `j`. -/
noncomputable def donorMatching [Finite Agent] [DecidableEq Agent]
    (g : Graph Agent) (p j : Agent) (hjp : SameComponent g j p) : Equiv.Perm Agent :=
  if j = p then 1 else (simplePath g j p hjp).cycleMatching

theorem donorMatching_recipient [Finite Agent] [DecidableEq Agent]
    (g : Graph Agent) (p j : Agent) (hjp : SameComponent g j p) :
    donorMatching g p j hjp p = j := by
  by_cases h : j = p
  · simp [donorMatching, h]
  · simp only [donorMatching, ite_eq_right h]
    exact SimplePath.cycleMatching_last _

theorem donorMatching_other [Finite Agent] [DecidableEq Agent]
    (g : Graph Agent) (p j : Agent) (hjp : SameComponent g j p) {x : Agent} (hx : x ≠ p) :
    donorMatching g p j hjp x = x ∨ Edge g x (donorMatching g p j hjp x) := by
  by_cases h : j = p
  · simp [donorMatching, h]
  · simp only [donorMatching, ite_eq_right h]
    exact SimplePath.cycleMatching_old _ hx

theorem donorMatching_preserves_components [Finite Agent] [DecidableEq Agent]
    (g : Graph Agent) (p j : Agent) (hjp : SameComponent g j p) (x y : Agent) :
    SameComponent (donorMatching g p j hjp :: g) x y ↔ SameComponent g x y := by
  apply component_cons_eq
  intro z
  by_cases h : j = p
  · simp only [donorMatching, ite_eq_left h, Equiv.Perm.one_apply]
    exact .refl _
  · simp only [donorMatching, ite_eq_right h]
    exact SimplePath.cycleMatching_internal _ z

end EnvyFreeResearch.Full.Chores.Components
