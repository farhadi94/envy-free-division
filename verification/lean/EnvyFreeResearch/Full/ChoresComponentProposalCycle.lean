import EnvyFreeResearch.Full.ChoresComponentMerge

/-! A finite outgoing proposal map with no self edge supplies a concrete cycle. -/

namespace EnvyFreeResearch.Full.Chores.Components

variable {Agent : Type*}

theorem exists_periodic_point [Finite Agent] [Nonempty Agent] (f : Agent → Agent) :
    ∃ x, x ∈ Function.periodicPts f := by
  let a := Classical.choice (inferInstance : Nonempty Agent)
  obtain ⟨m, n, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => f^[k] a)
  have hperiod : ∀ {i j : ℕ}, i < j → f^[i] a = f^[j] a →
      f^[i] a ∈ Function.periodicPts f := by
    intro i j hij h
    apply Function.mk_mem_periodicPts (n := j - i) (by omega)
    change f^[j - i] (f^[i] a) = f^[i] a
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le]
    exact h.symm
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨_, hperiod hlt heq⟩
  · exact ⟨_, hperiod hlt heq.symm⟩

noncomputable def orbitList (f : Agent → Agent) (a : Agent) : List Agent :=
  (List.range (Function.minimalPeriod f a)).map (fun k => f^[k] a)

theorem orbitList_nodup (f : Agent → Agent) (a : Agent) : (orbitList f a).Nodup := by
  simpa only [Function.periodicOrbit, Cycle.nodup_coe_iff, orbitList] using
    (Function.nodup_periodicOrbit (f := f) (x := a))

@[simp] theorem orbitList_length (f : Agent → Agent) (a : Agent) :
    (orbitList f a).length = Function.minimalPeriod f a := by
  simp [orbitList]

theorem orbitList_two (f : Agent → Agent) (a : Agent)
    (ha : a ∈ Function.periodicPts f) (hno : f a ≠ a) :
    2 ≤ (orbitList f a).length := by
  rw [orbitList_length]
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts ha
  have hn : Function.minimalPeriod f a ≠ 1 := by
    intro h
    exact hno (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h)
  omega

theorem orbitList_follows [DecidableEq Agent] (f : Agent → Agent) (a : Agent)
    {x : Agent} (hx : x ∈ orbitList f a) : (orbitList f a).formPerm x = f x := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hx
  have hn := orbitList_nodup f a
  have happ := List.formPerm_apply_getElem (orbitList f a) hn k hk
  have hindex : ∀ (i : ℕ) (hi : i < (orbitList f a).length),
      (orbitList f a)[i] = f^[i] a := by
    intro i hi
    simp [orbitList]
  rw [hindex, hindex] at happ
  have hget' : f^[k] a = x := (hindex k hk).symm.trans hget
  rw [hget', orbitList_length, Function.iterate_mod_minimalPeriod_eq] at happ
  rw [Function.iterate_succ_apply', hget'] at happ
  exact happ

structure ProposalCycle [DecidableEq Agent] (f : Agent → Agent) where
  vertices : List Agent
  nodup : vertices.Nodup
  two_le : 2 ≤ vertices.length
  follows : ∀ a ∈ vertices, vertices.formPerm a = f a

noncomputable def proposalCycle [Finite Agent] [Nonempty Agent] [DecidableEq Agent]
    (f : Agent → Agent) (hno : ∀ a, f a ≠ a) : ProposalCycle f :=
  let h := exists_periodic_point f
  { vertices := orbitList f h.choose
    nodup := orbitList_nodup f h.choose
    two_le := orbitList_two f h.choose h.choose_spec (hno _)
    follows := fun _ hx => orbitList_follows f h.choose hx }

namespace ProposalCycle

variable [DecidableEq Agent] {f : Agent → Agent} (cycle : ProposalCycle f)

theorem next_mem {a : Agent} (ha : a ∈ cycle.vertices) : f a ∈ cycle.vertices := by
  rw [← cycle.follows a ha]
  exact List.formPerm_apply_mem_of_mem ha

theorem length_le [Fintype Agent] : cycle.vertices.length ≤ Fintype.card Agent :=
  cycle.nodup.length_le_card

theorem next_ne {a : Agent} (ha : a ∈ cycle.vertices) : f a ≠ a := by
  rw [← cycle.follows a ha]
  exact (List.formPerm_apply_mem_ne_self_iff cycle.vertices cycle.nodup a ha).mpr cycle.two_le

end ProposalCycle

end EnvyFreeResearch.Full.Chores.Components
