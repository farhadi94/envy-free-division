import EnvyFreeResearch.Full.ChoresComponentPopulationProgram
import EnvyFreeResearch.Full.ChoresCompletionProgram

/-! Deterministic finite active-group labels and the actual two-child
completion call on a proper nonempty subset of the current population. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Population
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion
open scoped Classical

variable {n : ℕ}

def groupEmbedding (group : Finset (Fin n)) : Fin group.card ↪ Fin n :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe group)).symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩

theorem group_embedding_mem (group : Finset (Fin n)) (i : Fin group.card) : groupEmbedding group i ∈ group :=
  ((Fintype.equivFinOfCardEq (Fintype.card_coe group)).symm i).property

theorem group_embedding_range (group : Finset (Fin n)) : Set.range (groupEmbedding group) = ↑group := by
  ext i
  constructor
  · rintro ⟨a, rfl⟩
    exact group_embedding_mem group a
  · intro hi
    let a : group := ⟨i, hi⟩
    refine ⟨Fintype.equivFinOfCardEq (Fintype.card_coe group) a, ?_⟩
    simp only [groupEmbedding, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply]
    rfl

theorem group_card_lt {group : Finset (Fin n)} (h : group ≠ Finset.univ) : group.card < n := by
  simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card
    (Finset.ssubset_univ_iff.mpr h)

theorem complement_nonempty {group : Finset (Fin n)} (h : group ≠ Finset.univ) : groupᶜ.Nonempty := by
  by_contra hn
  have he : groupᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  exact h ((Finset.compl_eq_empty_iff group).mp he)

theorem complement_proper {group : Finset (Fin n)} (h : group.Nonempty) : groupᶜ ≠ Finset.univ := by
  intro he
  have hh : group = ∅ := (Finset.compl_eq_univ_iff group).mp he
  exact h.ne_empty hh

def groupUnionMap (group : Finset (Fin n)) : Sum (Fin group.card) (Fin groupᶜ.card) → Fin n :=
  Sum.elim (groupEmbedding group) (groupEmbedding groupᶜ)

theorem group_union_bijective (group : Finset (Fin n)) : Function.Bijective (groupUnionMap group) := by
  constructor
  · intro i j heq
    cases i with
    | inl a =>
      cases j with
      | inl b => exact congrArg Sum.inl ((groupEmbedding group).injective heq)
      | inr b =>
        have ha := group_embedding_mem group a
        have hb := group_embedding_mem groupᶜ b
        have heq' : groupEmbedding group a = groupEmbedding groupᶜ b := heq
        exact (Finset.mem_compl.mp hb (heq' ▸ ha)).elim
    | inr a =>
      cases j with
      | inl b =>
        have ha := group_embedding_mem groupᶜ a
        have hb := group_embedding_mem group b
        have heq' : groupEmbedding groupᶜ a = groupEmbedding group b := heq
        exact (Finset.mem_compl.mp ha (heq'.symm ▸ hb)).elim
      | inr b => exact congrArg Sum.inr ((groupEmbedding groupᶜ).injective heq)
  · intro i
    by_cases hi : i ∈ group
    · have hr : i ∈ Set.range (groupEmbedding group) := (group_embedding_range group).symm ▸ hi
      obtain ⟨a, rfl⟩ := hr
      exact ⟨Sum.inl a, rfl⟩
    · have hr : i ∈ Set.range (groupEmbedding groupᶜ) :=
        (group_embedding_range groupᶜ).symm ▸ Finset.mem_compl.mpr hi
      obtain ⟨a, rfl⟩ := hr
      exact ⟨Sum.inr a, rfl⟩

def groupEquiv (group : Finset (Fin n)) : Sum (Fin group.card) (Fin groupᶜ.card) ≃ Fin n :=
  Equiv.ofBijective (groupUnionMap group) (group_union_bijective group)

theorem group_sizes (group : Finset (Fin n)) : group.card + groupᶜ.card = n := by
  simpa only [Fintype.card_fin] using Finset.card_add_card_compl group

def reunite (group : Finset (Fin n))
    (out : Allocation n (Sum (Fin group.card) (Fin groupᶜ.card))) : Allocation n (Fin n) :=
  out.reindex (groupEquiv group).symm

theorem reunite_sound (cost : Costs n) (group : Finset (Fin n)) (U : Set ℝ)
    (out : Allocation n (Sum (Fin group.card) (Fin groupᶜ.card)))
    (h : out.Sound cost.measure (groupUnionMap group) U) :
    (reunite group out).Sound cost.measure id U := by
  have hh := h.reindex cost.measure (groupUnionMap group) U out (groupEquiv group).symm
    (groupEquiv group).symm.injective (groupEquiv group).symm.surjective
  have he : groupUnionMap group ∘ (groupEquiv group).symm = id := by
    funext i
    exact (groupEquiv group).apply_symm_apply i
  simpa only [he, reunite] using hh

def atomicProgram (group : Finset (Fin n)) (hpositive : group.Nonempty) (hproper : group ≠ Finset.univ)
    (base : Allocation n (Fin n)) (cacheX cacheR : List (Parent n)) (children : ChildPrograms n) :
    Program (Query (Fin n)) ℝ (Allocation n (Fin n)) :=
  (completeProgram (groupEmbedding group) (groupEmbedding groupᶜ)
    (Finset.card_pos.mpr hpositive) (Finset.card_pos.mpr (complement_nonempty hproper)) cacheX cacheR
    (children group.card (Finset.card_pos.mpr hpositive) (group_card_lt hproper) (groupEmbedding group))
    (children groupᶜ.card (Finset.card_pos.mpr (complement_nonempty hproper))
      (group_card_lt (complement_proper hpositive)) (groupEmbedding groupᶜ))).bind
    (fun out => .returned (base.join (reunite group out)))

/-- Both smaller recursive populations and their real child query ledgers
are joined to the closed base. This is the actual atomic completion branch. -/
theorem atomic_program_correct (cost : Costs n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (group : Finset (Fin n)) (hpositive : group.Nonempty) (hproper : group ≠ Finset.univ)
    (base : Allocation n (Fin n)) (allocated X R : Set ℝ) (hbase : base.Sound cost.measure id allocated)
    (hdisjoint : Disjoint allocated (X ∪ R)) (hXR : Disjoint X R)
    (cacheX cacheR : List (Parent n))
    (hX : CacheValid (measureProfile cost.measure) X cacheX)
    (hR : CacheValid (measureProfile cost.measure) R cacheR)
    (hsepB : ∀ i, (2 : ℝ)^(n+2)*(cost.measure (groupEmbedding group i)).real R ≤
      (cost.measure (groupEmbedding group i)).real X)
    (hsepD : ∀ i, (2 : ℝ)^(n+2)*(cost.measure (groupEmbedding groupᶜ i)).real X ≤
      (cost.measure (groupEmbedding groupᶜ i)).real R)
    (children : ChildPrograms n) (Q C : ℕ → ℕ)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Specification cost agent (children k hkpos hklt agent) (Q k+n*C k) (C k))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (atomicProgram group hpositive hproper base cacheX cacheR children) prior out trace ∧
      trace.length ≤ 19*2^n*n+(Q groupᶜ.card+n*C groupᶜ.card)+(Q group.card+n*C group.card) ∧
      virtualCuts trace ≤ 19*2^n+C groupᶜ.card+C group.card ∧
      out.Sound cost.measure id (allocated ∪ (X ∪ R)) := by
  have hb := Finset.card_pos.mpr hpositive
  have hd := Finset.card_pos.mpr (complement_nonempty hproper)
  let childB := children group.card hb (group_card_lt hproper) (groupEmbedding group)
  let childD := children groupᶜ.card hd (group_card_lt (complement_proper hpositive)) (groupEmbedding groupᶜ)
  have hB := hchildren group.card hb (group_card_lt hproper) (groupEmbedding group)
  have hD := hchildren groupᶜ.card hd (group_card_lt (complement_proper hpositive)) (groupEmbedding groupᶜ)
  obtain ⟨result, trace, hexec, hQ, hC, hs⟩ := complete_program_correct cost.measure oracle hpolicy
    (groupEmbedding group) (groupEmbedding groupᶜ) hb hd X R hXR cacheX cacheR hX hR
    (by simpa only [group_sizes] using hsepB) (by simpa only [group_sizes] using hsepD)
    childB childD (Q group.card+n*C group.card) (Q groupᶜ.card+n*C groupᶜ.card)
    (C group.card) (C groupᶜ.card)
    (fun cache hc prior => by
      obtain ⟨out, trace, he, hq, hc', hs, _, _⟩ := hB cache hc oracle hpolicy prior
      exact ⟨out, trace, he, hq, hc', hs⟩)
    (fun cache hc prior => by
      obtain ⟨out, trace, he, hq, hc', hs, _, _⟩ := hD cache hc oracle hpolicy prior
      exact ⟨out, trace, he, hq, hc', hs⟩) prior
  refine ⟨base.join (reunite group result), trace, ?_, ?_, ?_, ?_⟩
  · simpa only [atomicProgram, childB, childD, List.append_nil] using hexec.bind
      (fun out => Program.returned (base.join (reunite group out))) (Executes.returned _ _)
  · simpa only [group_sizes] using hQ
  · simpa only [group_sizes, virtualCuts] using hC
  · exact Allocation.join_sound cost.measure id allocated (X ∪ R) base (reunite group result)
      hbase (reunite_sound cost group (X ∪ R) result hs) hdisjoint

end EnvyFreeResearch.Full.Chores.Population
