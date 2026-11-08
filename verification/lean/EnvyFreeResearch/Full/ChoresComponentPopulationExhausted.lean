import EnvyFreeResearch.Full.ChoresComponentPopulationGroups

/-! The actual exhausted-frontier recursive completion. The assigned group
is nonempty and proper, so its complement is a strictly smaller population.
All residual-domain queries are those of this one real child call. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Population
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion
open scoped Classical

variable {n : ℕ}

def exhaustedProgram (assigned : Finset (Fin n)) (hpositive : assigned.Nonempty)
    (hproper : assigned ≠ Finset.univ) (base : Allocation n (Fin n))
    (cacheR : List (Parent n)) (children : ChildPrograms n) :
    Program (Query (Fin n)) ℝ (Allocation n (Fin n)) :=
  dominationProgram base (groupEmbedding assignedᶜ)
    (children assignedᶜ.card (Finset.card_pos.mpr (complement_nonempty hproper))
      (group_card_lt (complement_proper hpositive)) (groupEmbedding assignedᶜ) cacheR)

theorem exhausted_program_correct (cost : Costs n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (assigned : Finset (Fin n)) (hpositive : assigned.Nonempty) (hproper : assigned ≠ Finset.univ)
    (base : Allocation n (Fin n)) (allocated R : Set ℝ)
    (hbase : base.Sound cost.measure id allocated) (hdisjoint : Disjoint allocated R)
    (cacheR : List (Parent n)) (hR : CacheValid (measureProfile cost.measure) R cacheR)
    (hmargin : ∀ i ∉ assigned, ∀ j ∈ assigned,
      (cost.measure i).real R ≤ (cost.measure i).real (material (base.pieces j)) -
        (cost.measure i).real (material (base.pieces i)))
    (children : ChildPrograms n) (Q C : ℕ → ℕ)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Specification cost agent (children k hkpos hklt agent) (Q k+n*C k) (C k))
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle
        (exhaustedProgram assigned hpositive hproper base cacheR children) prior out trace ∧
      trace.length ≤ Q assignedᶜ.card+n*C assignedᶜ.card ∧
      virtualCuts trace ≤ C assignedᶜ.card ∧
      out.Sound cost.measure id (allocated ∪ R) := by
  have hc : CacheValid (measureProfile cost.measure) (material cacheR) cacheR := ⟨hR.1, hR.2.1, rfl⟩
  obtain ⟨child, trace, hexec, hQ, hC, hs, _, _⟩ := hchildren assignedᶜ.card
    (Finset.card_pos.mpr (complement_nonempty hproper))
    (group_card_lt (complement_proper hpositive)) (groupEmbedding assignedᶜ)
    cacheR hc oracle hpolicy prior
  have hs' : child.Sound cost.measure (groupEmbedding assignedᶜ) R := by simpa only [hR.2.2] using hs
  refine ⟨finishDomination base (groupEmbedding assignedᶜ) child, trace,
    domination_program_executes oracle base (groupEmbedding assignedᶜ) _ prior child trace hexec,
    hQ, hC, ?_⟩
  apply finish_domination_sound cost.measure (groupEmbedding assignedᶜ) allocated R base hbase hdisjoint
    _ child hs'
  intro i j hj
  have hi := Finset.mem_compl.mp (group_embedding_mem assignedᶜ i)
  have hj' : j ∈ assigned := by
    rw [group_embedding_range] at hj
    simpa only [Finset.mem_coe, Finset.mem_compl, not_not] using hj
  exact hmargin _ hi j hj'

end EnvyFreeResearch.Full.Chores.Population
