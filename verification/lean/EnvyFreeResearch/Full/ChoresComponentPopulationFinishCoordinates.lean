import EnvyFreeResearch.Full.ChoresComponentBoundaryCompletion
import EnvyFreeResearch.Full.ChoresComponentPopulationExhausted

/-! Parametric coordinate contracts for both concrete proper-population
completion branches, using the stronger recursive child induction hypothesis. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Population
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion Boundary
open scoped Classical

variable {n : ℕ}

theorem atomic_program_known (cost : Costs n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (group : Finset (Fin n)) (hpositive : group.Nonempty) (hproper : group ≠ Finset.univ)
    (base : Allocation n (Fin n)) (X R : Set ℝ) (cacheX cacheR : List (Parent n))
    (hX : CacheValid (measureProfile cost.measure) X cacheX)
    (hR : CacheValid (measureProfile cost.measure) R cacheR)
    (hsepB : ∀ i, (2 : ℝ)^(n+2)*(cost.measure (groupEmbedding group i)).real R ≤
      (cost.measure (groupEmbedding group i)).real X)
    (hsepD : ∀ i, (2 : ℝ)^(n+2)*(cost.measure (groupEmbedding groupᶜ i)).real X ≤
      (cost.measure (groupEmbedding groupᶜ i)).real R)
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n), CoordinateSpec cost (children k hkpos hklt agent))
    (points : Set ℝ) (hbase : AllocationKnown points base)
    (hcacheX : CacheKnown points cacheX) (hcacheR : CacheKnown points cacheR)
    (hzero : 0 ∈ points) (hone : 1 ∈ points)
    (prior : History (Query (Fin n)) ℝ) (out : Allocation n (Fin n)) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (atomicProgram group hpositive hproper base cacheX cacheR children) prior out trace) :
    AllocationKnown (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨result, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  cases hs
  simp only [List.append_nil] at ht
  subst trace
  have hb := Finset.card_pos.mpr hpositive
  have hd := Finset.card_pos.mpr (complement_nonempty hproper)
  obtain ⟨hresult, hscope⟩ := complete_program_known cost oracle hpolicy
    (groupEmbedding group) (groupEmbedding groupᶜ) hb hd X R cacheX cacheR hX hR
    (by simpa only [group_sizes] using hsepB) (by simpa only [group_sizes] using hsepD)
    _ _ (hchildren _ _ _ _) (hchildren _ _ _ _) points hcacheX hcacheR hzero hone prior result first hf
  exact ⟨join_known (hbase.mono subset_union_left) (reindex_known hresult (groupEquiv group).symm), hscope⟩

theorem exhausted_program_known (cost : Costs n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (assigned : Finset (Fin n)) (hpositive : assigned.Nonempty) (hproper : assigned ≠ Finset.univ)
    (base : Allocation n (Fin n)) (R : Set ℝ) (cacheR : List (Parent n))
    (hR : CacheValid (measureProfile cost.measure) R cacheR)
    (children : ChildPrograms n)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n), CoordinateSpec cost (children k hkpos hklt agent))
    (points : Set ℝ) (hbase : AllocationKnown points base) (hcacheR : CacheKnown points cacheR)
    (hzero : 0 ∈ points) (hone : 1 ∈ points)
    (prior : History (Query (Fin n)) ℝ) (out : Allocation n (Fin n)) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (exhaustedProgram assigned hpositive hproper base cacheR children) prior out trace) :
    AllocationKnown (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨child, first, second, hf, hs, ht⟩ := Executes.split_bind _ _ h
  cases hs
  simp only [List.append_nil] at ht
  subst trace
  obtain ⟨hscope, hchild⟩ := hchildren assignedᶜ.card
    (Finset.card_pos.mpr (complement_nonempty hproper))
    (group_card_lt (complement_proper hpositive)) (groupEmbedding assignedᶜ)
    cacheR ⟨hR.1,hR.2.1,rfl⟩ oracle hpolicy prior child first hf points hcacheR hzero hone
  exact ⟨domination_known _ base (groupEmbedding assignedᶜ) child (hbase.mono subset_union_left) hchild, hscope⟩

end EnvyFreeResearch.Full.Chores.Population
