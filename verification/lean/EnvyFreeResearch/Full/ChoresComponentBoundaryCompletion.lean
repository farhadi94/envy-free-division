import EnvyFreeResearch.Full.ChoresComponentBoundaryPreparation
import EnvyFreeResearch.Full.ChoresComponentPopulationCoordinates

/-! The actual two-child completion composes parametric coordinate provenance
through preparation and both recursive child programs at their real histories.
Truthfulness of the child input caches is derived from physical preparation. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Completion Population
open scoped Classical

variable {n b c : ℕ}

theorem complete_program_known (cost : Costs n)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (agentB : Fin b → Fin n) (agentD : Fin c → Fin n) (hb : 0 < b) (hc : 0 < c)
    (X R : Set ℝ) (cacheX cacheR : List (Parent n))
    (hX : CacheValid (measureProfile cost.measure) X cacheX)
    (hR : CacheValid (measureProfile cost.measure) R cacheR)
    (hsepB : ∀ i, (2 : ℝ)^(b+c+2)*(cost.measure (agentB i)).real R ≤ (cost.measure (agentB i)).real X)
    (hsepD : ∀ j, (2 : ℝ)^(b+c+2)*(cost.measure (agentD j)).real X ≤ (cost.measure (agentD j)).real R)
    (childB : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin b)))
    (childD : List (Parent n) → Program (Query (Fin n)) ℝ (Allocation n (Fin c)))
    (hchildB : CoordinateSpec cost childB) (hchildD : CoordinateSpec cost childD)
    (points : Set ℝ) (hcacheX : CacheKnown points cacheX) (hcacheR : CacheKnown points cacheR)
    (hzero : 0 ∈ points) (hone : 1 ∈ points)
    (prior : History (Query (Fin n)) ℝ) (out : Allocation n (Sum (Fin b) (Fin c)))
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (completeProgram agentB agentD hb hc cacheX cacheR childB childD) prior out trace) :
    AllocationKnown (Known points trace) out ∧ Scoped points trace := by
  obtain ⟨prepared, t₁, t₂, h₁, h₂, ht⟩ := Executes.split_bind _ _ h
  obtain ⟨outD, t₃, t₄, h₃, h₄, ht₂⟩ := Executes.split_bind _ _ h₂
  obtain ⟨outB, t₅, t₆, h₅, h₆, ht₄⟩ := Executes.split_bind _ _ h₄
  cases h₆
  simp only [List.append_nil] at ht₄
  subst t₄
  subst t₂
  subst trace
  obtain ⟨predicted, predictedTrace, hpredicted, _, _, hcorrect⟩ := prepare_correct cost.measure oracle hpolicy
    agentB agentD hb hc X R cacheX cacheR hX hR hsepB hsepD prior
  have heq : predicted = prepared := (hpredicted.deterministic h₁).1
  subst predicted
  obtain ⟨hp, hs₁⟩ := prepare_known oracle points agentB agentD hb hc cacheX cacheR hcacheX hcacheR prior prepared t₁ h₁
  obtain ⟨hs₃, hD⟩ := hchildD prepared.forD.allocation.remainder hcorrect.forD.remainder_cache
    oracle hpolicy (prior++t₁) outD t₃ h₃ (Known points t₁) hp.2.2.2 (Or.inl hzero) (Or.inl hone)
  obtain ⟨hs₅, hB⟩ := hchildB prepared.forB.allocation.remainder hcorrect.forB.remainder_cache
    oracle hpolicy ((prior++t₁)++t₃) outB t₅ h₅ (Known (Known points t₁) t₃)
    (hp.1.2.2.mono subset_union_left) (Or.inl (Or.inl hzero)) (Or.inl (Or.inl hone))
  have hpFinal : PreparedKnown (Known (Known (Known points t₁) t₃) t₅) prepared :=
    hp.mono (subset_union_left.trans subset_union_left)
  have hDFinal : AllocationKnown (Known (Known (Known points t₁) t₃) t₅) outD := hD.mono subset_union_left
  refine ⟨?_, (scoped_append points t₁ (t₃++t₅)).mpr
    ⟨hs₁, (scoped_append (Known points t₁) t₃ t₅).mpr ⟨hs₃, hs₅⟩⟩⟩
  simpa only [known_append] using finish_prepared_known _ prepared hpFinal outB outD hB hDFinal

end EnvyFreeResearch.Full.Chores.Boundary
