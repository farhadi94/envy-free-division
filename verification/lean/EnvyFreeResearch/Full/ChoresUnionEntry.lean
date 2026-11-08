import EnvyFreeResearch.Full.ChoresUnionOwnership

/-! Initial physical component cache, including its query cost. The Core
entry point below starts from the original oracle alone. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram

variable {n : ℕ}

def initialCacheProgram (n : ℕ) : Program (Query (Fin n)) ℝ (List (Parent n)) :=
  (valuesProgram 0 1 (allAgents n)).bind (fun values => .returned [⟨0,1,values⟩])

theorem initial_cache_correct (P : Profile (Fin n))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle) (prior : History (Query (Fin n)) ℝ) :
    ∃ cache : List (Parent n), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (initialCacheProgram n) prior cache trace ∧ trace.length = n ∧
      virtualCuts trace = 0 ∧ CacheValid P (Ioc 0 1) cache := by
  obtain ⟨values,trace,hexec,hlen,hcuts,hvalues⟩ :=
    values_program_correct P oracle hpolicy 0 1 ⟨le_rfl,zero_le_one,le_rfl⟩ (allAgents n) prior
  refine ⟨[⟨0,1,values⟩],trace,?_,?_,hcuts,?_,by simp [Ordered],by simp [material]⟩
  · simpa only [initialCacheProgram,List.append_nil] using
      hexec.bind (fun values => Program.returned [(⟨0,1,values⟩ : Parent n)]) (Executes.returned _ _)
  · simpa only [allAgents,Finset.length_toList,Finset.card_univ,Fintype.card_fin] using hlen
  · refine ⟨⟨⟨le_rfl,zero_le_one,le_rfl⟩,?_⟩,trivial⟩
    intro i
    exact hvalues i (by simp [allAgents])

def unitCoreProgram (c : Fin n) :
    Program (Query (Fin n)) ℝ (IntervalCore.Outcome n × List (Parent n)) :=
  (initialCacheProgram n).bind (cachedDomainCoreProgram c)

/-- Starting with ordinary oracle access and no supplied cache, the physical
Core returns exact reusable component records with its complete query ledger.
Its partial allocation plus residue covers the unit interval literally when
the separate left-endpoint ownership convention is applied. -/
theorem unit_core_correct (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (c : Fin n) (prior : History (Query (Fin n)) ℝ) :
    ∃ out : IntervalCore.Outcome n, ∃ fresh : List (Parent n),
    ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (unitCoreProgram c) prior (out,fresh) trace ∧
      trace.length ≤ n+cachedDomainCoreBudget n ∧
      virtualCuts trace ≤ n-1+IntervalCore.trimBudget n ∧
      DomainCorrect cost (Ioc 0 1) c out ∧
      (∀ i, CacheValid (measureProfile cost) (domainAllocation (Ioc 0 1) c out i)
        (allocationCache fresh out i)) ∧
      CacheValid (measureProfile cost) (domainResidue (Ioc 0 1) out) (residueCache fresh out) ∧
      (⋃ i, ownedAllocation (Ioc 0 1) c out i) ∪ domainResidue (Ioc 0 1) out = Icc 0 1 := by
  obtain ⟨cache,t₁,hexec₁,hlen₁,hcuts₁,hcache⟩ := initial_cache_correct (measureProfile cost) oracle hpolicy prior
  obtain ⟨out,fresh,t₂,hexec₂,hlen₂,hcuts₂,hcorrect,halloc,hres⟩ :=
    recorded_core_correct hn cost oracle hpolicy (Ioc 0 1) cache hcache c (prior++t₁)
  refine ⟨out,fresh,t₁++t₂,hexec₁.bind _ hexec₂,?_,?_,hcorrect,halloc,hres,
    owned_unit_cover cost c out hcorrect⟩
  · rw [List.length_append,hlen₁]
    exact Nat.add_le_add_left hlen₂ n
  · change (t₁++t₂).countP (fun qr => isCutQuery qr.1) ≤ _
    rw [List.countP_append]
    change virtualCuts t₁+virtualCuts t₂ ≤ _
    simpa only [hcuts₁,zero_add] using hcuts₂

end EnvyFreeResearch.Full.Chores.OrderedUnion
