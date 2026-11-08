import EnvyFreeResearch.Full.ChoresComponentBoundaryCompiler
import EnvyFreeResearch.Full.ChoresComponentBoundaryOutput

/-! Endpoint provenance for the released physical finite-union Core program,
including its protocol embedding and final all-observer recording pass. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n : ℕ}

theorem domain_core_known (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (points : Set ℝ) (hcache : CacheKnown points cache) (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (c : Fin n) (prior : History (Query (Fin n)) ℝ)
    (out : IntervalCore.Outcome n) (fresh : List (Parent n)) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (domainCoreProgram c cache) prior (out, fresh) trace) :
    CacheKnown (Known points trace) fresh ∧ Scoped points trace ∧
      (∀ x ∈ coreEndpoints out, x ∈ Known points trace) := by
  let initial : SemanticState (measureProfile cost) U := ⟨cache, prior, hc⟩
  let policy := virtualPolicy cost oracle hpolicy U initial
  have hlegal : AdaptiveOracle.IsLegalPolicy (restrictedProfile cost U) policy :=
    virtual_policy_legal cost oracle hpolicy U initial
  have hmono : ∀ i, Monotone ((restrictedProfile cost U).cumulative i) :=
    fun i => prefixCost_monotone ((cost i).restrict U) 0
  obtain ⟨result, virtualTrace, hsource, hlen, _, _, _⟩ :=
    IntervalCore.core_program_executes (restrictedProfile cost U) hmono policy hlegal c 0 1
      ⟨le_rfl, zero_le_one, le_rfl⟩ []
  have hrun := hsource.run (IntervalCore.queryBudget n) hlen
  have hembed : Executes policy
      (ofProtocol (IntervalCore.coreProgram c 0 1).protocol (IntervalCore.queryBudget n) []) [] result virtualTrace := by
    have he := ofProtocol_executes (IntervalCore.coreProgram c 0 1).protocol policy []
      (IntervalCore.queryBudget n) [] result (by simp only [List.nil_append, hrun])
    simpa only [List.nil_append, hrun] using he
  have hs := core_scoped policy points c 0 1 hzero hone [] result virtualTrace hsource
  obtain ⟨physicalTrace, hphysical, hfinalCache, hphysicalScope, hsubset⟩ :=
    translate_known cost oracle hpolicy U initial hembed points
      (by simpa only [historyState, List.foldl_nil, initial] using hcache) hs
  have hphysical' : Executes oracle (domainCoreProgram c cache) prior
      (result, (historyState cost oracle hpolicy U initial virtualTrace).cache) physicalTrace := by
    simpa only [domainCoreProgram, compileProtocol, historyState, List.foldl_nil, List.nil_append, initial] using hphysical
  obtain ⟨hpair, htrace⟩ := hphysical'.deterministic h
  have hout : result = out := congrArg Prod.fst hpair
  have hfresh : (historyState cost oracle hpolicy U initial virtualTrace).cache = fresh := congrArg Prod.snd hpair
  subst out
  subst fresh
  subst trace
  refine ⟨?_, hphysicalScope, ?_⟩
  · simpa only [List.nil_append] using hfinalCache
  · intro x hx
    exact hsubset (core_endpoints_known (restrictedProfile cost U) hmono policy hlegal points c 0 1
      hzero hone ⟨le_rfl, zero_le_one, le_rfl⟩ [] result virtualTrace hsource x hx)

theorem cached_domain_core_known (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (points : Set ℝ) (hcache : CacheKnown points cache) (hzero : (0 : ℝ) ∈ points) (hone : (1 : ℝ) ∈ points)
    (c : Fin n) (prior : History (Query (Fin n)) ℝ)
    (out : IntervalCore.Outcome n) (fresh : List (Parent n)) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (cachedDomainCoreProgram c cache) prior (out, fresh) trace) :
    CacheKnown (Known points trace) fresh ∧ Scoped points trace ∧
      (∀ x ∈ coreEndpoints out, x ∈ Known points trace) := by
  obtain ⟨result, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  rcases result with ⟨result, middle⟩
  obtain ⟨finalCache, tail, empty, htail, hreturn, hsecond⟩ := Executes.split_bind _ _ hsecond
  cases hreturn
  simp only [List.append_nil] at hsecond
  subst second
  subst trace
  obtain ⟨hmiddle, hscope, hpoints⟩ := domain_core_known cost oracle hpolicy U cache hc points
    hcache hzero hone c prior result middle first hfirst
  obtain ⟨hfinal, htailScope⟩ := align_many_known oracle (Known points first) (coreEndpoints result)
    hpoints middle hmiddle (prior ++ first) fresh tail htail
  exact ⟨hfinal.mono (known_mono points first tail),
    (scoped_append points first tail).mpr ⟨hscope, htailScope⟩,
    fun x hx => known_mono points first tail (hpoints x hx)⟩

/-- The boundary contract consumed by native-to-ambient recursive restoration
holds for the concrete physical finite-union Core, with no assumed output
provenance. -/
theorem physical_core_old_or_cut (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (c : Fin n) (prior : History (Query (Fin n)) ℝ)
    (out : IntervalCore.Outcome n) (fresh : List (Parent n)) (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (cachedDomainCoreProgram c cache) prior (out, fresh) trace) :
    CacheKnown (Known {x | Aligned cache x} trace) fresh ∧ Scoped {x | Aligned cache x} trace ∧
      (∀ x ∈ coreEndpoints out, FromTrace cache trace x) := by
  apply cached_domain_core_known cost oracle hpolicy U cache hc {x | Aligned cache x}
    (inherited_cache_known _ cache hc.1 hc.2.1) _ _ c prior out fresh trace h
  · intro p hp
    exact Or.inr (((valid_iff_forall _ _).mp hc.1 p hp).1.1)
  · intro p hp
    exact Or.inl (((valid_iff_forall _ _).mp hc.1 p hp).1.2.2)

end EnvyFreeResearch.Full.Chores.Boundary
