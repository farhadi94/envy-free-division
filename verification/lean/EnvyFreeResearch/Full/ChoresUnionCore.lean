import EnvyFreeResearch.Full.ChoresUnionAllocation

/-! The actual chore Core on an arbitrary recorded finite union, implemented
using only ordinary queries to the original physical profile. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram

variable {n : ℕ}

def domainCoreProgram (c : Fin n) (cache : List (Parent n)) :
    Program (Query (Fin n)) ℝ (IntervalCore.Outcome n × List (Parent n)) :=
  compileProtocol (IntervalCore.coreProgram c 0 1).protocol (IntervalCore.queryBudget n) cache

def domainCoreBudget (n : ℕ) : ℕ :=
  n*(2*IntervalCore.queryBudget n+(n-1+IntervalCore.trimBudget n))

/-- This is the compiled Core primitive itself: its successful physical
execution, literal domain allocation, exact envy-freeness, both cutter
progress inequalities, and final all-observer cache are derived from the
interval Core and the physical query translator. No restricted-domain oracle
or Core-correctness premise remains. It is a partial-allocation primitive,
not the main theorem's complete division procedure. -/
theorem domain_core_correct (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (c : Fin n) (prior : History (Query (Fin n)) ℝ) :
    ∃ out : IntervalCore.Outcome n, ∃ fresh : List (Parent n),
    ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (domainCoreProgram c cache) prior (out,fresh) trace ∧
      trace.length ≤ domainCoreBudget n ∧
      virtualCuts trace ≤ n-1+IntervalCore.trimBudget n ∧
      DomainCorrect cost U c out ∧ IntervalCore.Cached (restrictedProfile cost U) out ∧
      CacheValid (measureProfile cost) U fresh := by
  have hU : U ⊆ Icc 0 1 := fun x hx =>
    ⟨le_of_lt ((cache_domain_subset _ _ _ hc hx).1),(cache_domain_subset _ _ _ hc hx).2⟩
  have hvirtual : ∀ policy : AdaptiveOracle.Policy (Query (Fin n)) ℝ,
      AdaptiveOracle.IsLegalPolicy (restrictedProfile cost U) policy →
      ∃ out : IntervalCore.Outcome n,
        (AdaptiveOracle.run (IntervalCore.coreProgram c 0 1).protocol policy ()
          (IntervalCore.queryBudget n) []).stop = .returned out ∧
        virtualCuts (AdaptiveOracle.run (IntervalCore.coreProgram c 0 1).protocol policy ()
          (IntervalCore.queryBudget n) []).answered ≤ n-1+IntervalCore.trimBudget n ∧
        (DomainCorrect cost U c out ∧ IntervalCore.Cached (restrictedProfile cost U) out) := by
    intro policy hlegal
    obtain ⟨out,trace,hrun,hlen,hcuts,hmeasured,hcached⟩ :=
      IntervalCore.interval_core_measures hn (fun i => (cost i).restrict U) policy hlegal
        c 0 1 ⟨le_rfl,zero_le_one,le_rfl⟩
    refine ⟨out,by simp only [hrun],?_,domain_correct cost U hU c out hmeasured,hcached⟩
    simpa only [hrun,virtualCuts] using hcuts
  obtain ⟨out,fresh,trace,hexec,hlen,hcuts,hgood,hfresh⟩ :=
    compile_protocol_correct cost oracle hpolicy U cache hc
      (IntervalCore.coreProgram c 0 1).protocol (IntervalCore.queryBudget n)
      (n-1+IntervalCore.trimBudget n)
      (fun out => DomainCorrect cost U c out ∧ IntervalCore.Cached (restrictedProfile cost U) out)
      hvirtual prior
  exact ⟨out,fresh,trace,hexec,hlen,hcuts,hgood.1,hgood.2,hfresh⟩

theorem domain_core_run (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (c : Fin n) :
    ∃ out : IntervalCore.Outcome n, ∃ fresh : List (Parent n),
    ∃ trace : History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (domainCoreProgram c cache).protocol oracle () (domainCoreBudget n) [] =
        ⟨trace,.returned (out,fresh)⟩ ∧
      trace.length ≤ domainCoreBudget n ∧
      virtualCuts trace ≤ n-1+IntervalCore.trimBudget n ∧
      DomainCorrect cost U c out ∧ IntervalCore.Cached (restrictedProfile cost U) out ∧
      CacheValid (measureProfile cost) U fresh := by
  obtain ⟨out,fresh,trace,hexec,hlen,hcuts,hcorrect,hcached,hfresh⟩ :=
    domain_core_correct hn cost oracle hpolicy U cache hc c []
  exact ⟨out,fresh,trace,hexec.run _ hlen,hlen,hcuts,hcorrect,hcached,hfresh⟩

end EnvyFreeResearch.Full.Chores.OrderedUnion
