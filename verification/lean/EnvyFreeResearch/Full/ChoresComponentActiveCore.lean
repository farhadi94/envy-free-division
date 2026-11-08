import EnvyFreeResearch.Full.ChoresComponentActiveQueries

/-! Core for an active population embedded in the original observer set.
The restricted-domain interpreter is applied once to the lifted k-agent
Core, so the ambient recording factor does not multiply recursive child
execution budgets. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ActiveCore
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion

variable {n k : ℕ}

def domainProgram (agent : Fin k ↪ Fin n) (c : Fin k) (cache : List (Parent n)) :
    Program (Query (Fin n)) ℝ (IntervalCore.Outcome k × List (Parent n)) :=
  translate (liftProgram agent (IntervalCore.coreProgram c 0 1)) cache

def domainBudget (n k : ℕ) : ℕ :=
  n * (2 * IntervalCore.queryBudget k + (k - 1 + IntervalCore.trimBudget k))

theorem profile_restrict (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Fin k → Fin n) (U : Set ℝ) :
    profile (restrictedProfile cost U) agent = restrictedProfile (fun i => cost (agent i)) U := rfl

theorem domain_program_correct (hk : 2 ≤ k) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (agent : Fin k ↪ Fin n) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache) (c : Fin k)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : IntervalCore.Outcome k, ∃ fresh : List (Parent n),
      ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (domainProgram agent c cache) prior (out, fresh) trace ∧
      trace.length ≤ domainBudget n k ∧
      virtualCuts trace ≤ k - 1 + IntervalCore.trimBudget k ∧
      DomainCorrect (fun i => cost (agent i)) U c out ∧
      CacheValid (measureProfile cost) U fresh := by
  let initial : SemanticState (measureProfile cost) U := ⟨cache, prior, hc⟩
  let policy := virtualPolicy cost oracle hpolicy U initial
  have hlegal : AdaptiveOracle.IsLegalPolicy (restrictedProfile cost U) policy :=
    virtual_policy_legal cost oracle hpolicy U initial
  let childPolicy := localPolicy agent policy []
  have hlocal : AdaptiveOracle.IsLegalPolicy
      (measureProfile (fun i => (cost (agent i)).restrict U)) childPolicy :=
    local_policy_legal (restrictedProfile cost U) agent policy hlegal []
  have hmono : ∀ i, Monotone ((measureProfile (fun i => (cost (agent i)).restrict U)).cumulative i) :=
    fun i => prefixCost_monotone ((cost (agent i)).restrict U) 0
  obtain ⟨out, virtualTrace, hexec, hlen, hcuts, hcorrect, _⟩ :=
    IntervalCore.core_program_executes (measureProfile (fun i => (cost (agent i)).restrict U))
      hmono childPolicy hlocal c 0 1 ⟨le_rfl, zero_le_one, le_rfl⟩ []
  have hlift : Executes policy (liftProgram agent (IntervalCore.coreProgram c 0 1)) [] out
      (liftHistory agent virtualTrace) := by
    simpa only [liftHistory, List.map_nil, List.nil_append] using lift_executes agent policy [] hexec
  obtain ⟨trace, hphysical, hphysicalLength, hphysicalCuts⟩ :=
    translate_executes cost oracle hpolicy U initial hlift
  let fresh := (historyState cost oracle hpolicy U initial (liftHistory agent virtualTrace)).cache
  have hU : U ⊆ Icc 0 1 := fun x hx =>
    ⟨(cache_domain_subset _ _ _ hc hx).1.le, (cache_domain_subset _ _ _ hc hx).2⟩
  have hd := domain_correct (fun i => cost (agent i)) U hU c out
    (IntervalCore.measured_correct hk (fun i => (cost (agent i)).restrict U) c 0 1
      ⟨le_rfl, zero_le_one, le_rfl⟩ out hcorrect)
  refine ⟨out, fresh, trace, ?_, ?_, ?_, hd,
    (historyState cost oracle hpolicy U initial (liftHistory agent virtualTrace)).valid⟩
  · simpa only [domainProgram, historyState, List.foldl_nil, List.nil_append, initial, fresh] using hphysical
  · rw [lift_length, lift_cuts] at hphysicalLength
    exact hphysicalLength.trans (Nat.mul_le_mul_left n
      (Nat.add_le_add (Nat.mul_le_mul_left 2 hlen) hcuts))
  · rw [lift_cuts] at hphysicalCuts
    exact hphysicalCuts.trans hcuts

end EnvyFreeResearch.Full.Chores.ActiveCore
