import EnvyFreeResearch.Full.ChoresUnionSimulation

/-! Bounded adaptive protocols on a recorded domain compile directly to the
original physical oracle. The simulation overhead is charged once, not
recursively through a stack of restricted-domain oracles. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.OrderedUnion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram

variable {n : ℕ} {A : Type*}

def compileProtocol (next : Protocol Unit (Query (Fin n)) ℝ A) (budget : ℕ)
    (cache : List (Parent n)) : Program (Query (Fin n)) ℝ (A × List (Parent n)) :=
  translate (ofProtocol next budget []) cache

/-- A complete restricted-domain protocol with logical query budget B and
Cut budget C has an actual original-oracle implementation using at most
`n(2B+C)` ordinary calls and C Cuts. The returned property is preserved
through the concrete executor simulation, rather than assumed of its
physical output. -/
theorem compile_protocol_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (next : Protocol Unit (Query (Fin n)) ℝ A) (budget cuts : ℕ) (Good : A → Prop)
    (hvirtual : ∀ policy : AdaptiveOracle.Policy (Query (Fin n)) ℝ,
      AdaptiveOracle.IsLegalPolicy (restrictedProfile cost U) policy →
      ∃ result : A, (AdaptiveOracle.run next policy () budget []).stop = .returned result ∧
        virtualCuts (AdaptiveOracle.run next policy () budget []).answered ≤ cuts ∧ Good result)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result : A, ∃ fresh : List (Parent n), ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (compileProtocol next budget cache) prior (result,fresh) trace ∧
      trace.length ≤ n*(2*budget+cuts) ∧ virtualCuts trace ≤ cuts ∧ Good result ∧
      CacheValid (measureProfile cost) U fresh := by
  let initial : SemanticState (measureProfile cost) U := ⟨cache,prior,hc⟩
  let policy := virtualPolicy cost oracle hpolicy U initial
  have hlegal : AdaptiveOracle.IsLegalPolicy (restrictedProfile cost U) policy :=
    virtual_policy_legal cost oracle hpolicy U initial
  obtain ⟨result,hreturn,hcuts,hgood⟩ := hvirtual policy hlegal
  let virtualTrace := (AdaptiveOracle.run next policy () budget []).answered
  have htrace : Executes policy (ofProtocol next budget []) [] result virtualTrace := by
    simpa only [List.nil_append] using
      ofProtocol_executes next policy [] budget [] result hreturn
  obtain ⟨trace,hexec,hlen,hcuts'⟩ :=
    translate_executes cost oracle hpolicy U initial htrace
  let fresh := (historyState cost oracle hpolicy U initial virtualTrace).cache
  have hlen' : virtualTrace.length ≤ budget :=
    AdaptiveOracle.answered_length_le next policy () budget []
  refine ⟨result,fresh,trace,?_,?_,hcuts'.trans hcuts,hgood,
    (historyState cost oracle hpolicy U initial virtualTrace).valid⟩
  · simpa only [historyState,List.foldl_nil,List.nil_append,initial,compileProtocol,fresh] using hexec
  · exact hlen.trans (Nat.mul_le_mul_left n
      (Nat.add_le_add (Nat.mul_le_mul_left 2 hlen') hcuts))

/-- Standalone next-action execution of the compiled program. The same
program can also be embedded under an arbitrary enclosing physical history
using `compile_protocol_correct`. -/
theorem compile_protocol_run (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (next : Protocol Unit (Query (Fin n)) ℝ A) (budget cuts : ℕ) (Good : A → Prop)
    (hvirtual : ∀ policy : AdaptiveOracle.Policy (Query (Fin n)) ℝ,
      AdaptiveOracle.IsLegalPolicy (restrictedProfile cost U) policy →
      ∃ result : A, (AdaptiveOracle.run next policy () budget []).stop = .returned result ∧
        virtualCuts (AdaptiveOracle.run next policy () budget []).answered ≤ cuts ∧ Good result) :
    ∃ result : A, ∃ fresh : List (Parent n), ∃ trace : History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (compileProtocol next budget cache).protocol oracle ()
        (n*(2*budget+cuts)) [] = ⟨trace,.returned (result,fresh)⟩ ∧
      trace.length ≤ n*(2*budget+cuts) ∧ virtualCuts trace ≤ cuts ∧ Good result ∧
      CacheValid (measureProfile cost) U fresh := by
  obtain ⟨result,fresh,trace,hexec,hlen,hcuts,hgood,hfresh⟩ :=
    compile_protocol_correct cost oracle hpolicy U cache hc next budget cuts Good hvirtual []
  exact ⟨result,fresh,trace,hexec.run _ hlen,hlen,hcuts,hgood,hfresh⟩

end EnvyFreeResearch.Full.Chores.OrderedUnion
